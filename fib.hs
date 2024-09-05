{-#  LANGUAGE  MagicHash  #-}
{-#  LANGUAGE  UnboxedTuples  #-}
{-#  LANGUAGE  BangPatterns  #-}

import GHC.IO(IO(..))
import Control.Concurrent
import GHC.Stack
import GHC.Exts
import GHC.Word
import Data.Bits
import Data.Array
import qualified Data.ByteString as BS

main = do
    -- To get unpinned large blocks
    let a = array (1,4000) ((1,1) : [(i, i * a!(i-1)) | i <- [2..100]])
    let b = BS.pack [1..254]
    let c = BS.pack $ concat $ replicate 9 [1..254]
    let d = BS.pack $ concat $ replicate 9 [1..253]
    -- capabilities <- getNumCapabilities
    -- putStrLn $ "Number of capabilities: " ++ show capabilities
    print $ length a
    print $ BS.length b
    print $ BS.length c
    print $ BS.length d
    let !r1 = f 20
    triggerProf (ReportSince 0 0) True True
    let !r2 = f 30
    print $ r1 + r2
    -- threadDelay 100000000
    print $ length a
    print $ BS.last b
    print $ BS.last c
    print $ BS.last d
    errorWithStackTrace "hello"

    where

    f n  = fib n
    g n  = fib (n `div` 2)

fib n = if n < 2 then 1 else fib (n-1) + fib (n-2)

-- The following are equal
-- ReportSince j i
-- ReportWindow (numGCs - j) i

data ReportType
    = ReportSince
          { rsOffsetAbsFromBegLower :: Word64
          , rsOffsetRelFromEndUpper :: Word64
          }
    | ReportWindow
          { rwOffsetRelFromEndLower :: Word64
          , rwOffsetRelFromEndUpper :: Word64
          }
    | ReportStats

triggerProf :: ReportType -> Bool -> Bool -> IO ()
triggerProf reportType verbose fineGrainedPinnedReporting = do
    let (W64# unused) = 0
    case reportType of
        ReportSince (W64# l) (W64# u) -> IO $ \s ->
            let (W64# rt) = setOptions 0
             in (# triggerProf# (unsafeCoerce# rt) u unused l s, () #)
        ReportWindow (W64# l) (W64# u) -> IO $ \s ->
            let (W64# rt) = setOptions 1
             in (# triggerProf# (unsafeCoerce# rt) u l unused s, () #)
        ReportStats -> IO $ \s ->
            let (W64# rt) = setOptions 2
             in (# triggerProf# (unsafeCoerce# rt) unused unused unused s, () #)
    where
    setOptions = setVerbosityBit . setPinnedReportingBit
    setVerbosityBit i =
        if verbose
        then setBit i 3
        else i
    setPinnedReportingBit i =
        if fineGrainedPinnedReporting
        then setBit i 2
        else i
