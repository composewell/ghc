{-#  LANGUAGE  MagicHash  #-}
{-#  LANGUAGE  UnboxedTuples  #-}

import GHC.IO(IO(..))
import Control.Concurrent
import GHC.Stack
import GHC.Exts
import GHC.Word
import Data.Bits

main = do
    -- capabilities <- getNumCapabilities
    -- putStrLn $ "Number of capabilities: " ++ show capabilities
    a  <-  f 20
    triggerProf (ReportSince 0 0) True
    -- triggerProfSinceIO 0 9
    b  <-  g 30
    print  $  a  +  b
    errorWithStackTrace "hello"

    where

    f n  = fib n
    g n  = fib (n `div` 2)

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

triggerProf :: ReportType -> Bool -> IO ()
triggerProf reportType verbose = do
    let (W64# unused) = 0
    case reportType of
        ReportSince (W64# l) (W64# u) -> IO $ \s ->
            let (W64# rt) = setVerbosityBit 0
             in (# triggerProf# (unsafeCoerce# rt) u unused l s, () #)
        ReportWindow (W64# l) (W64# u) -> IO $ \s ->
            let (W64# rt) = setVerbosityBit 1
             in (# triggerProf# (unsafeCoerce# rt) u l unused s, () #)
    where
    setVerbosityBit i =
        if verbose
        then setBit i 1
        else i

fib n =
    if n < 2
    then pure 1
    else do
          a <- fib (n-1)
          b <- fib (n-2)
          pure $ a + b
