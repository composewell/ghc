{-#  LANGUAGE  MagicHash  #-}
{-#  LANGUAGE  UnboxedTuples  #-}

import GHC.IO(IO(..))
import Control.Concurrent
import GHC.Stack
import GHC.Exts
import GHC.Word

main = do
    -- capabilities <- getNumCapabilities
    -- putStrLn $ "Number of capabilities: " ++ show capabilities
    a  <-  f 20
    -- triggerProfWindowIO 0 1
    -- triggerProfSinceIO 0 9
    b  <-  g 30
    print  $  a  +  b
    errorWithStackTrace "hello"

    where

    f n  = fib n
    g n  = fib (n `div` 2)


-- The following are equal
-- triggerProfSinceIO i j
-- triggerProfWindowIO i (numGCs - j)

triggerProfSinceIO (W64# a) (W64# b) = IO $
    \s -> (# triggerProf# (unsafeCoerce# 0#) a (unsafeCoerce# 0#) b s, () #)

triggerProfWindowIO (W64# a) (W64# b) = IO $
    \s -> (# triggerProf# (unsafeCoerce# 1#) a b (unsafeCoerce# 0#) s, () #)

fib n =
    if n < 2
    then pure 1
    else do
          a <- fib (n-1)
          b <- fib (n-2)
          pure $ a + b
