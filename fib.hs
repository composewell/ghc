import Control.Concurrent

main = do
    -- capabilities <- getNumCapabilities
    -- putStrLn $ "Number of capabilities: " ++ show capabilities
    print (f 30 + g 30)

    where

    f n  = fib n
    g n  = fib (n `div` 2)

fib n = if n < 2 then 1 else fib (n-1) + fib (n-2)
