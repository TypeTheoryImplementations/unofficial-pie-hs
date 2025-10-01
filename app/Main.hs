module Main where

import InterfaceIO.Interface

main :: IO ()
main = do
    putStrLn "Input filename:"
    fp <- getLine
    typeCheckFile fp
