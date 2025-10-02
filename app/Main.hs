module Main where

import InterfaceIO.Interface
import System.Environment (getArgs)

main :: IO ()
main = do
    filePaths <- getArgs
    mapM_ printAndCheckFile filePaths
