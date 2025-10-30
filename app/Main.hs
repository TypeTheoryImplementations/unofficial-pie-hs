-- Copyright (C) 2025 Lincoln Sand
-- SPDX-License-Identifier: AGPL-3.0-only

module Main where

import System.Environment (getArgs)

import Interface

main :: IO ()
main = do
    filePaths <- getArgs
    mapM_ printAndCheckFile filePaths
