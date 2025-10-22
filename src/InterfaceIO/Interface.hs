-- Copyright (C) 2025 Lincoln Sand
-- SPDX-License-Identifier: AGPL-3.0-only

module InterfaceIO.Interface where

import Parser.Parser
import Text.Megaparsec (parse, errorBundlePretty)

printAndCheckFile :: FilePath -> IO ()
printAndCheckFile fp = do
    putStr $ fp ++ ": "
    typeCheckFile fp

typeCheckFile :: FilePath -> IO ()
typeCheckFile fp = do
    src <- readFile fp
    case parse parseTopLevel fp src of
        Left err -> putStr $ errorBundlePretty err
        Right decls ->
            case processFile decls of
                Nothing -> putStrLn "Type Error."
                Just _ -> putStrLn "Program Ok."

typeCheckText :: String -> IO ()
typeCheckText src =
    case parse parseTopLevel "<input>" src of
        Left err -> putStr $ errorBundlePretty err
        Right decls ->
            case processFile decls of
                Nothing -> putStrLn "Type Error."
                Just _ -> putStrLn "Program Ok."
