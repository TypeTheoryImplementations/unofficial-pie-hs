-- Copyright (C) 2025 Lincoln Sand
-- SPDX-License-Identifier: AGPL-3.0-only

module Interface (printAndCheckFile, typeCheckFile, typeCheckText) where

import Parser.Parser
import Typing.TypeChecker
import Text.Megaparsec (parse, errorBundlePretty)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

printAndCheckFile :: FilePath -> IO ()
printAndCheckFile fp = do
    putStr $ fp <> ": "
    typeCheckFile fp

typeCheckFile :: FilePath -> IO ()
typeCheckFile fp = do
    src <- TIO.readFile fp
    case parse parseTopLevel fp src of
        Left err -> putStr $ errorBundlePretty err
        Right decls ->
            case processFile decls of
                Nothing -> putStrLn "Type Error."
                Just _ -> putStrLn "Program Ok."

typeCheckText :: T.Text -> IO ()
typeCheckText src =
    case parse parseTopLevel "<input>" src of
        Left err -> putStr $ errorBundlePretty err
        Right decls ->
            case processFile decls of
                Nothing -> putStrLn "Type Error."
                Just _ -> putStrLn "Program Ok."
