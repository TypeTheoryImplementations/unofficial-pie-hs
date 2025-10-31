-- Copyright (C) 2025 Lincoln Sand
-- SPDX-License-Identifier: AGPL-3.0-only

module Interface (printAndCheckFile, typeCheckFile, typeCheckText) where

import Parser.Parser
import Typing.TypeChecker
import Text.Megaparsec (parse, errorBundlePretty)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

typeCheckInputImpl :: String -> T.Text -> IO ()
typeCheckInputImpl message src = do
    case parse parseTopLevel message src of
        Left err -> putStr $ errorBundlePretty err
        Right decls ->
            case processFile decls of
                Left err -> putStrLn $ "Type Error. Error message: " <> err
                Right _ -> putStrLn "Program Ok."

printAndCheckFile :: FilePath -> IO ()
printAndCheckFile fp = do
    putStr $ fp <> ": "
    typeCheckFile fp

typeCheckFile :: FilePath -> IO ()
typeCheckFile fp = do
    src <- TIO.readFile fp
    typeCheckInputImpl fp src

typeCheckText :: T.Text -> IO ()
typeCheckText src = typeCheckInputImpl "<input>" src
