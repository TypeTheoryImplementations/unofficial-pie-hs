module InterfaceIO.Interface where

import Parser.Parser
import Text.Megaparsec (parse, errorBundlePretty)

typeCheckText :: String -> IO ()
typeCheckText src =
    case parse parseTopLevel "<input>" src of
        Left err -> putStr $ errorBundlePretty err
        Right decls ->
            case processFile decls of
                Nothing -> putStrLn "Type Error."
                Just _ -> putStrLn "Program Ok."

typeCheckFile :: FilePath -> IO ()
typeCheckFile fp = do
    src <- readFile fp
    case parse parseTopLevel fp src of
        Left err -> putStr $ errorBundlePretty err
        Right decls ->
            case processFile decls of
                Nothing -> putStrLn "Type Error."
                Just _ -> putStrLn "Program Ok."



