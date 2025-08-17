module ParsingSpec where

import Test.Hspec

import Parser

import Text.Megaparsec (parse)
-- import Text.Megaparsec.Error (errorBundlePretty)

spec :: Spec
spec = do
    describe "Parser" $ do
        it "Parses a simple expression" $ do
            let input = "x"
            let expectedResult = Symbol "x"
            parse topLevelP "" input `shouldBe` Right expectedResult
        it "Parses Single Param Arrow" $ do
            let input = "(-> Nat Nat)"
            let expectedResult = Arrow Nat Nat
            parse topLevelP "" input `shouldBe` Right expectedResult
        it "Parses Multiparam Arrow" $ do
            let input = "(-> Nat Nat Nat)"
            let expectedResult = Arrow Nat (Arrow Nat Nat)
            parse topLevelP "" input `shouldBe` Right expectedResult
        it "Parses Multiparam Pi" $ do
            let input = "(Pi ((y Nat) (x Nat)) Nat)"
            let expectedResult = Pi ("y", Nat) (Pi ("x", Nat) Nat)
            parse topLevelP "" input `shouldBe` Right expectedResult
        it "Parses Multiparam Lambda" $ do
            let input = "(lambda (x y) x)"
            let expectedResult = Lambda "x" (Lambda "y" (Symbol "x"))
            parse topLevelP "" input `shouldBe` Right expectedResult
        it "Parses Multiparam Application" $ do
            let input = "(func x y)"
            let expectedResult = Application (Application (Symbol "func") (Symbol "x")) (Symbol "y")
            parse topLevelP "" input `shouldBe` Right expectedResult
