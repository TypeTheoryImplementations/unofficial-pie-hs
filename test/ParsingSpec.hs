module ParsingSpec where

import Test.Hspec

import Parser

import Text.Megaparsec (parse)
import Text.Megaparsec.Error (errorBundlePretty)

spec :: Spec
spec = do
    describe "Parser" $ do
        it "Parses a simple expression" $ do
            let input = "x"
            let expectedResult = Variable "x"
            parse topLevelP "" input `shouldBe` Right expectedResult
