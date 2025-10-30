-- Copyright (C) 2025 Lincoln Sand
-- SPDX-License-Identifier: AGPL-3.0-only

module Parser.Parser (parseTopLevel) where

import qualified Data.Void as Void
import qualified Data.Text as T
import Data.Char (isAlphaNum, isAlpha)

import Text.Megaparsec (Parsec, notFollowedBy, takeWhileP, takeWhile1P, (<|>), try, many, some, empty, eof, between)
import qualified Text.Megaparsec.Char as ParsecChar
import qualified Text.Megaparsec.Char.Lexer as CharLexer

import Common.Types

type Parser = Parsec Void.Void T.Text

spaceConsumer :: Parser ()
spaceConsumer = CharLexer.space ParsecChar.space1 (CharLexer.skipLineComment ";") empty

reservedKeywords :: [Name]
reservedKeywords = [
    "the", "Atom", "Pair", "Sigma", "cons", "car", "cdr", "->", "Pi", "lambda",
    "Nat", "zero", "add1", "which-Nat", "iter-Nat", "rec-Nat", "ind-Nat",
    "List", "nil", "::", "rec-List", "ind-List", "Vec", "vecnil", "vec::", "head",
    "tail", "ind-Vec", "=", "same", "symm", "cong", "replace", "trans", "ind-=",
    "Either", "left", "right", "ind-Either", "Trivial", "sole", "Absurd", "ind-Absurd", "U",
    "claim", "define", "check-same"]

-- NOTE: Entry point into parser
parseTopLevel :: Parser TopLevelDecls
parseTopLevel = spaceConsumer *> many parseTopLevelBinder <* spaceConsumer <* eof

parseLexeme :: Parser a -> Parser a
parseLexeme = CharLexer.lexeme spaceConsumer

identifierChar :: Parser Char
identifierChar = ParsecChar.alphaNumChar <|> ParsecChar.char '-'

isIdentTail :: Char -> Bool
isIdentTail c = isAlphaNum c || c == '-'

parseKeyword :: T.Text -> Parser T.Text
parseKeyword word = parseLexeme (ParsecChar.string word <* notFollowedBy identifierChar)

parseSymbol :: T.Text -> Parser T.Text
parseSymbol = CharLexer.symbol spaceConsumer

parseParens :: Parser a -> Parser a
parseParens = between (parseSymbol "(") (parseSymbol ")")

parseIdentifier :: Parser T.Text
parseIdentifier = parseLexeme $ do
    first <- ParsecChar.letterChar
    rest <- takeWhileP (Just "identifier tail") isIdentTail
    let ident = T.cons first rest
    if ident `elem` reservedKeywords
        then fail $ "keyword " <> T.unpack ident <> " cannot be used as an identifier"
        else return ident

parseNumber :: Parser Integer
parseNumber = parseLexeme CharLexer.decimal

isAtomLiteral :: Char -> Bool
isAtomLiteral = isAlpha

parseSrc :: Parser SyntacticTerm
parseSrc
        =   try parseSrcThe
        <|> try parseSrcAtom
        <|> try parseSrcAtomLiteral
        <|> try parseSrcPair
        <|> try parseSrcSigma
        <|> try parseSrcCons
        <|> try parseSrcCar
        <|> try parseSrcCdr
        <|> try parseSrcArrow
        <|> try parseSrcPi
        <|> try parseSrcLambda
        <|> try parseSrcNat
        <|> try parseSrcZero
        <|> try parseSrcAdd1
        <|> try parseSrcNatLiteral
        <|> try parseSrcWhichNat
        <|> try parseSrcIterNat
        <|> try parseSrcRecNat
        <|> try parseSrcIndNat
        <|> try parseSrcList
        <|> try parseSrcListNil
        <|> try parseSrcListColonColon
        <|> try parseSrcRecList
        <|> try parseSrcIndList
        <|> try parseSrcVec
        <|> try parseSrcVecNil
        <|> try parseSrcVecColonColon
        <|> try parseSrcHead
        <|> try parseSrcTail
        <|> try parseSrcIndVec
        <|> try parseSrcEq
        <|> try parseSrcEqSame
        <|> try parseSrcSymm
        <|> try parseSrcCong
        <|> try parseSrcReplace
        <|> try parseSrcTrans
        <|> try parseSrcIndEq
        <|> try parseSrcEither
        <|> try parseSrcLeft
        <|> try parseSrcRight
        <|> try parseSrcIndEither
        <|> try parseSrcTrivial
        <|> try parseSrcTrivialSole
        <|> try parseSrcAbsurd
        <|> try parseSrcIndAbsurd
        <|> try parseSrcU
-- NOTE: We put `parseSrcVar` here to avoid excessive backtracking (for performance reasons).
        <|> try parseSrcVar
-- NOTE: We put `parseSrcApplication` last since it has no special syntax/character at the beginning to match on.
--  It would still work if put earlier (order of the parsers doesn't matter here), but the excessive backtracing would have performance costs.
        <|>     parseSrcApplication

parseSingleParam :: Parser (Name, SyntacticTerm)
parseSingleParam = parseParens $ do
    paramName <- parseIdentifier
    paramType <- parseSrc
    return $ (paramName, paramType)

parseSrcThe :: Parser SyntacticTerm
parseSrcThe = parseParens $ do
    _ <- parseKeyword "the"
    annot <- parseSrc
    expr <- parseSrc
    return $ SrcThe annot expr

parseSrcVar :: Parser SyntacticTerm
parseSrcVar = SrcVar <$> parseIdentifier

parseSrcAtom :: Parser SyntacticTerm
parseSrcAtom = SrcAtom <$ parseKeyword "Atom"

parseSrcAtomLiteral :: Parser SyntacticTerm
parseSrcAtomLiteral = parseLexeme $ do -- `parseLexeme` consumes the trailing whitespace after we've parsed the full atom literal
    _ <- ParsecChar.char '\''
    sym <- takeWhile1P (Just "atom literal string") isAtomLiteral
    return $ SrcAtomLiteral sym

parseSrcPair :: Parser SyntacticTerm
parseSrcPair = parseParens $ do
    _ <- parseKeyword "Pair"
    car <- parseSrc
    cdr <- parseSrc
    return $ SrcPair car cdr

parseSrcSigma :: Parser SyntacticTerm
parseSrcSigma = parseParens $ do
    _ <- parseKeyword "Sigma"
    paramList <- parseParens $ some parseSingleParam
    body <- parseSrc
    return $ SrcSigma paramList body

parseSrcCons :: Parser SyntacticTerm
parseSrcCons = parseParens $ do
    _ <- parseKeyword "cons"
    car <- parseSrc
    cdr <- parseSrc
    return $ SrcCons car cdr

parseSrcCar :: Parser SyntacticTerm
parseSrcCar = parseParens $ do
    _ <- parseKeyword "car"
    expr <- parseSrc
    return $ SrcCar expr

parseSrcCdr :: Parser SyntacticTerm
parseSrcCdr = parseParens $ do
    _ <- parseKeyword "cdr"
    expr <- parseSrc
    return $ SrcCdr expr

parseSrcArrow :: Parser SyntacticTerm
parseSrcArrow = parseParens $ do
    _ <- parseKeyword "->"
    fromType <- parseSrc
    toTypes <- some parseSrc
    return $ SrcArrow fromType toTypes

parseSrcPi :: Parser SyntacticTerm
parseSrcPi = parseParens $ do
    _ <- parseKeyword "Pi"
    paramList <- parseParens $ some parseSingleParam
    body <- parseSrc
    return $ SrcPi paramList body

parseSrcLambda :: Parser SyntacticTerm
parseSrcLambda = parseParens $ do
    _ <- parseKeyword "lambda"
    paramNames <- parseParens $ some parseIdentifier
    body <- parseSrc
    return $ SrcLambda paramNames body

parseSrcApplication :: Parser SyntacticTerm
parseSrcApplication = parseParens $ do
    func <- parseSrc
    args <- some parseSrc
    return $ SrcApplication func args

parseSrcNat :: Parser SyntacticTerm
parseSrcNat = SrcNat <$ parseKeyword "Nat"

parseSrcZero :: Parser SyntacticTerm
parseSrcZero = SrcNatZero <$ parseKeyword "zero"

parseSrcAdd1 :: Parser SyntacticTerm
parseSrcAdd1 = parseParens $ do
    _ <- parseKeyword "add1"
    arg <- parseSrc
    return $ SrcNatAdd1 arg

parseSrcNatLiteral :: Parser SyntacticTerm
parseSrcNatLiteral = SrcNatLiteral <$> parseNumber

parseSrcWhichNat :: Parser SyntacticTerm
parseSrcWhichNat = parseParens $ do
    _ <- parseKeyword "which-Nat"
    target <- parseSrc
    base <- parseSrc
    step <- parseSrc
    return $ SrcWhichNat target base step

parseSrcIterNat :: Parser SyntacticTerm
parseSrcIterNat = parseParens $ do
    _ <- parseKeyword "iter-Nat"
    target <- parseSrc
    base <- parseSrc
    step <- parseSrc
    return $ SrcIterNat target base step

parseSrcRecNat :: Parser SyntacticTerm
parseSrcRecNat = parseParens $ do
    _ <- parseKeyword "rec-Nat"
    target <- parseSrc
    base <- parseSrc
    step <- parseSrc
    return $ SrcRecNat target base step

parseSrcIndNat :: Parser SyntacticTerm
parseSrcIndNat = parseParens $ do
    _ <- parseKeyword "ind-Nat"
    target <- parseSrc
    mot <- parseSrc
    base <- parseSrc
    step <- parseSrc
    return $ SrcIndNat target mot base step

parseSrcList :: Parser SyntacticTerm
parseSrcList = parseParens $ do
    _ <- parseKeyword "List"
    elementType <- parseSrc
    return $ SrcList elementType

parseSrcListNil :: Parser SyntacticTerm
parseSrcListNil = SrcListNil <$ parseKeyword "nil"

parseSrcListColonColon :: Parser SyntacticTerm
parseSrcListColonColon = parseParens $ do
    _ <- parseKeyword "::"
    listHead <- parseSrc
    listTail <- parseSrc
    return $ SrcListColonColon listHead listTail

parseSrcRecList :: Parser SyntacticTerm
parseSrcRecList = parseParens $ do
    _ <- parseKeyword "rec-List"
    target <- parseSrc
    base <- parseSrc
    step <- parseSrc
    return $ SrcRecList target base step

parseSrcIndList :: Parser SyntacticTerm
parseSrcIndList = parseParens $ do
    _ <- parseKeyword "ind-List"
    target <- parseSrc
    mot <- parseSrc
    base <- parseSrc
    step <- parseSrc
    return $ SrcIndList target mot base step

parseSrcVec :: Parser SyntacticTerm
parseSrcVec = parseParens $ do
    _ <- parseKeyword "Vec"
    elementType <- parseSrc
    vecSize <- parseSrc
    return $ SrcVec elementType vecSize

parseSrcVecNil :: Parser SyntacticTerm
parseSrcVecNil = SrcVecNil <$ parseKeyword "vecnil"

parseSrcVecColonColon :: Parser SyntacticTerm
parseSrcVecColonColon = parseParens $ do
    _ <- parseKeyword "vec::"
    vecHead <- parseSrc
    vecTail <- parseSrc
    return $ SrcVecColonColon vecHead vecTail

parseSrcHead :: Parser SyntacticTerm
parseSrcHead = parseParens $ do
    _ <- parseKeyword "head"
    expr <- parseSrc
    return $ SrcHead expr

parseSrcTail :: Parser SyntacticTerm
parseSrcTail = parseParens $ do
    _ <- parseKeyword "tail"
    expr <- parseSrc
    return $ SrcTail expr

parseSrcIndVec :: Parser SyntacticTerm
parseSrcIndVec = parseParens $ do
    _ <- parseKeyword "ind-Vec"
    n <- parseSrc
    target <- parseSrc
    mot <- parseSrc
    base <- parseSrc
    step <- parseSrc
    return $ SrcIndVec n target mot base step

parseSrcEq :: Parser SyntacticTerm
parseSrcEq = parseParens $ do
    _ <- parseKeyword "="
    exprType <- parseSrc
    from <- parseSrc
    to <- parseSrc
    return $ SrcEq exprType from to

parseSrcEqSame :: Parser SyntacticTerm
parseSrcEqSame = parseParens $ do
    _ <- parseKeyword "same"
    expr <- parseSrc
    return $ SrcEqSame expr

parseSrcSymm :: Parser SyntacticTerm
parseSrcSymm = parseParens $ do
    _ <- parseKeyword "symm"
    expr <- parseSrc
    return $ SrcEqSymm expr

parseSrcCong :: Parser SyntacticTerm
parseSrcCong = parseParens $ do
    _ <- parseKeyword "cong"
    expr <- parseSrc
    func <- parseSrc
    return $ SrcEqCong expr func

parseSrcReplace :: Parser SyntacticTerm
parseSrcReplace = parseParens $ do
    _ <- parseKeyword "replace"
    target <- parseSrc
    mot <- parseSrc
    base <- parseSrc
    return $ SrcEqReplace target mot base

parseSrcTrans :: Parser SyntacticTerm
parseSrcTrans = parseParens $ do
    _ <- parseKeyword "trans"
    fromMid <- parseSrc
    midTo <- parseSrc
    return $ SrcEqTrans fromMid midTo

-- Aka: The J eliminator
parseSrcIndEq :: Parser SyntacticTerm
parseSrcIndEq = parseParens $ do
    _ <- parseKeyword "ind-="
    target <- parseSrc
    motive <- parseSrc
    base <- parseSrc
    return $ SrcEqIndEq target motive base

parseSrcEither :: Parser SyntacticTerm
parseSrcEither = parseParens $ do
    _ <- parseKeyword "Either"
    leftType <- parseSrc
    rightType <- parseSrc
    return $ SrcEither leftType rightType

parseSrcLeft :: Parser SyntacticTerm
parseSrcLeft = parseParens $ do
    _ <- parseKeyword "left"
    expr <- parseSrc
    return $ SrcEitherLeft expr

parseSrcRight :: Parser SyntacticTerm
parseSrcRight = parseParens $ do
    _ <- parseKeyword "right"
    expr <- parseSrc
    return $ SrcEitherRight expr

parseSrcIndEither :: Parser SyntacticTerm
parseSrcIndEither = parseParens $ do
    _ <- parseKeyword "ind-Either"
    target <- parseSrc
    mot <- parseSrc
    baseLeft <- parseSrc
    baseRight <- parseSrc
    return $ SrcIndEither target mot baseLeft baseRight

parseSrcTrivial :: Parser SyntacticTerm
parseSrcTrivial = SrcTrivial <$ parseKeyword "Trivial"

parseSrcTrivialSole :: Parser SyntacticTerm
parseSrcTrivialSole = SrcTrivialSole <$ parseKeyword "sole"

parseSrcAbsurd :: Parser SyntacticTerm
parseSrcAbsurd = SrcAbsurd <$ parseKeyword "Absurd"

parseSrcIndAbsurd :: Parser SyntacticTerm
parseSrcIndAbsurd = parseParens $ do
    _ <- parseKeyword "ind-Absurd"
    target <- parseSrc
    mot <- parseSrc
    return $ SrcIndAbsurd target mot

parseSrcU :: Parser SyntacticTerm
parseSrcU = SrcU <$ parseKeyword "U"

parseTopLevelBinder :: Parser TopLevelDecl
parseTopLevelBinder
    =   try parseClaim
    <|> try parseDef
    <|> try parseCheckSame
    <|>     TopLevelFree <$> parseSrc

parseClaim :: Parser TopLevelDecl
parseClaim = parseParens $ do
    _ <- parseKeyword "claim"
    claimName <- parseIdentifier
    claimPropType <- parseSrc
    return $ TopLevelClaim claimName claimPropType

parseDef :: Parser TopLevelDecl
parseDef = parseParens $ do
    _ <- parseKeyword "define"
    x <- parseIdentifier
    xDef <- parseSrc
    return $ TopLevelDef x xDef

parseCheckSame :: Parser TopLevelDecl
parseCheckSame = parseParens $ do
    _ <- parseKeyword "check-same"
    eqType <- parseSrc
    x1 <- parseSrc
    x2 <- parseSrc
    return $ TopLevelCheckSame eqType x1 x2
