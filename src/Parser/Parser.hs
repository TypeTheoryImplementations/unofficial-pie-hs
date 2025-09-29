module Parser.Parser(parseTopLevel, Term(..), Name, The(..)) where

import Text.Megaparsec
import Parser.SyntacticTypes
import qualified Text.Megaparsec.Char as ParsecChar
import qualified Text.Megaparsec.Char.Lexer as CharLexer

import qualified Data.Void as Void

type Parser = Parsec Void.Void String

-- NOTE: Perface all parsing functions with `parse`

parseTopLevel :: Parser Term
parseTopLevel = (skipMany ParsecChar.spaceChar) *> parseTerm <* eof

parseLexeme :: Parser a -> Parser a
parseLexeme = CharLexer.lexeme ParsecChar.space

parseSymbol :: String -> Parser String
parseSymbol = CharLexer.symbol ParsecChar.space

parseParens :: Parser a -> Parser a
parseParens = between (parseSymbol "(") (parseSymbol ")")

parseIdentifier :: Parser String
parseIdentifier = parseLexeme $ (:) <$> ParsecChar.letterChar <*> many (ParsecChar.alphaNumChar <|> ParsecChar.char '-')

parseThe :: Parser The
parseThe = parseParens $ do
    _ <- parseSymbol "the"
    annot <- parseTerm
    expr <- parseTerm
    return $ The annot expr

parseSingleParam :: Parser (Name, Term)
parseSingleParam = parseParens $ do
    paramName <- parseIdentifier
    paramType <- parseTerm
    return $ (paramName, paramType)

parseTerm :: Parser Term
parseTerm =
            try parseTermThe
        <|> try parseTermAtom
        <|> try parseTermAtomLiteral
        <|> try parseTermSigma
        <|> try parseTermCons
        <|> try parseTermCar
        <|> try parseTermCdr
        <|> try parseTermPi
        <|> try parseTermLambda
        <|> try parseTermNat
        <|> try parseTermNatZero
        <|> try parseTermNatAdd1
        <|> try parseTermWhichNat
        <|> try parseTermIterNat
        <|> try parseTermRecNat
        <|> try parseTermIndNat
        <|> try parseTermList
        <|> try parseTermListNil
        <|> try parseTermListColonColon
        <|> try parseTermRecList
        <|> try parseTermIndList
        <|> try parseTermVec
        <|> try parseTermVecNil
        <|> try parseTermVecColonColon
        <|> try parseTermHead
        <|> try parseTermTail
        <|> try parseTermIndVec
        <|> try parseTermEq
        <|> try parseTermEqSame
        <|> try parseTermSymm
        <|> try parseTermCong
        <|> try parseTermReplace
        <|> try parseTermTrans
        <|> try parseTermIndEq
        <|> try parseTermEither
        <|> try parseTermEitherLeft
        <|> try parseTermEitherRight
        <|> try parseTermIndEither
        <|> try parseTermTrivial
        <|> try parseTermTrivialSole
        <|> try parseTermAbsurd
        <|> try parseTermIndAbsurd
        <|> try parseTermU
        <|> try parseTermApplication -- NOTE: General, consumes any two space separated terms in parens. Must be near bottom/after most expressions
        <|>     parseTermVar -- NOTE: General, consumes any valid identifier. Must be near bottom/after all keywords

parseTermThe :: Parser Term
parseTermThe = TermThe <$> parseThe

parseTermVar :: Parser Term
parseTermVar = TermVar <$> parseIdentifier

parseTermAtom :: Parser Term
parseTermAtom = TermAtom <$ parseSymbol "Atom"

parseTermAtomLiteral :: Parser Term
parseTermAtomLiteral = do
    _ <- parseSymbol "'"
    sym <- parseIdentifier
    return $ TermAtomLiteral sym

parseTermSigma :: Parser Term
parseTermSigma = parseParens $ do
    _ <- parseSymbol "Sigma"
    paramList <- parseParens $ parseSingleParam
    body <- parseTerm
    return $ TermSigma (fst paramList) (snd paramList) body

parseTermCons :: Parser Term
parseTermCons = parseParens $ do
    _ <- parseSymbol "cons"
    car <- parseTerm
    cdr <- parseTerm
    return $ TermCons car cdr

parseTermCar :: Parser Term
parseTermCar = parseParens $ do
    _ <- parseSymbol "car"
    expr <- parseTerm
    return $ TermCar expr

parseTermCdr :: Parser Term
parseTermCdr = parseParens $ do
    _ <- parseSymbol "cdr"
    expr <- parseTerm
    return $ TermCdr expr

parseTermPi :: Parser Term
parseTermPi = parseParens $ do
    _ <- parseSymbol "Pi"
    paramList <- parseParens $ parseSingleParam
    body <- parseTerm
    return $ TermPi (fst paramList) (snd paramList) body

parseTermLambda :: Parser Term
parseTermLambda = parseParens $ do
    _ <- parseSymbol "lambda"
    paramName <- parseParens $ parseIdentifier
    body <- parseTerm
    return $ TermLambda paramName body

parseTermApplication :: Parser Term
parseTermApplication = parseParens $ do
    func <- parseTerm
    arg <- parseTerm
    return $ TermApplication func arg

parseTermNat :: Parser Term
parseTermNat = TermNat <$ parseSymbol "Nat"

parseTermNatZero :: Parser Term
parseTermNatZero = TermNatZero <$ parseSymbol "zero"

parseTermNatAdd1 :: Parser Term
parseTermNatAdd1 = parseParens $ do
    _ <- parseSymbol "add1"
    arg <- parseTerm
    return $ TermNatAdd1 arg

parseTermWhichNat :: Parser Term
parseTermWhichNat = parseParens $ do
    _ <- parseSymbol "which-Nat"
    target <- parseTerm
    base <- parseThe
    step <- parseTerm
    return $ TermWhichNat target base step

parseTermIterNat :: Parser Term
parseTermIterNat = parseParens $ do
    _ <- parseSymbol "iter-Nat"
    target <- parseTerm
    base <- parseThe
    step <- parseTerm
    return $ TermIterNat target base step

parseTermRecNat :: Parser Term
parseTermRecNat = parseParens $ do
    _ <- parseSymbol "rec-Nat"
    target <- parseTerm
    base <- parseThe
    step <- parseTerm
    return $ TermRecNat target base step

parseTermIndNat :: Parser Term
parseTermIndNat = parseParens $ do
    _ <- parseSymbol "ind-Nat"
    target <- parseTerm
    mot <- parseTerm
    base <- parseTerm
    step <- parseTerm
    return $ TermIndNat target mot base step

parseTermList :: Parser Term
parseTermList = parseParens $ do
    _ <- parseSymbol "List"
    elementType <- parseTerm
    return $ TermList elementType

parseTermListNil :: Parser Term
parseTermListNil = TermListNil <$ parseSymbol "nil"

parseTermListColonColon :: Parser Term
parseTermListColonColon = parseParens $ do
    _ <- parseSymbol "::"
    listHead <- parseTerm
    listTail <- parseTerm
    return $ TermListColonColon listHead listTail

parseTermRecList :: Parser Term
parseTermRecList = parseParens $ do
    _ <- parseSymbol "rec-List"
    target <- parseTerm
    base <- parseThe
    step <- parseTerm
    return $ TermRecList target base step

parseTermIndList :: Parser Term
parseTermIndList = parseParens $ do
    _ <- parseSymbol "ind-List"
    target <- parseTerm
    mot <- parseTerm
    base <- parseTerm
    step <- parseTerm
    return $ TermIndList target mot base step

parseTermVec :: Parser Term
parseTermVec = parseParens $ do
    _ <- parseSymbol "Vec"
    elementType <- parseTerm
    vecSize <- parseTerm
    return $ TermVec elementType vecSize

parseTermVecNil :: Parser Term
parseTermVecNil = TermVecNil <$ parseSymbol "vecnil"

parseTermVecColonColon :: Parser Term
parseTermVecColonColon = parseParens $ do
    _ <- parseSymbol "vec::"
    vecHead <- parseTerm
    vecTail <- parseTerm
    return $ TermVecColonColon vecHead vecTail

parseTermHead :: Parser Term
parseTermHead = parseParens $ do
    _ <- parseSymbol "head"
    expr <- parseTerm
    return $ TermHead expr

parseTermTail :: Parser Term
parseTermTail = parseParens $ do
    _ <- parseSymbol "tail"
    expr <- parseTerm
    return $ TermTail expr

parseTermIndVec :: Parser Term
parseTermIndVec = parseParens $ do
    _ <- parseSymbol "ind-Vec"
    n <- parseTerm
    target <- parseTerm
    mot <- parseTerm
    base <- parseTerm
    step <- parseTerm
    return $ TermIndVec n target mot base step

parseTermEq :: Parser Term
parseTermEq = parseParens $ do
    _ <- parseSymbol "="
    exprType <- parseTerm
    from <- parseTerm
    to <- parseTerm
    return $ TermEq exprType from to

parseTermEqSame :: Parser Term
parseTermEqSame = parseParens $ do
    _ <- parseSymbol "same"
    expr <- parseTerm
    return $ TermEqSame expr

parseTermSymm :: Parser Term
parseTermSymm = parseParens $ do
    _ <- parseSymbol "symm"
    expr <- parseTerm
    return $ TermSymm expr

parseTermCong :: Parser Term
parseTermCong = parseParens $ do
    _ <- parseSymbol "cong"
    exprType <- parseTerm
    expr <- parseTerm
    func <- parseTerm
    return $ TermCong exprType expr func

parseTermReplace :: Parser Term
parseTermReplace = parseParens $ do
    _ <- parseSymbol "replace"
    target <- parseTerm
    mot <- parseTerm
    base <- parseTerm
    return $ TermReplace target mot base

parseTermTrans :: Parser Term
parseTermTrans = parseParens $ do
    _ <- parseSymbol "trans"
    fromMid <- parseTerm
    midTo <- parseTerm
    return $ TermTrans fromMid midTo

-- Aka: The J eliminator
parseTermIndEq :: Parser Term
parseTermIndEq = parseParens $ do
    _ <- parseSymbol "ind-="
    target <- parseTerm
    motive <- parseTerm
    base <- parseTerm
    return $ TermIndEq target motive base

parseTermEither :: Parser Term
parseTermEither = parseParens $ do
    _ <- parseSymbol "Either"
    leftType <- parseTerm
    rightType <- parseTerm
    return $ TermEither leftType rightType

parseTermEitherLeft :: Parser Term
parseTermEitherLeft = parseParens $ do
    _ <- parseSymbol "left"
    expr <- parseTerm
    return $ TermEitherLeft expr

parseTermEitherRight :: Parser Term
parseTermEitherRight = parseParens $ do
    _ <- parseSymbol "right"
    expr <- parseTerm
    return $ TermEitherRight expr

parseTermIndEither :: Parser Term
parseTermIndEither = parseParens $ do
    _ <- parseSymbol "ind-Either"
    target <- parseTerm
    mot <- parseTerm
    baseLeft <- parseTerm
    baseRight <- parseTerm
    return $ TermIndEither target mot baseLeft baseRight

parseTermTrivial :: Parser Term
parseTermTrivial = TermTrivial <$ parseSymbol "Trivial"

parseTermTrivialSole :: Parser Term
parseTermTrivialSole = TermTrivialSole <$ parseSymbol "sole"

parseTermAbsurd :: Parser Term
parseTermAbsurd = TermAbsurd <$ parseSymbol "Absurd"

parseTermIndAbsurd :: Parser Term
parseTermIndAbsurd = parseParens $ do
    _ <- parseSymbol "ind-Absurd"
    target <- parseTerm
    mot <- parseTerm
    return $ TermIndAbsurd target mot

parseTermU :: Parser Term
parseTermU = TermU <$ parseSymbol "U"
