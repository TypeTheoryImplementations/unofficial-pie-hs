module Parser.Parser(parseTopLevel, processFile, Term(..), Name, The(..)) where

import Text.Megaparsec
import Parser.SyntacticTypes
import Typing.SemanticTypes
import Typing.Normalization
import Typing.TypingRules
import qualified Text.Megaparsec.Char as ParsecChar
import qualified Text.Megaparsec.Char.Lexer as CharLexer

import qualified Data.Void as Void
import Control.Monad

type Parser = Parsec Void.Void String

-- NOTE: Preface all parsing functions with `parse`

type TopLevelDecls = [TopLevelDecl]

reservedKeywords :: [Name]
reservedKeywords = [
    "The", "Atom", "Sigma", "cons", "car", "cdr", "Pi", "lambda", "Nat", "zero", "add1", "which-Nat",
    "iter-Nat", "rec-Nat", "ind-Nat", "List", "nil", "rec-List", "ind-List", "Vec", "vecnil", "head", "tail",
    "ind-Vec", "same", "symm", "cong", "replace", "trans", "Either", "left", "right", "ind-Either",
    "Trivial", "sole", "Absurd", "ind-Absurd", "U"]

parseTopLevelDecl :: Parser TopLevelDecl
parseTopLevelDecl = (skipMany ParsecChar.spaceChar) *> parseTopLevelBinder

-- NOTE: Entry point into parser
parseTopLevel :: Parser TopLevelDecls
parseTopLevel = some parseTopLevelDecl <* eof

parseLexeme :: Parser a -> Parser a
parseLexeme = CharLexer.lexeme ParsecChar.space

parseSymbol :: String -> Parser String
parseSymbol = CharLexer.symbol ParsecChar.space

parseParens :: Parser a -> Parser a
parseParens = between (parseSymbol "(") (parseSymbol ")")

parseIdentifier :: Parser String
parseIdentifier = do
    ident <- parseLexeme $ (:) <$> ParsecChar.letterChar <*> many (ParsecChar.alphaNumChar <|> ParsecChar.char '-')
    if ident `elem` reservedKeywords
        then fail $ "keyword " ++ (show ident) ++ " cannot be used as an identifier"
        else return ident

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
    paramList <- parseSingleParam
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
    paramList <- parseSingleParam
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


data TopLevelDecl
    = TopLevelClaim Name Term
    | TopLevelDef Name Term
    | TopLevelCheckSame Term Term Term
    | TopLevelFree Term

parseTopLevelBinder :: Parser TopLevelDecl
parseTopLevelBinder =
        try parseClaim
    <|> try parseDef
    <|> try parseCheckSame
    <|>     TopLevelFree <$> parseTerm

parseClaim :: Parser TopLevelDecl
parseClaim = parseParens $ do
    _ <- parseSymbol "claim"
    x <- parseIdentifier
    xType <- parseTerm
    return $ TopLevelClaim x xType

parseDef :: Parser TopLevelDecl
parseDef = parseParens $ do
    _ <- parseSymbol "define"
    x <- parseIdentifier
    xDef <- parseTerm
    return $ TopLevelDef x xDef

parseCheckSame :: Parser TopLevelDecl
parseCheckSame = parseParens $ do
    _ <- parseSymbol "check-same"
    xType <- parseTerm
    x1 <- parseTerm
    x2 <- parseTerm
    return $ TopLevelCheckSame xType x1 x2


initCtx :: Context
initCtx = []

initRename :: Renaming
initRename = []

-- NOTE: Entry point into type checker
processFile :: TopLevelDecls -> Maybe Context
processFile decls = foldM processDecl initCtx decls

processDecl :: Context -> TopLevelDecl -> Maybe Context
processDecl ctx (TopLevelClaim name ty) = addClaim ctx name ty
processDecl ctx (TopLevelDef name e) = addDef ctx name e
processDecl ctx (TopLevelCheckSame ty e1 e2) = checkSame ctx ty e1 e2 >> return ctx
processDecl ctx (TopLevelFree e) = typingSynth ctx initRename e >> return ctx


addClaim :: Context -> Name -> Term -> Maybe Context
addClaim ctx x ty = do
    _ <- notUsed ctx x
    tyOut <- isType ctx initRename ty
    return ((x, Claim (valInCtx ctx tyOut)):ctx)

addDef :: Context -> Name -> Term -> Maybe Context
addDef ctx x expr = do
    typeVal <- getClaim ctx x
    exprOut <- typingCheck ctx initRename expr typeVal
    return $ bindVal (removeClaim x ctx) x typeVal (valInCtx ctx exprOut)

removeClaim :: Name -> Context -> Context
removeClaim _ [] = []
removeClaim x ((y, b):ctxTail)
    | x == y =
        case b of
            Claim _ -> removeClaim x ctxTail
            _ -> error "There is a logic error in the implementation where `removeClaim` has been called with duplicate definitions in the context"
    | otherwise = (y, b) : removeClaim x ctxTail

checkSame :: Context -> Term -> Term -> Term -> Maybe ConvertSuccess
checkSame ctx ty a b = do
    tyOut <- isType ctx initRename ty
    let tyVal = valInCtx ctx tyOut
    aOut <- typingCheck ctx initRename a tyVal
    bOut <- typingCheck ctx initRename b tyVal
    let aVal = valInCtx ctx aOut
    let bVal = valInCtx ctx bOut
    convert ctx tyVal aVal bVal

notUsed :: Context -> Name -> Maybe ConvertSuccess
notUsed [] _ = Just ConvertSuccess
notUsed ((y, _):ctxTail) x =
    if x == y then Nothing else notUsed ctxTail x

getClaim :: Context -> Name -> Maybe Value
getClaim [] _ = Nothing
getClaim ((y, Def _ _):_) x
    | x == y = Nothing -- x is already defined
getClaim ((y, Claim typeVal):_) x
    | x == y = Just typeVal
getClaim (_:ctxTail) x = getClaim ctxTail x

bindVal :: Context -> Name -> Value -> Value -> Context
bindVal ctx x typeVal val = ((x, Def typeVal val):ctx)


