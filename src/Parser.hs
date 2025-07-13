module Parser(topLevelP, alphaRename, Term(..)) where

import Text.Megaparsec
import qualified Text.Megaparsec.Char as ParsecChar
import qualified Text.Megaparsec.Char.Lexer as CharLexer

import qualified Data.Void as Void
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad.State as State


type Parser = Parsec Void.Void String

type Name = String
data Term
    = Variable Name
    | Lambda Name Term Term
    | Application Term Term
    | Pi Name Term Term
    | Type
    deriving (Show, Eq)

lexemeP :: Parser a -> Parser a
lexemeP = CharLexer.lexeme ParsecChar.space

symbolP :: String -> Parser String
symbolP = CharLexer.symbol ParsecChar.space

topLevelP :: Parser Term
topLevelP = (skipMany ParsecChar.spaceChar) *> termP <* eof

termP :: Parser Term
termP = try typeP <|> try lambdaAbstractionP <|> try piTypeAbstractionP <|> try arrowTypeConstructorP <|> try applicationP <|> try (parensP termP) <|> (Variable <$> variableP)

identifierP :: Parser String
identifierP = parensP identifierP <|> identifierWithoutParensP

identifierWithoutParensP :: Parser String
identifierWithoutParensP = lexemeP $ (:) <$> ParsecChar.letterChar <*> many (ParsecChar.alphaNumChar <|> ParsecChar.char '_')

variableP :: Parser String
variableP = identifierP

parensP :: Parser a -> Parser a
parensP = between (symbolP "(") (symbolP ")")

paramP :: Parser (String, Term)
paramP = try (parensP paramWithoutParensP) <|> paramWithoutParensP

paramWithoutParensP :: Parser (String, Term)
paramWithoutParensP = do
    var <- variableP
    _ <- symbolP ":"
    ty <- termP
    return (var, ty)

lambdaAbstractionP :: Parser Term
lambdaAbstractionP = do
    _ <- symbolP "\\lambda"
    param <- paramP
    _ <- symbolP "."
    term <- termP
    return $ Lambda (fst param) (snd param) term

-- `foldl` allows us to have syntax sugar for multi-parameter lambda application that desugars into repeated currying
applicationP :: Parser Term
applicationP = parensP $ foldl Application <$> termP <*> some termP

typeP :: Parser Term
typeP = Type <$ symbolP "Type"

piTypeAbstractionP :: Parser Term
piTypeAbstractionP = do
    _ <- symbolP "\\Pi"
    param <- paramP
    _ <- symbolP "."
    body <- termP
    return $ Pi (fst param) (snd param) body

arrowTypeConstructorP :: Parser Term
arrowTypeConstructorP = do
    aType <- variableP
    _ <- symbolP "\\to"
    bType <- variableP
    return $ Pi "_" (Variable aType) (Variable bType)




type Env = Map.Map String String
type Used = Set.Set String
type RenameM = State.State (Env, Used)


freshen :: String -> Set.Set String -> String
freshen name usedNames = head $ dropWhile (`Set.member` usedNames) candidates
    where
        candidates = iterate (++ "'") name

rename :: Term -> RenameM Term
rename (Variable name) = do
    (env, _) <- State.get
    return $ Variable (Map.findWithDefault name name env)

rename (Application f x) = do
    f' <- rename f
    x' <- rename x
    return $ Application f' x'

rename (Lambda x ty body) = do
    (env, used) <- State.get
    let x' = freshen x used
    let env' = Map.insert x x' env
    let used' = Set.insert x' used
    State.put (env', used')
    ty' <- rename ty
    body' <- rename body
    State.put (env, used')
    return $ Lambda x' ty' body'

rename (Pi x ty body) = do
    (env, used) <- State.get
    let x' = freshen x used
    let env' = Map.insert x x' env
    let used' = Set.insert x' used
    State.put (env', used')
    ty' <- rename ty
    body' <- rename body
    State.put (env, used')
    return $ Pi x' ty' body'

rename Type = return Type

freeVars :: Term -> Set.Set String
freeVars = free Set.empty

free :: Set.Set String -> Term -> Set.Set String
free bound (Variable name)
    | name `Set.member` bound = Set.empty
    | otherwise = Set.singleton name

free bound (Application f x) = free bound f `Set.union` free bound x

free bound (Lambda x ty body) = free bound ty `Set.union` free (Set.insert x bound) body

free bound (Pi x ty body) = free bound ty `Set.union` free (Set.insert x bound) body

free _ Type = Set.empty

alphaRename :: Term -> Term
alphaRename term = State.evalState (rename term) (Map.empty, freeVars term)


