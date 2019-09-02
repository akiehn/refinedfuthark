module RefinedFuthark.Parser
    ( parseFile, Program, ParseError, SourceName
    ) where

--import Text.Parsec hiding (Empty, (<|>))
import Text.Parsec hiding (Empty)
import Text.Parsec.String (Parser)
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language
import RefinedFuthark.Syntax
import RefinedFuthark.Transform (curryfy)

lexer :: T.TokenParser ()
lexer = T.makeTokenParser def
  where def = emptyDef { T.reservedNames = resNames
                       , T.commentLine = "--"
                       , T.identStart = letter <|> char '_'
                       , T.identLetter = alphaNum <|> char '_'
                       , T.opStart = oneOf "+-*/%=!><|&^"
                       , T.opLetter = oneOf "+-*/%=!><|&^."
                       , T.reservedOpNames =  resOpNames
                       }

resNames :: [String]
resNames = ["true", "false", "if", "then", "else", "let", "loop", "in"     
           ,"val", "for", "do", "with", "local", "open", "include", "import" 
           ,"type", "entry", "module", "while", "unsafe", "assert", "_"]

resOpNames :: [String]
resOpNames = ["+", "-", "*", "/", "%", "//", "%%", "==", "!=", "<", "<=", ">"
             ,">=", "&&", "||", "**", "^", "&", "|", ">>", "<<", "<|", "|>"]

reserved :: String -> Parser ()
reserved = T.reserved lexer

ident :: Parser Ident
ident = T.identifier lexer

symbol :: String -> Parser ()
symbol s = T.symbol lexer s >> return ()

colon :: Parser ()
colon = T.colon lexer >> return ()

comma :: Parser ()
comma = T.comma lexer >> return ()

integer :: Parser Integer
integer = T.integer lexer

naturalOrFloat :: Parser (Either Integer Double)
naturalOrFloat = T.naturalOrFloat lexer

reservedOp :: String -> Parser ()
reservedOp = T.reservedOp lexer

brackets :: Parser a -> Parser a
brackets = T.brackets (lexer)

parens :: Parser a -> Parser a
parens = T.parens (lexer)

braces :: Parser a -> Parser a
braces = T.braces lexer

stringLiteral :: Parser String
stringLiteral = T.stringLiteral lexer

parseFile :: SourceName -> String -> Either ParseError Program
parseFile fileName s = parse program fileName s

program :: Parser Program
program =
  do T.whiteSpace lexer
     decs <- many dec
     eof
     return decs

dec :: Parser Dec
dec = (reserved "let" >> val <?> "value binding") <|>
      (reserved "import" >> ImportDec <$> stringLiteral <?> "import") <?> "declaration"

val :: Parser Dec
val =
  do bindId <- ident
     tps <- many tparam
     fps <- many param
     colon
     ted <- typeExp
     symbol "="
     e <- expr
     return (ValDec bindId tps fps ted e)

tparam :: Parser TypeParam
tparam = (char '\'' >> TypeVar <$> ident)
  <|> (SizeVar <$> brackets ident) <?> "type parameter"

boolIndex :: Parser BoolIndex
boolIndex = flip chainl1 (symbol "&&" >> return IAnd) $ do
  i <- intIndex
  op <- (try $ symbol "<=" >> return ILess) <|> (symbol "<" >> return ISLess)
  j <- intIndex
  return (op i j)

param :: Parser Param
param = (parens $
  do paramName <- ident
     colon
     te <- typeExp
     return (Param paramName te)) <?> "parameter"

typeExp :: Parser TypeExp
typeExp = typeExpTerm >>= (\t -> (symbol "->" >> FunType t <$> typeExp) <|> return t)

typeExpTerm :: Parser TypeExp
typeExpTerm =
     arrayTypeExp
  <|> predType
  <|> (ident >>= (\i -> IntType <$> parens intIndex <|> return (TypeName i)))
  <|> try (parens typeExp)
  <|> TupleType <$> (parens $ sepBy typeExp comma)
  <?> "type expression"

predType :: Parser TypeExp
predType = braces $ do
  t <- (symbol "i32" >> IntPredType <$> parens ident) <|>
    ArrayPredType <$> (brackets ident) <*> typeExpTerm
  symbol "|"
  index <- boolIndex
  --return (IntPredType tyvar index)
  return (t index)

arrayTypeExp :: Parser TypeExp
arrayTypeExp =
  do index <- (brackets $ optionMaybe intIndex)
     te <- typeExp
     return (ArrayType index te)

intIndex :: Parser IntIndex
intIndex = IndexVar <$> qualName <|> IndexConst <$> integer <?> "integer type index"

qualName :: Parser QualName
qualName = ident

expr :: Parser Exp
expr = letExpr <|> opExpr
  <|> ifThenElse
  <|> lambdaExpr
  <?> "expression"

ifThenElse :: Parser Exp
ifThenElse =
  do reserved "if"
     e1 <- expr
     reserved "then"
     e2 <- expr
     reserved "else"
     e3 <- expr
     return (IfThenElse e1 e2 e3)

lambdaExpr :: Parser Exp
lambdaExpr =
  do symbol "\\"
     fp <- lparam
     fps <- many lparam
     rettp <- optionMaybe (colon >> typeExpTerm)
     symbol "->"
     e <- expr
     return (curryfy fp fps rettp e)
  <?> "lambda expression"

lparam :: Parser LParam
lparam = ((\x -> (x,Nothing)) <$> ident) <|> parens (do
  pName <- ident
  colon
  t <- typeExp
  return (pName, Just t))

--skipTill :: String -> Parser String
--skipTill s = manyTill anyChar (try (symbol s))

letExpr :: Parser Exp
letExpr =
  do bindings <- many letBinding
     reserved "in"
     e <- expr
     return (Let bindings e)
  where letBinding =
          do reserved "let"
             bindId <- ident
             bindType <- optionMaybe (colon >> typeExp)
             symbol "="
             e <- expr
             return (bindId,bindType,e)

numberLit :: Parser Exp
numberLit = f <$> naturalOrFloat
  where f (Left n) = IntLit n
        f (Right d) = FloatLit d

negLit :: Parser Exp
negLit = (\r -> case r of Left n -> IntLit (-n)
                          Right d -> FloatLit (-d)) <$> try (string "-" >> naturalOrFloat)
atomExpr :: Parser Exp
atomExpr =
  negLit <|>
  option id (reservedOp "-" >> return (UnOp Neg)) <*> applyExpr


atomExpr2 :: Parser Exp
atomExpr2 =
  numberLit <|>
  (qualName >>= (\v -> Index v <$> brackets expr <|> return (Var v)))
  <|> try (parens opSec)
  <|> parens expr

applyExpr :: Parser Exp
applyExpr = (<|> atomExpr2) . try $
  do func <- qualName
     args <- many1 atomExpr2
     return (Apply (Var func) args)

-- apply :: QualName -> Exp -> [Exp] -> Exp
-- apply fname arg args = Apply (Var fname) (foldr Apply arg args)

opSec :: Parser Exp
opSec = choice (map opOf [("+",Plus)])
  where opOf (ops,op) = reservedOp ops >> return (OpSection op)

opExpr :: Parser Exp
opExpr = buildExpressionParser table atomExpr
  where table = [
                 --[Prefix $ reservedOp "-" >> return (UnOp Neg)],
                 [binOp "*" Times, binOp "/" Divide, binOp "%" Modulo],
                 [binOp "+" Plus, binOp "-" Minus],
                 [binOp "<" Less, binOp "==" Equals]]
        binOp ops op = Infix (reservedOp ops  >> return (BinOp op)) AssocLeft
