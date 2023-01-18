
module MathExpr.Parser where

import Chronos
import MathExpr.Transformations
import MathExpr.Types
import Text.Parsec hiding (Empty)
import qualified Data.Time.Calendar as D
import Text.Parsec.Expr
import Text.Parsec.Token
import Yahp hiding ((<|>), Product, Sum, Prefix, Infix, and, sum, try)

mathLangDef :: forall m u . Monad m => GenLanguageDef String u m
mathLangDef    = LanguageDef
  { commentStart   = "/*"
   , commentEnd     = "*/"
   , commentLine    = "#"
   , nestedComments = True
   , identStart     = letter <|> char '_'
   , identLetter    = alphaNum <|> oneOf "_'"
   , opStart        = opLetter mathLangDef
   , opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
   , reservedOpNames= ops
   , reservedNames  = ["abs","true","false"] <> ops
   , caseSensitive  = False
   }
  where ops = fmap unarySymbols unaryPrecedence
          <> foldMap (toList . binarySymbols) (foldMap snd binaryPrecedence)
{-# INLINABLE mathLangDef #-}


lexer :: Monad m => GenTokenParser String u m
lexer = makeTokenParser mathLangDef
{-# INLINABLE lexer #-}

expr :: Monad m => ParsecT String u m Expr
expr = buildExpressionParser table term <?> "expression"
{-# INLINABLE expr #-}

term :: Monad m => ParsecT String u m Expr
term = parens expr
       <|> UnaryE Abs <$> (reserved "abs" >> parens expr)
       <|> VarE . VarName . toS <$> identifier
       <|> SetE <$> braces (commaSep expr)
       -- <|> try (UnaryE IsNonEmpty <$> angles expr)
       <|> UnaryE Iverson <$> squares expr
       <|> LiteralE <$> literal
       <?> "term"
  where TokenParser{..} = lexer
        literal = StringL . toS <$> stringLiteral
                  <|> BoolL <$> (True <$ reserved "true"
                                 <|> False <$ reserved "false")
                  <|> (DateL <$> lexeme (try dateParserYmd))
                  <|> NumberL . either fromInteger id <$> naturalOrFloat
{-# INLINABLE term #-}

number :: Monad m => Int -> ParsecT String u m Int
number size = do
  digits <- count size digit
  let n = foldl (\x d -> 10*x + digitToInt d) 0 digits
  seq n $ pure n
{-# INLINABLE number #-}

dateParserYmd :: Monad m => ParsecT String u m Day
dateParserYmd = do
  y <- number 4 
  char '-'
  m <- number 2
  char '-'
  d <- number 2
  pure $ fromBaseDay $ D.fromGregorian (toInteger y) m d
{-# INLINABLE dateParserYmd #-}


table :: Monad m => [[Operator String u m Expr]]
table = [[ Prefix $ UnaryE op <$ reservedOp (unarySymbols op) | op <- unaryPrecedence]]
  <> fmap (fmap (\(assoc, op) ->
                   Infix (BinaryE op <$ choice (reservedOp <$> toList (binarySymbols op))) assoc) . sequence) binaryPrecedence
  where TokenParser{..} = lexer
  -- where bin 
{-# INLINABLE table #-}

unaryPrecedence :: [UnaryOperator]
unaryPrecedence = [Not, Negate]

binaryPrecedence :: [(Assoc, [BinaryOperator])]
binaryPrecedence = fmap3 Base [(AssocLeft, [Product,Quotient])

         ,(AssocLeft, [Sum, Difference])

         ,(AssocNone, [Less ,LessEqual ,Greater ,GreaterEqual])
         ,(AssocRight, [Intersection])

         ,(AssocRight, [Union, SetDifference])
           
         ,(AssocNone, [Element, NotElement])

         ,(AssocNone, [Equal ,NotEqual])

         ,(AssocRight, [And])

         ,(AssocRight, [Xor])

         ,(AssocRight, [Or])

         ]
  <> fmap3 Extra
         [(AssocNone,   [StepHeight])

         ,(AssocRight,  [StepConcat])

         ,(AssocNone,   [StepFunction])
         ]


fullExprParser :: Monad m => ParsecT String u m Expr
fullExprParser = ws *> expr <* (ws >> eof)
  where ws = whiteSpace lexer
{-# INLINABLE fullExprParser #-}

parseExpr :: String -> Either ParseError Expr
parseExpr = parse fullExprParser ""
{-# INLINABLE parseExpr #-}

parseAndDesugarExpr :: Error m => String -> m DesugaredExpr
parseAndDesugarExpr = either (throwError . shot) desugarStepFunctions . parseExpr
{-# INLINABLE parseAndDesugarExpr #-}


