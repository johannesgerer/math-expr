
module MathExpr.Types where

import           Data.HashMap.Strict ()
import qualified Data.Text as T
import           Yahp hiding (Sum, Product)
import           Chronos
import           TextShow

type Error m = MonadError Text m

newtype VarName = VarName { unVarName :: Text }
  deriving (Read, Eq, Hashable, IsString, Ord)

instance TextShow VarName where
  showb (VarName n) = "VarName " <> fromText n

instance Show VarName where
  show (VarName n) = "VarName " <> T.unpack n

data Expr' a = VarE VarName
          | LiteralE Literal
          | UnaryE UnaryOperator (Expr' a)
          | BinaryE (BinaryOperator' a) (Expr' a) (Expr' a)
          | SetE [Expr' a]
  deriving (Read, Eq)

data UnaryOperator = Not | Negate | Iverson
  -- ^ Iverson bracket: True -> 1, False -> 0, {} -> False, nonempty set -> 1
  -- see Zippable.eval
  | Abs -- | IsNonEmpty
  deriving (Bounded, Enum, Show, Read, Eq)

data BinaryOperator' a = Base BaseOperator | Extra a
  deriving (Show, Read, Eq)

data BaseOperator = Sum | Difference | Product | Quotient                             -- arithmetics
                    | And | Or | Xor                                                    -- boolean
                    | Element | NotElement | Intersection | Union | SetDifference       -- sets
                    | Less | LessEqual | Equal | NotEqual | Greater | GreaterEqual      -- comparisons
  deriving (Show, Read, Eq)


data StepFunctionsOperators = StepFunction | StepConcat | StepHeight
  deriving (Bounded, Enum, Show, Read, Eq)

type Expr = Expr' StepFunctionsOperators
type BinaryOperator = BinaryOperator' StepFunctionsOperators
type DesugaredExpr = Expr' Void

data Literal = BoolL Bool
             | NumberL Double
             | StringL Text
             | DateL Day
  deriving (Show, Read, Eq)

instance HasBinarySymbols a => Show (Expr' a) where
  show = toS . pretty

pretty :: HasBinarySymbols a => Expr' a -> Text
pretty = \case
  VarE          v -> unVarName v
  LiteralE      l -> case l of
    BoolL    b -> shot b
    NumberL  b -> shot b
    StringL  b -> shot b
    DateL    b -> shot b
  SetE          l -> "{" <> (T.intercalate ", " $ pretty <$> toList l) <> "}"
  UnaryE op e  -> let std' sep = unarySymbols op <> sep <> parens e
                      std = std' ""
                      func = std' " "
                  in case op of
    Not         -> std
    Negate      -> std
    Abs         -> func
    Iverson     -> "[" <> pretty e <> "]"
    -- IsNonEmpty  -> "<" <> pretty e <> ">"
  BinaryE op e1 e2 -> parens e1 <> " " <> head (binarySymbols op) <> " " <> parens e2
  where parens          e = case e of
          UnaryE Iverson _ -> wop
          UnaryE _ _    -> withp
          BinaryE _ _ _ -> withp
          SetE _        -> wop
          VarE _        -> wop
          LiteralE _    -> wop
          where (wop, withp) = (pretty e, "(" <> wop <> ")")
{-# INLINABLE pretty #-}

class HasBinarySymbols a where
  extraBinarySymbols :: IsString t => a -> NonEmpty t

instance HasBinarySymbols Void where
  extraBinarySymbols = \case
  {-# INLINE extraBinarySymbols #-}
    
instance HasBinarySymbols StepFunctionsOperators where
  extraBinarySymbols = \case
    StepFunction              -> "?"  :| []
    StepHeight                -> ":"  :| []
    StepConcat                -> ";"  :| []
  {-# INLINABLE extraBinarySymbols #-}
  

binarySymbols :: (IsString a, HasBinarySymbols b) => BinaryOperator' b -> NonEmpty a
binarySymbols (Base op) = case op of
              Product                   -> "*"  :| []
              Quotient                  -> "/"  :| []
              Sum                       -> "+"  :| []
              Difference                -> "-"  :| []
              Less                      -> "<"  :| []
              LessEqual                 -> "≤"  :| ["<="]
              Greater                   -> ">"  :| []
              GreaterEqual              -> "≥" :| [">="]
              Equal                     -> "="  :| []
              NotEqual                  -> "≠"  :| ["/="]
              And                       -> "&"  :| []
              Xor                       -> "^"  :| []
              Or                        -> "|"  :| []
              Intersection              -> "∩"  :| ["cap"]
              Union                     -> "∪"  :| ["cup"]
              SetDifference             -> "\\" :| []
              Element                   -> "∈"  :| ["in"]
              NotElement                -> "∉"  :| ["notIn"]
binarySymbols (Extra op) = extraBinarySymbols op
{-# INLINABLE binarySymbols #-}



unarySymbols :: IsString a => UnaryOperator -> a
unarySymbols = \case
  Not           -> "~"
  Negate        -> "-"
  Iverson       -> "Iverson"
  Abs           -> "Abs"
  -- IsNonEmpty    -> "IsNonEmpty"
{-# INLINABLE unarySymbols #-}

-- * Helpers

varE :: Text -> Expr' e
varE           = VarE . VarName
{-# INLINE varE #-}

stringE :: Text -> Expr' e
stringE           = LiteralE . StringL
{-# INLINE stringE #-}

boolE :: Bool -> Expr' e
boolE           = LiteralE . BoolL
{-# INLINE boolE #-}

numE :: Double -> Expr' e
numE             = LiteralE . NumberL
{-# INLINE numE #-}

prodE :: Eq a => Expr' a -> Expr' a -> Expr' a
prodE a b | a == oneE                   = b
          | b == oneE                   = a
          | a == nullE || b == nullE    = nullE
          | True                        = BinaryE (Base Product) a b
{-# INLINABLE prodE #-}


-- pattern NullE = LiteralE (NumberL 0)
-- pattern OneE = LiteralE (NumberL 1)

nullE :: Expr' e
nullE = numE 0
{-# INLINE nullE #-}

oneE :: Expr' e
oneE = numE 1
{-# INLINE oneE #-}

absE :: Expr' a -> Expr' a
absE            = UnaryE Abs
{-# INLINE absE #-}

iversonE :: Expr' a -> Expr' a
iversonE        = UnaryE Iverson
{-# INLINE iversonE #-}

orE :: Expr' a -> Expr' a -> Expr' a
orE             = BinaryE $ Base Or
{-# INLINE orE #-}

andE :: Expr' a -> Expr' a -> Expr' a
andE            = BinaryE $ Base And
{-# INLINE andE #-}

greaterEqualE :: Expr' a -> Expr' a -> Expr' a
greaterEqualE   = BinaryE $ Base GreaterEqual
{-# INLINE greaterEqualE #-}

notEqE :: Expr' a -> Expr' a -> Expr' a
notEqE           = BinaryE $ Base NotEqual
{-# INLINE notEqE #-}

eqE :: Expr' a -> Expr' a -> Expr' a
eqE           = BinaryE $ Base Equal
{-# INLINE eqE #-}

lessE :: Expr' a -> Expr' a -> Expr' a
lessE           = BinaryE $ Base Less
{-# INLINE lessE #-}

quotientE :: Expr' a -> Expr' a -> Expr' a
quotientE       = BinaryE $ Base Quotient
{-# INLINE quotientE #-}

notE :: Expr' a -> Expr' a
notE            = UnaryE Not
{-# INLINE notE #-}

negateE :: Expr' a -> Expr' a
negateE             = UnaryE Negate
{-# INLINE negateE #-}

differenceE :: Expr' a -> Expr' a -> Expr' a
differenceE             = BinaryE $ Base Difference
{-# INLINE differenceE #-}

sumE :: Expr' a -> Expr' a -> Expr' a
sumE             = BinaryE $ Base Sum
{-# INLINE sumE #-}

