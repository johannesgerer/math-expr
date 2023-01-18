{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}

module MathExpr.Zippable where


import           Chronos
import           Control.Monad.Writer (tell, runWriter)
import           Data.Functor.Classes
import qualified Data.Set as S
import           Data.Time.Calendar (fromGregorian)
import           MathExpr.Parser
import           MathExpr.Transformations
import           MathExpr.Types
import           Yahp hiding (Sum, Product)

-- * Value type

data ValueDyn f   = StringV (f Text)
                  | NumberV (f Double)
                  | BoolV   (f Bool)
                  | DateV   (f Day)

valueDynZip :: (Typeable f, Typeable g, Error m)
  => Text -> (forall a . IsDynValue a => f a -> g a -> b) -> ValueDyn f -> ValueDyn g -> m b
valueDynZip msg f a b = case (a, b) of
    (StringV    x, StringV     y) -> pure $ f x y
    (NumberV    x, NumberV     y) -> pure $ f x y
    (BoolV      x, BoolV       y) -> pure $ f x y
    (DateV      x, DateV       y) -> pure $ f x y
    _ -> throwError $ "'" <> msg <> "' requires two operands of the same type, got: "
              <> valueDynType "" a <> " and  " <> valueDynType "" b
{-# INLINABLE valueDynZip #-}
  

data Value f = ConstValue (ValueDyn I)
             | DynValue (ValueDyn f)
             | ConstSet (ValueDyn Set)
             | DynSet (ValueDyn (f :.: Set))

mapValueDyn :: (forall a . IsDynValue a => f a -> g a) -> ValueDyn f -> ValueDyn g
mapValueDyn g = withValueDyn $ toDynValue . g
{-# INLINABLE mapValueDyn #-}

withValueDyn :: (forall a . IsDynValue a => f a -> b) -> ValueDyn f -> b
withValueDyn f = \case
  StringV     s -> f s
  NumberV     s -> f s
  BoolV       s -> f s
  DateV       s -> f s
{-# INLINABLE withValueDyn #-}

eitherScalarOrDyn :: (Typeable f, IsDynValue a, Error m) => Value f -> m (Either a (f a))
eitherScalarOrDyn = \case
  ConstValue    x       -> Left <$> fromConstValue x
  DynValue      x       -> Right <$> fromDynValue x
  ConstSet      l       -> throwError $ "Expected scalar, got set of size " <> shot (withValueDyn length l)
  -- ConstSet      l       -> throwError $ "Expected scalar, got set of size " <> shot (maybe 0 (withValueDyn length) l)
  DynSet        _       -> throwError $ "Expected scalar, got dynamic set"
{-# INLINABLE eitherScalarOrDyn #-}

fromScalarValue :: (Typeable f, IsDynValue a, Error m) => (a -> f a) -> Value f -> m (f a)
fromScalarValue pure' = fmap2 (either pure' id) eitherScalarOrDyn
{-# INLINABLE fromScalarValue #-}

-- instance (Typeable f, Eq1 f)  => Eq (ValueDyn f) where
  -- (==) = fmap (either (const False) id) <$> valueDynZip "(==)" eq1

deriving instance Eq (ValueDyn Set)
deriving instance Ord (ValueDyn Set)
deriving instance Eq (ValueDyn (I :.: Set))
deriving instance Ord (ValueDyn (I :.: Set))
deriving instance Eq (ValueDyn I)
deriving instance Ord (ValueDyn I)
deriving instance Eq (Value I)

-- mapValue :: (forall a . IsDynValue a => f a -> g a) -> Value f -> Value g
-- mapValue g = \case
--   DynValue      v  -> DynValue $ mapValueDyn g v
--   ConstValue    v  -> ConstValue v
--   ConstSet      v  -> ConstSet v
--   DynSet        v  -> DynSet $ mapValueDyn (Comp . g . unComp) v
-- {-# INLINABLE mapValue #-}

type ContextSatifies a f =
  (Show1 f, a (f Day), a (f Text), a (f Double), a (f Bool)) :: Constraint

showValueDyn :: ContextSatifies Show f => ValueDyn f -> Text
showValueDyn = \case -- this needs to it would need `Show (f a)`
  StringV     s -> shot s
  NumberV     s -> shot s
  BoolV       s -> shot s
  DateV       s -> shot s
{-# INLINABLE showValueDyn #-}


showValue :: forall f . ContextSatifies Show f  => Value f -> Text
showValue = \case
  ConstValue    v  -> showValueDyn v
  DynValue      v  -> showValueDyn v
  ConstSet      v  -> showValueDyn v
  -- ConstSet      v  -> maybe "[]" (showValueDyn . mapValueDyn toList) v
  DynSet        v  -> showValueDyn v
{-# INLINABLE showValue #-}

instance ContextSatifies Show f  => Show (Value f) where
  show = toS . showValue
  {-# INLINABLE show #-}



valueType :: forall f . Typeable f => Value f -> Text
valueType = \case
  ConstValue    v -> valueDynType "" v
  DynValue      v -> valueDynType (" " <> shot (typeRep $ Proxy @f))v
  -- ConstSet v -> maybe "∅" (\x -> "{" <> valueDynType "" x <> "}") v
  ConstSet v -> "{" <> valueDynType "" v <> "}"
  DynSet   v -> "{" <> valueDynType "" v <> "}"
{-# INLINABLE valueType #-}

valueDynType :: forall f . Typeable f => Text -> ValueDyn f -> Text
valueDynType suf = (<> suf) . withValueDyn (shot . typeOf)
{-# INLINABLE valueDynType #-}

class (Typeable a, Ord a, Eq a) => IsDynValue a where
  toDynValue            ::                              f a          -> ValueDyn f
  fromDynValue          :: (Error m, Typeable f) =>     ValueDyn f   -> m (f a)

toConstValue :: IsDynValue a => a -> ValueDyn I
toConstValue    = toDynValue . I
{-# INLINABLE toConstValue #-}

fromConstValue :: (IsDynValue b, Error m) => ValueDyn I -> m b
fromConstValue  = fmap2 unI fromDynValue
{-# INLINABLE fromConstValue #-}

fromConstSet :: (IsDynValue b, Error m) => Maybe (ValueDyn Set) -> m (Set b)
fromConstSet = maybe (pure mempty) fromDynValue
{-# INLINABLE fromConstSet #-}

fromDynSet :: (Typeable f, IsDynValue b, Error m) => ValueDyn (f :.: Set) -> m (f (Set b))
fromDynSet = fmap unComp . fromDynValue
{-# INLINABLE fromDynSet #-}

typeError :: (Error m, Typeable f) => Text -> ValueDyn f -> m a
typeError exp got = throwError $ "Expected '" <> exp <> "', got: " <> valueDynType "" got
{-# INLINABLE typeError #-}

instance IsDynValue Text    where
  toDynValue = StringV
  fromDynValue v = case v of { StringV s -> pure s; _ -> typeError "String" v }

instance IsDynValue Day    where
  toDynValue = DateV
  fromDynValue v = case v of { DateV s -> pure s; _ -> typeError "Day" v }

instance IsDynValue Double    where
  toDynValue = NumberV
  fromDynValue v = case v of { NumberV s -> pure s; _ -> typeError "Number" v }

instance IsDynValue Bool    where
  toDynValue = BoolV
  fromDynValue v = case v of { BoolV s -> pure s; _ -> typeError "Bool" v }

constV :: IsDynValue a => a -> Value f
constV   = ConstValue    . toConstValue
{-# INLINABLE constV #-}

dynSetV :: IsDynValue a => f (Set a) -> Value f
dynSetV = DynSet . toDynValue . Comp
{-# INLINABLE dynSetV #-}

constSetV :: IsDynValue a => Set a -> Value f
constSetV = ConstSet . toDynValue
{-# INLINABLE constSetV #-}

dynV :: IsDynValue a => f a -> Value f
dynV     = DynValue      . toDynValue
{-# INLINABLE dynV #-}

mapUnary :: (IsDynValue a, IsDynValue b, Error m, Typeable f, Functor f)
  => Text -> (a -> b) -> Value f -> m (Value f)
mapUnary opName g v = case v of
  ConstValue    a -> constV       . g            <$> fromConstValue a
  DynValue      a -> dynV         . fmap g       <$> fromDynValue a
  _ -> throwError $ "'" <> opName <> "' not supported on Sets"
{-# INLINABLE mapUnary #-}

mapBinary2 :: (IsDynValue b, Error m, Typeable f, Zippable f)
  => BaseOperator -> (forall a . IsDynValue a => a -> a -> b) -> Value f -> Value f -> m (Value f)
mapBinary2 opName g v1 v2 = case (v1, v2) of
  (ConstValue   a1, ConstValue  a2)     -> constV <$> valueDynZip msg (on g unI) a1 a2
  (ConstValue   a1, DynValue    a2)     -> dynV <$>  valueDynZip msg (fmap . g . unI) a1 a2
  (DynValue     a1, ConstValue  a2)     -> dynV <$> valueDynZip msg (fmap . (flip g) . unI) a2 a1
  (DynValue     a1, DynValue    a2)     -> dynV <$> valueDynZip msg (zipWith_ g) a1 a2
  _                                     -> throwError $ "'" <> msg <> "' not supported on Sets"
  where msg = shot opName
{-# INLINABLE mapBinary2 #-}

mapBinary :: (IsDynValue a1, IsDynValue a2, IsDynValue b, Error m, Typeable f, Zippable f)
  => BaseOperator -> (a1 -> a2 -> b) -> Value f -> Value f -> m (Value f)
mapBinary opName g v1 v2 = case (v1, v2) of
  (ConstValue   a1, ConstValue  a2)     -> fmap2 constV g <$> fromConstValue a1 <*> fromConstValue a2
  (ConstValue   a1, DynValue    a2)     -> fmap dynV . fmap . g  <$> fromConstValue a1 <*> fromDynValue a2
  (DynValue     a1, ConstValue  a2)     -> fmap dynV . fmap . flip g <$> fromConstValue a2 <*> fromDynValue a1
  (DynValue     a1, DynValue    a2)     -> fmap dynV . zipWith_ g <$> fromDynValue a1 <*> fromDynValue a2
  _                                     -> throwError $ "'" <> shot opName <> "' not supported on Sets"
{-# INLINABLE mapBinary #-}

setBinary :: (Zippable f, Functor f, Typeable f, Error m)
  => BaseOperator -> (forall a . IsDynValue a => Set a -> Set a -> Set a)
  -> Value f -> Value f -> m (Value f)
setBinary opName g v1 v2 = case (v1, v2) of
  (ConstSet     a1, ConstSet    a2)     -> valueDynZip msg (fmap2 constSetV g) a1 a2
  (ConstSet     a1, DynSet      a2)     -> valueDynZip msg (\a -> dynSetV . fmap (g a) . unComp) a1 a2
  (DynSet       a1, ConstSet    a2)     -> valueDynZip msg (\a -> dynSetV . fmap (flip g a) . unComp) a2 a1
  (DynSet       a1, DynSet      a2)     -> valueDynZip msg (fmap2 dynSetV $ on (zipWith_ g) unComp) a1 a2
  _ -> err
  where err = throwError $ "'" <> shot opName <> "' requires two Sets, got: "
              <> valueType v1 <> " and " <> valueType v2
        msg = shot opName
{-# INLINABLE setBinary #-}

element' :: forall f m . (Error m, Typeable f, Functor f, Zippable f)
  => Bool -> Value f -> Value f -> m (Value f)
element' negate v s = case s of
  -- SetValue s   -> maybe (pure $ constV negate) (withValueDyn mapU) s
  ConstSet      s -> withValueDyn mapU s
  DynSet        s -> case v of
    ConstValue    e -> dynV <$> valueDynZip msg (\(I a) -> fmap (g a) . unComp) e s
    DynValue      e -> dynV <$> valueDynZip msg (\a -> zipWith_ g a . unComp) e s
    _ -> err
  _ -> err
  where err = throwError $ "'∈' requires two Value and Set of the same type, got: "
              <> valueType v <> " and  " <> valueType s
        mapU :: (IsDynValue a, Ord a) => Set a -> m (Value f)
        mapU x = mapUnary msg (flip g x) v
        g :: Ord a => a -> Set a -> Bool
        g = fmap2 (xor negate) S.member
        msg = "∈ {}"
{-# INLINABLE element' #-}
  

requireConst :: (HasBinarySymbols a, Error m) => Expr' a -> Value f -> m (ValueDyn I)
requireConst e = \case
  ConstValue    c -> pure c
  _ -> throwError $ "Only constants are allowed in sets, got: " <> pretty e
{-# INLINABLE requireConst #-}

fromConstValueList :: Error m => [ValueDyn I] -> m (Value f)
fromConstValueList = \case
  [] -> throwError $ "Empty set expressions not implemented because their "
    <> "requires either polymorphism or explicit typ annotations"
  (h:t) -> withValueDyn (\(I v) -> (\r -> constSetV $ S.fromList $ v:r) <$> mapErrors fromConstValue t) h
{-# INLINABLE fromConstValueList #-}


-- * Evaluation

type VarValues m f = VarName -> m (Value f)

evalStepFunctionSteps :: forall f m . (Error m, Typeable f, Zippable f)
  => VarValues m f -> StepFunctionSteps -> m (NonEmpty (Maybe (Value f), Maybe (Value f)))
evalStepFunctionSteps vars = mapM $ \(b,v) -> on (liftA2 (,)) (mapM $ eval vars) b v
{-# INLINABLE evalStepFunctionSteps #-}
  
evalTopLevelStepFunctionSteps :: (MonadError Text m, Typeable f, Zippable f) =>
     VarValues m f -> Expr -> m (NonEmpty (Maybe (Value f), Maybe (Value f)))
evalTopLevelStepFunctionSteps vars e = evalStepFunctionSteps vars =<< topLevelStepFunctionSteps e
{-# INLINABLE evalTopLevelStepFunctionSteps #-}

eval :: forall f m . (Error m, Typeable f, Zippable f) => VarValues m f -> DesugaredExpr -> m (Value f)
eval vars expr = case expr of 
  VarE          v -> vars v
  LiteralE      l -> pure $ ConstValue $ case l of
    BoolL    b  -> BoolV        $ I b
    NumberL  b  -> NumberV      $ I b
    StringL  b  -> StringV      $ I b
    DateL    b  -> DateV        $ I b
  SetE          l -> fromConstValueList =<< mapM (\e -> requireConst e =<< recurse e) l
  UnaryE op e  -> recurse e >>= let opt = shot op in case op of
    Not         -> mapUnary opt not
    Abs         -> mapUnary opt $ abs @Double
    Negate      -> mapUnary opt $ negate @Double
    Iverson     -> \case
      ConstValue (BoolV (I b))  -> pure $ constV @Double $ bool 0 1 b
      DynValue   (BoolV v)      -> pure $ dynV   @Double $ bool 0 1 <$> v
      ConstSet  l               -> pure $ constV $ withValueDyn (not . null) l
      -- ConstSet l                    -> pure $ constV $ maybe False ((>0) . withValueDyn length) l
      DynSet    v               -> pure $ withValueDyn (dynV . fmap (not . null) . unComp) v
      _ -> throwError $ "'Iverson' only supported on Bool values or sets"
  BinaryE (Extra op) _ _ -> case op of
  BinaryE (Base op) e1 e2 -> chain2 (evalBinaryOp op) (recurse e1) $ recurse e2
  where recurse = eval vars
{-# INLINABLE eval #-}

evalBinaryOp :: forall f m . (Error m, Typeable f, Zippable f)
  => BaseOperator -> Value f -> Value f -> m (Value f)
evalBinaryOp op a b =
  let mb2 g = mapBinary2 op g a b
      mb2 :: IsDynValue b => (forall a . IsDynValue a => a -> a -> b) -> m (Value f)
  in case op of
  Sum         -> case a of
    NullV     -> pure b
    _         -> case b of
      NullV   -> pure a
      _       -> mapBinary @Double op (+) a b
  Difference  -> case a of
    NullV     -> mapUnary (shot op) (negate @Double) b
    _         -> case b of
      NullV   -> pure a
      _       -> mapBinary @Double op (-) a b
  Product     -> case a of
    NullV     -> pure nullV
    OneV      -> pure b
    _         -> case b of
      NullV   -> pure nullV
      OneV    -> pure a
      _       -> mapBinary @Double op    (*) a b
  Quotient    -> case a of
    NullV     -> pure nullV
    _         -> case b of
      OneV    -> pure a
      _       -> mapBinary @Double op    (/) a b
  And         -> case a of
    FalseV    -> pure falseV
    TrueV     -> pure b
    _         -> case b of
      FalseV  -> pure falseV
      TrueV   -> pure a
      _       -> mapBinary op    (&&) a b
  Or          -> case a of
    FalseV    -> pure b
    TrueV     -> pure trueV
    _         -> case b of
      FalseV  -> pure a
      TrueV   -> pure trueV
      _       -> mapBinary op    (||) a b
  Xor         -> case a of
    TrueV     -> mapUnary (shot op) not b
    FalseV    -> pure b
    _         -> case b of
      TrueV   -> mapUnary (shot op) not a
      FalseV  -> pure a
      _       -> mapBinary @Bool op    xor a b
  Less                -> mb2    (<)
  LessEqual           -> mb2    (<=)
  Equal               -> mb2    (==)
  NotEqual            -> mb2    (/=)
  Greater             -> mb2    (>)
  GreaterEqual        -> mb2    (>=)
  Intersection        -> setBinary op S.intersection a b
  Union               -> setBinary op S.union a b
  SetDifference       -> setBinary op S.difference a b
  Element             -> element' False a b
  NotElement          -> element' True  a b
{-# INLINABLE evalBinaryOp #-}

            
parseAndEval :: (Error m, Typeable f, Zippable f) => VarValues m f -> String -> m (Value f)
parseAndEval vars = chain (eval vars) . either (throwError . shot) desugarStepFunctions . parseExpr
{-# INLINABLE parseAndEval #-}


exampleVars :: [(Text, Value ([] :.: (->) Double))]
exampleVars = [("a", dynV $ Comp [(+10), (+ (-2)), negate])
              ,("b", dynV $ Comp [("v" <>) . shot])
              ,("t", constV @Text "v8.0")
              ,("d", constV @Double 2.5)]

-- | 
-- λ>  runExample "a+a" 3
-- ZipList {getZipList = [26.0,2.0,-6.0]}
-- runExample :: MonadIO m => String -> Double -> m ()
-- runExample x y = either putStrLn putStrLn $ showValue . mapValue (fmap ($ y) . unComp)
--   <$> parseAndEval (flip lookupThrow $ HM.fromList $ first VarName <$> exampleVars) x 


-- | 
-- λ>  runExample2 "(b cap c) + a"
-- (Left "'Intersection' requires two Sets of the same type, got: Number and  Number",["b","c"])
-- 
-- λ> runExample2 "d ? 2022-03-01:2"
-- (Right I 0.0,["d"])
runExample2 :: String -> (Either Text (Value I), [Text])
runExample2 = runWriter . runExceptT . parseAndEval (\v -> constV (fromBaseDay $ fromGregorian 2022 1 1) <$ tell [unVarName v])


pattern FalseV  = ConstValue (BoolV (I False))
pattern TrueV  = ConstValue (BoolV (I True))
pattern NullV  = ConstValue (NumberV (I 0))
pattern OneV   = ConstValue (NumberV (I 1))

falseV :: Value f
falseV  = constV False
{-# INLINE falseV #-}

trueV :: Value f
trueV   = constV True
{-# INLINE trueV #-}

nullV :: Value f
nullV   = constV @Double 0
{-# INLINE nullV #-}

zeroV :: Value f
zeroV    = constV @Double 0
{-# INLINE zeroV #-}

oneV :: Value f
oneV    = constV @Double 1
{-# INLINE oneV #-}

infV :: Value f
infV    = constV @Double $ 1.0/0.0
{-# INLINE infV #-}

