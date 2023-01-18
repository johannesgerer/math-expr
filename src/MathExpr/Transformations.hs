
module MathExpr.Transformations where

import qualified Data.List.NonEmpty as E
import qualified Data.Set as S
import qualified Data.Vector as V
import           GHC.Stack
import           MathExpr.Types
import           Yahp hiding (Sum, Product)

-- * Step Functions

-- | 
--   λ> parseAndDesugarExpr @(Either Text) "a ? 2021-03-27 : d ; c"
--   Right d * [(a ≥ 2021-03-27) & (a < c)]
--   λ> parseAndDesugarExpr @(Either Text) "a ? 2021-03-27 : 4"
--   Right 4.0 * [a ≥ 2021-03-27]
--   λ> parseAndDesugarExpr @(Either Text) "a ? 3; 2021-03-27"
--   Right 3.0 * [a < 2021-03-27]
--   λ> parseAndDesugarExpr @(Either Text) "a ? 3; 2021-03-27: 5"
--   Right (3.0 * [a < 2021-03-27]) + (5.0 * [a ≥ 2021-03-27])
--   λ> parseAndDesugarExpr @(Either Text) "a ? 3; 2021-03-27: 5 ; 2022-03-27"
--   Right (3.0 * [a < 2021-03-27]) + (5.0 * [(a ≥ 2021-03-27) & (a < 2022-03-27)])
--   λ> parseAndDesugarExpr @(Either Text) "a ? 2021-03-27 : 4; 2022-03-27"
--   Right 4.0 * [(a ≥ 2021-03-27) & (a < 2022-03-27)]
desugarStepFunctions :: Error m => Expr -> m DesugaredExpr
desugarStepFunctions = \case
  UnaryE o e -> UnaryE o <$> desugarStepFunctions e
  BinaryE (Base op) e1 e2 -> BinaryE (Base op) <$> desugarStepFunctions e1 <*> desugarStepFunctions e2
  BinaryE (Extra op) f1 rest1 -> case op of
    StepConcat -> err op
    StepHeight -> err op
    StepFunction -> stepFunctionToExpr <$> desugarStepFunctions f1 <*> topLevelStepFunctionSteps rest1
    where err op = throwError $ binasyOpString op <> " has to be inside of step function"
  SetE          s -> SetE <$> mapM desugarStepFunctions s
  VarE          v -> pure $ VarE v
  LiteralE      l -> pure $ LiteralE      l
{-# INLINABLE desugarStepFunctions #-}


-- | list of (lower bound; values)-pairs
-- (Nothing, v          ) = first step starts at negative infinity
-- (s      , Nothing    ) = last step goes up to `s` (exclusive)
type StepFunctionSteps = NonEmpty (Maybe DesugaredExpr, Maybe DesugaredExpr)

-- | return step function argument (left of the `?`) and steps
-- 
-- λ> either (Left . shot) toplevelStepFunction $ parseExpr "a ? 3; 2021-03-27: 5; c"
-- Right (a,(Nothing,Just 3.0) :| [(Just 2021-03-27,Just 5.0),(Just c,Nothing)])
-- Nothing = unbounded
toplevelStepFunction :: forall m . Error m => Expr -> m (DesugaredExpr, StepFunctionSteps)
toplevelStepFunction = \case
  BinaryE (Extra StepFunction) f1 rest1 -> (,) <$> desugarStepFunctions f1
    <*> topLevelStepFunctionSteps rest1
  e -> throwError $ "Not a step function: " <> shot e
{-# INLINABLE toplevelStepFunction #-}

-- | returns lower bound of the first step and the upper bound of the last step
--
-- Nothing = unbounded
--
-- λ> either (Left . shot) stepFunctionCover $ parseExpr "a ? 3; 2021-03-27: 5; c"
-- Right (Nothing,Just c)
--
-- λ> either (Left . shot) stepFunctionCover $ parseExpr "a ? 2021-03-27: 5; c"
-- Right (Just 2021-03-27,Just c)
--
-- λ> either (Left . shot) stepFunctionCover $ parseExpr "a ? 2021-03-27: 5; c: 10"
-- Right (Just 2021-03-27,Nothing)
stepFunctionCover :: forall m . Error m => Expr -> m (Maybe DesugaredExpr, Maybe DesugaredExpr)
stepFunctionCover = fmap (g . snd) . toplevelStepFunction
  where g = fst . E.head &&& (\(b, v) -> b <* guard (isNothing v)) . E.last


topLevelStepFunctionSteps :: forall m . Error m => Expr -> m StepFunctionSteps
topLevelStepFunctionSteps = g (Just @Text "first")
  where
    g n = \case
      BinaryE (Extra StepConcat) e1 e2 -> (<>) <$> f n e1 <*> g Nothing e2
      r -> f (msum [n, Just "last"]) r
    f _ (BinaryE (Extra StepHeight) e1 e2) = (\x -> pure . (Just x,) . Just)
                                             <$> desugarStepFunctions e1 <*> desugarStepFunctions e2
    f (Just "first") r = pure . (Nothing,) . Just <$> desugarStepFunctions r
    f (Just "last") r = pure . (,Nothing). Just  <$>  desugarStepFunctions r 
    f _ r = throwError $ "Expected " <> binasyOpString StepHeight
      <> "-expression in the middle of a step function, got " <> shot r
{-# INLINABLE topLevelStepFunctionSteps #-}

binasyOpString = shot . toList . binarySymbols @Text . Extra
binasyOpString :: StepFunctionsOperators -> Text

-- | Turn a step function description into a sum of products of the
-- form `height * [condition]`
stepFunctionToExpr :: DesugaredExpr
                      -- ^ the expression to compare
                      -> StepFunctionSteps -> DesugaredExpr
stepFunctionToExpr comp steps = maybe (numE 0) (foldr1 sumE) $ nonEmpty
  $ catMaybes $ zipWith g (toList steps) $ (E.tail steps) <> [(Nothing, Nothing)]
  where g (_, Nothing) _ = Nothing
        g (lb, Just h) (ub, _) = Just $ maybe h (prodE h . iversonE . foldr1 andE)
                                 $ nonEmpty $ catMaybes [greaterEqualE comp <$> lb, lessE comp <$> ub]
        g :: (Maybe DesugaredExpr, Maybe DesugaredExpr) -> (Maybe DesugaredExpr, a) -> Maybe DesugaredExpr
{-# INLINABLE stepFunctionToExpr #-}
          
-- * Derivatives

-- | λ> either putStrLn print $ derivative (VarName "a") =<< parseAndDesugarExpr "a * (b? 3:4)"
--   4.0 * [b ≥ 3.0]
derivative :: Error m => VarName -> DesugaredExpr -> m DesugaredExpr
derivative var ex = case recurse ex of
  NoOccurence           -> pure nullE
  NonDifferentiable   t -> throwError $ "Non differentiable: " <> t
  Derivative          d -> pure d
  where recurse = \case
          VarE v2       -> bool NoOccurence (Derivative oneE) $ v2 == var
          LiteralE _    -> NoOccurence
          UnaryE op ex -> let d = recurse ex
                              nond = nonDifferentiable (shot op) d in case op of
            Not         -> nond
            Abs         -> nond
            Iverson     -> nond
            -- IsNonEmpty  -> nond
            Negate      -> fmap (UnaryE Negate) d
          BinaryE (Base op) ex1 ex2 -> let d1 = recurse ex1
                                           d2 = recurse ex2
                                           diff = derivativeOp differenceE negateE
                                           sum = derivativeOp sumE id
                                           prodSum f = f (prodE ex2 <$> d1) (prodE ex1 <$> d2)
                                           nond = nonDifferentiableBinary (shot op) d1 d2 in case op of
            Sum                         -> sum d1 d2
            Difference                  -> diff d1 d2
            Product                     -> prodSum sum
            Quotient                    -> case d2 of
              NoOccurence               -> flip quotientE ex2 <$> d1
              NonDifferentiable _       -> d2
              _                         -> flip quotientE (prodE ex2 ex2) <$> (prodSum diff)
            Less                        -> nond
            LessEqual                   -> nond
            Greater                     -> nond
            GreaterEqual                -> nond
            Equal                       -> nond
            NotEqual                    -> nond
            And                         -> nond
            Xor                         -> nond
            Or                          -> nond
            Intersection                -> nond
            Union                       -> nond
            SetDifference               -> nond
            Element                     -> nond
            NotElement                  -> nond
            
          BinaryE (Extra op) _ _ -> case op of
          
          SetE s -> if all hasNoOccurence $ recurse <$> s then NoOccurence
                    else NonDifferentiable "Set"
{-# INLINABLE derivative #-}

data Derivative e = NoOccurence | NonDifferentiable Text | Derivative e
  deriving (Functor, Eq, Show)

type DerivativeExpr = Derivative DesugaredExpr

hasNoOccurence :: Derivative e -> Bool
hasNoOccurence = \case
  NoOccurence -> True
  _ -> False
{-# INLINABLE hasNoOccurence #-}

derivativeOp :: (Expr' a -> Expr' a -> Expr' a) -> (Expr' a -> Expr' a)
  -> Derivative (Expr' a) -> Derivative (Expr' a) -> Derivative (Expr' a)
derivativeOp _  f NoOccurence x = f <$> x
derivativeOp _  _ x NoOccurence = x
derivativeOp _  _ x@(NonDifferentiable _) _ = x
derivativeOp _  _ _ x@(NonDifferentiable _) = x
derivativeOp op _  (Derivative a) b = op a <$> b
{-# INLINABLE derivativeOp #-}

nonDifferentiableBinary :: Text -> Derivative e1 -> Derivative e2 -> Derivative e3
nonDifferentiableBinary reason a b = case (a,b) of
  (NoOccurence, NoOccurence) -> NoOccurence
  _ -> NonDifferentiable reason
{-# INLINABLE nonDifferentiableBinary #-}

nonDifferentiable :: Text -> Derivative e1 -> Derivative e2
nonDifferentiable reason = \case
  NoOccurence -> NoOccurence
  _ -> NonDifferentiable reason
{-# INLINABLE nonDifferentiable #-}


substitute :: Applicative m => (VarName -> m (Maybe (Expr' a)))
           -> Expr' a
           -> m (Expr' a)
substitute repl orig = g orig
  where g x = case x of 
          VarE          v -> fromMaybe x <$> repl v
          LiteralE      _ -> pure x
          SetE          l -> fmap SetE $ traverse g l
          UnaryE op     e -> UnaryE op <$> g e
          BinaryE o   a b -> BinaryE o <$> g a <*> g b
{-# INLINABLE substitute #-}

variableNames :: Expr' a -> [VarName]
variableNames = \case
  VarE          v -> [v]
  LiteralE      _ -> []
  SetE          l -> foldMap variableNames l
  UnaryE _ e  -> variableNames e
  BinaryE _ e1 e2 -> on (<>) variableNames e1 e2
{-# INLINABLE variableNames #-}

maxBool :: MonadError Text m => S.Set VarName -> DesugaredExpr -> m DesugaredExpr
maxBool v = fmap2 snd $ boundAbs v $ BoolT True
{-# INLINABLE maxBool #-}

minBool :: MonadError Text m => S.Set VarName -> DesugaredExpr -> m DesugaredExpr
minBool v = fmap2 snd $ boundAbs v $ BoolT False
{-# INLINABLE minBool #-}

maxAbs :: MonadError Text m => S.Set VarName -> DesugaredExpr -> m DesugaredExpr
maxAbs v = fmap2 snd $ boundAbs v MaxAbsNonZeroT
{-# INLINABLE maxAbs #-}


-- | returns an upper or lower bound for abs(f(x)) where x is the
-- tuple of variables passed to this funtion, whose values range over
-- every possible value
--
-- first part of the returned pair indicates whether f depends on x
boundAbs ::  forall m . MonadError Text m
  => S.Set VarName -> BoundType -> DesugaredExpr -> m (Bool, DesugaredExpr)
{-# INLINABLE boundAbs #-}
boundAbs vars btype e0 = let
  recurse = boundAbs vars btype
  inverse e = flip (boundAbs vars) e =<< typeInverse btype
  useIndependentSelf = pure (False, typeAbsE btype e0)
  maxV = pure (True, typeBoundE btype)
  useMaxIf = bool useIndependentSelf maxV
  useIndependentSelfOr f a b = do
    (d1,b1) <- a
    (d2,b2) <- b
    if d1 || d2 then (True,) <$> f b1 b2 else useIndependentSelf
  useMaxIfnonIndependent1 = useMaxIf . not . independent vars
  typeError :: HasCallStack => a -> m b
  typeError _ = throwError $ "boundAbs expected " <> typeName btype <> ", got: " <> shot e0
    <> "\n" <> toS (prettyCallStack callStack)
  withBool      = case btype of { BoolT _               -> id; _ -> typeError }
  withNumber    = case btype of { MaxAbsNonZeroT        -> id; _ -> typeError }
  setError = typeError ()
  in
  case e0 of
    VarE          v -> useMaxIf $ S.member v vars
    LiteralE      l -> ($ useIndependentSelf) $ case l of
      BoolL     _ -> withBool
      NumberL   _ -> withNumber
      StringL   _ -> typeError
      DateL     _ -> typeError
    SetE          _ -> setError
    UnaryE op e1  -> case op of
      Not         -> withBool $ fmap notE <$> inverse e1
      Negate      -> withNumber $ recurse e1
      Abs         -> withNumber $ recurse e1
      Iverson     -> case btype of
                       -- IsNonEmpty
                       BoolT _          -> case e1 of
                                             SetE l  -> pure (False, boolE $ not $ null l)
                                             _       -> useMaxIfnonIndependent1 e1
                       MaxAbsNonZeroT   -> withNumber $ fmap iversonE <$> boundAbs vars (BoolT True) e1
    BinaryE (Extra op) _ _ -> case op of
    BinaryE (Base op) e1 e2 ->
      let useMaxIfnonIndependent2 = useMaxIf $ not $ on (&&) (independent vars) e1 e2
          fa' g = useIndependentSelfOr g (recurse e1) $ recurse e2
          fa = fa' . fmap2 pure
      in case op of
      And               -> withBool $ fa andE
      Or                -> withBool $ fa orE
      Sum               -> withNumber $ fa sumE
      -- ! this is not a typo: max(abs(a-b)) <= max(abs(a) + abs(b)) <= max(abs(a)) + max(abs(b)),
      -- but it is not a very useful upper bound if one really wants a difference
      -- to be 0 instead of simply every operand being zero
      Difference        -> withNumber $ fa sumE  
      Product           -> withNumber $ fa prodE
      Quotient          -> withNumber $ bool maxV (fmap (flip quotientE $ absE e2)
                                                   <$> recurse e1)  $ independent vars e2 
      Xor               -> withBool $ fa' $ \b1 b2 -> do
        (_, b1inv) <- inverse e1
        (_, b2inv) <- inverse e2
        pure $ orE (andE b1 $ notE b2inv) $ andE b2 $ notE b1inv

      -- if needed there is a better bound available: e.g. max(0 < abs(a) <= (0 < max(abs(a))
      Less              -> useMaxIfnonIndependent2
      LessEqual         -> useMaxIfnonIndependent2
      Greater           -> useMaxIfnonIndependent2
      GreaterEqual      -> useMaxIfnonIndependent2
      Equal             -> useMaxIfnonIndependent2
      NotEqual          -> useMaxIfnonIndependent2
                                         
      Element           -> useMaxIfnonIndependent2
      NotElement        -> useMaxIfnonIndependent2     
                                         
      Intersection      -> setError
      Union             -> setError
      SetDifference     -> setError

          

data BoundType = BoolT Bool -- ^ get upper bound
               | MaxAbsNonZeroT -- ^ expression has either zero or some non-zero absotule value
                 
  deriving Eq

typeInverse :: (MonadError e f, IsString e) => BoundType -> f BoundType
typeInverse = \case
  BoolT b -> pure $ BoolT $ not b
  MaxAbsNonZeroT -> throwError "currently lower bounds only implemented for Bool"
{-# INLINABLE typeInverse #-}

typeBoundE :: BoundType -> Expr' e
typeBoundE = \case
  BoolT b -> boolE b
  MaxAbsNonZeroT -> numE 1
{-# INLINABLE typeBoundE #-}

typeAbsE :: BoundType -> Expr' a -> Expr' a
typeAbsE = \case
  BoolT _ -> id
  MaxAbsNonZeroT -> absE
{-# INLINABLE typeAbsE #-}
  
typeName :: IsString a => BoundType -> a
typeName = \case
  BoolT _ -> "Bool"
  MaxAbsNonZeroT -> "Number"
{-# INLINABLE typeName #-}



-- | True means the expression depends on the given variables
independent :: S.Set VarName -> Expr' a -> Bool
independent vars = \case
          VarE          v -> S.notMember v vars
          LiteralE      _ -> True
          SetE          l -> all (independent vars) l
          UnaryE _      e -> independent  vars e
          BinaryE _   a b -> on (&&) (independent  vars) a b
{-# INLINABLE independent #-}
