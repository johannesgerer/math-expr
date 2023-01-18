
module MathExpr.Tests where

import qualified Data.Map as M
import           MathExpr
import           Test.Hspec
import           Yahp


main :: IO ()
main = hspec $ do
  describe "maxBool" $
    let cmp i (input,res) = it ("should satisfy case A." <> show i) $
          either id shot (maxBool (fromList vars) =<< parseAndDesugarExpr input)
          `shouldBe` either id shot (parseAndDesugarExpr res)
        vars = ["x1","x2","x3","x4"]
    in zipWithM_ cmp [(1::Int)..] $ 
       [("x1"                   , "True")
       ,("x1 & True"            , "True & True")
       ,("~(x1 & True)"         , "~(False & True)")
       ,("[{}]"                 , "False")
       ,("[{2,3}]"              , "True")
       ,("[{} cap a]"           , "[{} cap a]")
       ,("[{} cap x1]"          , "True")
       ,("0 < 1 - x1"           , "True")
       ,("0 < -1"               , "0 < -1")
       ,("a & ~(c & x1)"        , "a & ~(c & False)")
       ,("False ^ x1"           , "(False & (~False)) | (True & (~False))")
       ,("x2 ^ x1"              , "(True & (~False)) | (True & (~False))")
       ,("a ^ b"                , "a ^ b")
       ,("a ∈ x1"               , "True")
       ]

  describe "maxAbs" $
    let cmp i (input,res) = it ("should satisfy case B." <> show i) $
          either id shot (maxAbs (fromList vars) =<<
                          parseAndDesugarExpr input) `shouldBe`
          either id shot (parseAndDesugarExpr res)
        vars = ["x1","x2","x3","x4"]
    in zipWithM_ cmp [(1::Int)..] $ 
       [("x1"                   , "1")
       ,("-x1"                  , "1")
       ,("1/x1"                 , "1")
       ,("1/(1+2)"              , "abs(1)/abs(1+2)")
       ,("-a"                   , "Abs(a)")
       ,("[x1]"                 , "[True]")
       ,("[~x1]"                , "[~False]")
       ,("a + [x1]"             , "abs(a) + [True]")
       ,("a - [x1]"             , "abs(a) + [True]")
       ,("x4 * b"             , "Abs(b)")
       ]


  describe "maxAbs" $
    let cmp i (input,res) = it ("should satisfy case C." <> show i) $
          ev (maxAbs (fromList vars) =<< parseAndDesugarExpr input) `shouldBe` res
        ev x = eitherException (fromScalarValue I =<< eval @I v2 =<< x)
        vars = ["x1","x2","x3","x4"]
        v2 = flip lookupThrow $ M.fromList [("zero", dynV $ I @Double 0), ("one", dynV $ I @Double 1), ("Zero", zeroV), ("One", oneV)]
    in zipWithM_ cmp [(1::Int)..] $ 
       [("x1 + One"                   , I @Double $ 2)
       ,("x1 * One"                   , I 1)
       ,("x1 * Zero"                   , I @Double 0)
       ,("x1 * zero"                   , I @Double 0)
       ]

  describe "eval" $
    let cmp i (input,res) = it ("should satisfy case D." <> show i) $
          ev (parseAndDesugarExpr input) `shouldBe` res
        ev x = eitherException (eval @I v2 =<< x)
        v2 = flip lookupThrow $ M.fromList [("zero", dynV $ I @Double 0), ("one", dynV $ I @Double 1), ("Zero", zeroV), ("One", oneV)]
    in zipWithM_ cmp [(1::Int)..] $ 
       [("zero in {0}"          , dynV $ I True)
       ,("zero in {0} \\ {0}"   , dynV $ I False)
       ,("one in {1} \\ {0}"    , dynV $ I True)
       ]

devmain = main
