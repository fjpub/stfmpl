{-# LANGUAGE TemplateHaskell #-}
module Tests where

import Control.Monad
import Test.QuickCheck
import Exp

genType :: Gen Ty
genType = elements [TBool, TNum]

genNat :: Gen Int
genNat = elements [0 .. 1000]

genExpr :: Int -> Ty -> Gen Expr
genExpr size TBool 
  | size > 0  = oneof ([ return BTrue, return BFalse, liftM2 And gt gt ])
  | otherwise = oneof ([ return BTrue, return BFalse ])
  where gt = genExpr (size - 2) TBool --genExpr (size `div` 2) TBool
genExpr size TNum
  | size > 0  = oneof ([ liftM Num n, liftM2 Add gt gt ])
  | otherwise = oneof ([ liftM Num n ])
  where n  = genNat
        gt = genExpr (size - 2) TNum -- genExpr (size `div` 2) TNum

instance Arbitrary Expr where
  arbitrary = do
    t <- genType
    sized (\n -> genExpr n t)

prop_progress :: Expr -> Bool
prop_progress e = isVal e || maybe (False) (const True) (step e) 

prop_preservation :: Expr -> Bool
prop_preservation e = 
  isVal e || 
  case (typeof e) of 
    Just t -> case (step e) of 
                Just e' -> case (typeof e') of 
                             Just t' -> t == t'
                             _ -> False 
                _ -> False
    _ -> False

return [] 
main = $forAllProperties $
         quickCheckWithResult (stdArgs { maxSuccess = 1000 })

