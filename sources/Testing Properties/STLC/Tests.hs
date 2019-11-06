{-# LANGUAGE TemplateHaskell #-}
module Tests where

import Control.Monad
import Test.QuickCheck
import Data.Map
import Data.Maybe
import STLC

--------------------------------------------------------------------------------
--                        RANDOM PROGRAM GENERATION                           --
--------------------------------------------------------------------------------

-- Auxiliary functions to deal with variables

maybeElements :: [a] -> Maybe (Gen a)
maybeElements [] = Nothing
maybeElements xs = Just (elements xs)

pickVar :: Env -> Ty -> Maybe (Gen Expr)
pickVar ctx t = maybeElements [Var x | (x, t') <- Data.Map.assocs ctx, t' == t]

genVar :: Gen Int
genVar = elements [0 .. 1000]

-- Type generation

genType :: Int -> Gen Ty
genType size = frequency ([ (7, return TBool) , (3, liftM2 TLam gt gt)])
  where gt = genType (size `div` 2)

instance Arbitrary Ty where
  arbitrary = sized (\n -> genType n)

-- Expression generation

genExpr :: Int -> Env -> Ty -> Gen Expr
genExpr size ctx TBool
  | size > 0  = oneof ([ return BTrue , return BFalse , gapp ] ++
                       maybeToList (pickVar ctx TBool))
  | otherwise = oneof ([ return BTrue , return BFalse ] ++
                       maybeToList (pickVar ctx TBool))
  where gapp       = do t1 <- genType (size `div` 2)
                        liftM2 App (glam t1 TBool) (gt t1)
        glam t1 t2 = genExpr (size - 2) ctx (TLam t1 t2)
        gt t1      = genExpr (size - 2) ctx t1
genExpr size ctx t@(TLam t1 t2) 
  | size > 0  = oneof ( [ gapp , glam ] ++ maybeToList (pickVar ctx t))
  | otherwise = oneof ( glam : maybeToList (pickVar ctx t))
  where
    gapp = do tl <- genType (size `div` 4)
              e1 <- genExpr (size `div` 2) ctx (TLam tl t)
              e2 <- genExpr (size `div` 2) ctx tl
              return (App e1 e2)
    glam = do v <- genVar
              e <- genExpr (size - 2) (Data.Map.insert v t1 ctx) t2
              return (Lam v t1 e)

instance Arbitrary Expr where
  arbitrary = sized (\n -> genExpr n Data.Map.empty TBool)

--------------------------------------------------------------------------------
--                       PROPERTY BASED TESTING                               --
--------------------------------------------------------------------------------

-- Testing Progress property

prop_progress :: Expr -> Bool
prop_progress e = isVal e || maybe (False) (const True) (step e) 

-- Testing Preservation property

prop_preservation :: Expr -> Bool
prop_preservation e = 
  isVal e || 
  case (typeof Data.Map.empty e) of 
    Just t -> case (step e) of 
                Just e' -> case (typeof Data.Map.empty e') of 
                             Just t' -> t == t'
                             _ -> False 
                _ -> False
    _ -> False

-- Running all tests / properties

return [] 
main = $forAllProperties $
         quickCheckWithResult (stdArgs { maxSuccess = 1000 })

