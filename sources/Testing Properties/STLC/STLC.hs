module STLC where

import Data.Map

-- Type definition

data Ty = TBool
        | TLam Ty Ty
        deriving (Show, Eq)

-- Syntax definition

data Expr = BTrue 
          | BFalse
          | Var Int
          | Lam Int Ty Expr
          | App Expr Expr
          deriving (Show)

-- Value definition

data Val = VTrue
         | VFalse
         | VLam Int Ty Expr

-- Value verification

isVal :: Expr -> Bool
isVal BTrue = True
isVal BFalse = True
isVal (Lam _ _ _) = True
isVal _ = False

-- Substitution

subs :: Int -> Expr -> Expr -> Maybe Expr
subs x s BTrue = Just BTrue
subs x s BFalse = Just BFalse
subs x s (Var y)
    | x == y    = Just s
    | otherwise = Just (Var y)
subs x s (Lam y t e) = do e' <- subs x s e
                          return (Lam y t e')
subs x s (App e1 e2) = do e1' <- subs x s e1 
                          e2' <- subs x s e2
                          return (App e1' e2')

-- Small-step interpreter

step :: Expr -> Maybe Expr
step (App (Lam x t e1) e2)
    | isVal e2   = subs x e2 e1
    | otherwise  = do e2' <- step e2
                      return (App (Lam x t e1) e2')
step (App e1 e2) = do e1' <- step e1
                      return (App e1' e2)

-- Environment

type Env = Map Int Ty

-- Typing

typeof :: Env -> Expr -> Maybe Ty
typeof ctx BTrue = Just TBool
typeof ctx BFalse = Just TBool
typeof ctx (Var x) = Data.Map.lookup x ctx
typeof ctx (Lam x t e) = do t1 <- typeof (Data.Map.insert x t ctx) e
                            return (TLam t t1)
typeof ctx (App e1 e2) = do (TLam t1 t2) <- typeof ctx e1
                            t1' <- typeof ctx e2
                            if (t1 == t1') then
                              return t2
                            else
                              Nothing

