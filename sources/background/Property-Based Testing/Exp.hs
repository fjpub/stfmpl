module Exp where

-- Syntax definition

data Expr = BTrue 
          | BFalse
          | Num Int
          | Add Expr Expr
          | And Expr Expr
          deriving (Show)
--          deriving (Show, Eq)

-- Value definition

data Val = VTrue
         | VFalse
         | VNum Int
--         deriving (Show, Eq)

isVal :: Expr -> Bool
isVal BTrue = True
isVal BFalse = True
isVal (Num _) = True
isVal _ = False

-- Type definition

data Ty = TBool
        | TNum
        deriving (Eq)
--        deriving (Show, Eq)

-- Small-step interpreter

step :: Expr -> Maybe Expr
step (Add (Num n1) (Num n2)) = Just (Num (n1 + n2))
step (Add (Num n1) e2) = do e2' <- step e2
                            return (Add (Num n1) e2')
step (Add e1 e2) = do e1' <- step e1
                      return (Add e1 e2) 
step (And BTrue e2) = Just e2
step (And BFalse e2) = Just BFalse
step (And e1 e2) = do e1' <- step e1
                      return (And e1' e2)

-- Big-step interpreter

{-
bigstep :: Expr -> Maybe Val
bigstep (BTrue) = Just VTrue
bigstep (BFalse) = Just VFalse
bigstep (Num n) = Just (VNum n)
bigstep (Add e1 e2) = 
  do (VNum nv1) <- bigstep e1
     (VNum nv2) <- bigstep e2
     Just (VNum (nv1 + nv2))
bigstep (And e1 e2) =
  case (bigstep e1) of
    Just VTrue -> bigstep e2
    Just VFalse -> Just VFalse
    _ -> Nothing
-}

-- Typing

typeof :: Expr -> Maybe Ty
typeof BTrue = Just TBool
typeof BFalse = Just TBool
typeof (Num _) = Just TNum
typeof (Add e1 e2) = do TNum <- typeof e1
                        TNum <- typeof e2
                        return TNum
typeof (And e1 e2) = do TBool <- typeof e1
                        TBool <- typeof e2
                        return TBool
