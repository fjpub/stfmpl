-- Utilitary functions for FJ + Lambda interpreter
-- Author: Samuel da Silva Feitosa
-- Date: 03/2018
--------------------------------------------------
module FJUtils where
import FJParser
import Data.Map
import Data.List

-- Function: subtyping
-- Objective: Check classes for subtyping.
-- Params: Class table, Class A, Class B.
-- Returns: Returns if class A is subtype of class B.
-----------------------------------------------------
subtyping :: CT -> String -> String -> Bool
subtyping ct t t' 
  | t == t' = True
  | otherwise = 
      case (Data.Map.lookup t ct) of
        Just (TClass (Class _ t'' il _ _ _)) ->
          if (t' == t'' || Data.List.elem t' il) then
            True
          else 
            subtyping ct t'' t' || 
            Data.List.any (\t'' -> subtyping ct t'' t') il
        Just (TInterface (Interface _ il _ _)) ->
          Data.List.elem t' il || 
          Data.List.any (\t'' -> subtyping ct t'' t') il
        _ -> False
                 
-- Function: fields
-- Objective: Search for a class on class table and returns its fields.
-- Params: Class table, Class name.
-- Returns: A monad Maybe containing the field list or Nothing.
-----------------------------------------------------------------------
fields :: CT -> String -> Maybe [(Type,String)]
fields _ "Object" = Just []
fields ct c = case (Data.Map.lookup c ct) of 
                Just (TClass (Class _ c'' _ attrs _ _)) ->
                  case (fields ct c'') of 
                    Just base -> Just (base ++ attrs)
                    _ -> Nothing
                _ -> Nothing


-- Function: absmethods
-- Objective: Search for a class or interface on class table and returns its
-- abstract methods.
-- Params: Class table, Class name.
-- Returns: A monad Maybe containing the method signature or Nothin.
----------------------------------------------------------------------------
absmethods :: CT -> String -> Maybe [Sign]
absmethods _ "Object" = Just []
absmethods ct t = 
  case (Data.Map.lookup t ct) of
    Just (TClass (Class _ t' il _ _ _)) -> 
      case (absmethods ct t') of
        Just bam -> 
          let bam' = Data.List.concatMap (\i -> case (absmethods ct i) of
                                                  Just am -> am
                                                  _ -> []
                                         ) il
              bam'' = unionBy (\(Sign _ n' _) 
                                (Sign _ n'' _) -> n' == n'') bam bam'
              cam = case (methods ct t) of
                      Just meths -> 
                        case (methods ct t') of
                          Just bmeths -> 
                            unionBy (\(Sign _ n' _) 
                                      (Sign _ n'' _) -> n' == n'')
                              (Data.List.map (\(Method s e) -> s) meths)
                              (Data.List.map (\(Method s e) -> s) bmeths)
                          _ -> Data.List.map (\(Method s e) -> s) meths
                      _ -> []
            in Just (bam'' Data.List.\\ cam)
        _ -> Nothing
    Just (TInterface (Interface _ il ameths _)) -> 
      let bam = Data.List.concatMap (\i -> case (absmethods ct i) of
                                             Just am -> am
                                             _ -> []
                                    ) il
          ameths' = unionBy (\(Sign _ n' _) 
                              (Sign _ n'' _) -> n' == n'') ameths bam
        in Just (ameths')
    _ -> Nothing


-- Function: methods
-- Objective: Search for a class on class table and returns its methods.
-- Params: Class table, Class name.
-- Returns: A monad Maybe containing the method list of Nothing.
------------------------------------------------------------------------
methods :: CT -> String -> Maybe [Method]
methods _ "Object" = Just []
methods ct t = 
  case (Data.Map.lookup t ct) of 
    Just (TClass (Class _ cb il _ _ meths)) ->
      case (methods ct cb) of
        Just bms -> 
          let bim = Data.List.concatMap (\i -> case (methods ct i) of
                                                 Just m -> m
                                                 _ -> []
                                        ) il
              m' = unionBy (\(Method (Sign _ n' _) _)
                             (Method (Sign _ n'' _) _) -> n' == n'') meths bms
              m'' = unionBy (\(Method (Sign _ n' _) _)
                              (Method (Sign _ n'' _) _) -> n' == n'') m' bim
            in Just m''
        _ -> Nothing
    Just (TInterface (Interface _ il _ defmeths)) -> 
      let bim = Data.List.concatMap (\i -> case (methods ct i) of 
                                             Just m -> m
                                             _ -> []
                                    ) il
          m' = unionBy (\(Method (Sign _ n' _) _)
                         (Method (Sign _ n'' _) _) -> n' == n'') defmeths bim
        in Just m'
    _ -> Nothing


-- Function: mtype
-- Objective: Search for a class on class table, then looks up for a method 
-- and returns its type.
-- Params: Class table, Method name, Class name.
-- Returns: A monad Maybe containing the method type.
---------------------------------------------------------------------------
mtype :: CT -> String -> String -> Maybe ([Type], Type)
mtype _ _ "Object" = Nothing
mtype ct m t = 
  case (absmethods ct t) of 
    Just absmeths -> 
      case (Data.List.find (\(Sign _ m' _) -> m == m') absmeths) of
        Just (Sign r _ p) -> Just (fst (unzip p), r)
        _ -> case (methods ct t) of 
               Just meths -> 
                 case (Data.List.find 
                         (\(Method (Sign _ m' _) _) -> m == m') meths) of
                   Just (Method (Sign r _ p) _) -> Just (fst (unzip p), r)
                   _ -> Nothing
               _ -> Nothing
    _ -> Nothing

-- Function: mbody
-- Objective: Search for a class on class table, then looks up for a method
-- and returns its body.
-- Params: Class table, Method name, Class name.
-- Returns: A monad Maybe containing the method body or Nothing.
---------------------------------------------------------------------------
mbody :: CT -> String -> String -> Maybe ([String], Expr)
mbody _ _ "Object" = Nothing
mbody ct m t =
  case (methods ct t) of 
    Just meths -> case (Data.List.find (\(Method (Sign _ m' _) _) 
                          -> m == m') meths) of
      Just (Method (Sign _ _ p) e) -> Just (snd (unzip p), e)
      _ -> Nothing
    _ -> Nothing
 
-- Function: isValue 
-- Objective: Check if an expression represents a value.
-- Params: Class table, Expression.
-- Returns: Boolean indicating if an expression is a value.
-----------------------------------------------------------
isValue :: CT -> Expr -> Bool
isValue _ (CreateObject c []) = True
isValue ct (CreateObject c p) = Data.List.all (isValue ct) p
isValue ct (Closure _ _) = True
isValue ct (Cast _ (Closure _ _)) = True
isValue _ _ = False

-- Function: lambdaMark
-- Objective: Annotate the types for lambda expressions.
-- Params: Expression, Type.
-- Returns: A lambda expression annotated with its type, or the expression if
-- it is not a lambda expression.
-----------------------------------------------------------------------------
lambdaMark :: Expr -> Type -> Expr
lambdaMark c@(Closure _ _) (Type t) = Cast t c
lambdaMark e _ = e


-- Function: removeRuntimeAnnotation
-- Objective: Remove runtime annotations in lambda expressions.
-- Params: Expression.
-- Returns: An expression without the runtime type annotations.
---------------------------------------------------------------
removeRuntimeAnnotation :: Expr -> Expr
removeRuntimeAnnotation (FieldAccess e f) = 
  let e' = removeRuntimeAnnotation e
    in FieldAccess e' f
removeRuntimeAnnotation (MethodInvk e m p) = 
  let e' = removeRuntimeAnnotation e
      p' = Data.List.map removeRuntimeAnnotation p
    in MethodInvk e' m p'
removeRuntimeAnnotation (CreateObject c p) = 
  let p' = Data.List.map removeRuntimeAnnotation p
    in CreateObject c p'                              
removeRuntimeAnnotation (Closure p e) = 
  let e' = removeRuntimeAnnotation e
    in Closure p e'
removeRuntimeAnnotation (Cast t e) = removeRuntimeAnnotation e
removeRuntimeAnnotation e = e

