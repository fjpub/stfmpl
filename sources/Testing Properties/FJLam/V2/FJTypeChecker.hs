-- Haskell type checker for FJ + Lambda
-- Author: Samuel da Silva Feitosa
-- Date: 03/2018
---------------------------------------
module V2.FJTypeChecker where
import FJParser
import FJUtils
import Data.Map
import Data.List

-- Function: throwError
-- Objective: Launching a type error.
-- Params: Expected type, Found type, Expression presenting the error.
-- Returns: A type error structure.
----------------------------------------------------------------------
throwError :: TypeError -> Either TypeError Type
throwError e = Left e

-- Function: typeof
-- Objective: Check the type of a given expression.
-- Params: Type context, Class table, Expression.
-- Returns: The type of a given term or a type error.
-----------------------------------------------------
typeof :: CT -> Env -> Expr -> Either TypeError Type
typeof ct ctx (Var v) = -- T-Var
  case (Data.Map.lookup v ctx) of 
    Just t -> return t
    _ -> throwError (VariableNotFound v) 
typeof ct ctx (FieldAccess e f) = -- T-Field
  case (typeof ct ctx e) of
    Right (Type c) ->
      case (fields ct c) of 
        Just flds ->
          case (Data.List.find (\(tp,nm) -> f == nm) flds) of
            Just (tp,nm) -> return tp
            _ -> throwError (FieldNotFound f)
        _ -> throwError (ClassNotFound c)
    e -> e -- Error: Expression type not found
typeof ct ctx (MethodInvk e m p) = -- T-Invk
  case (typeof ct ctx e) of
    Right (Type t) -> 
      case (mtype ct m t) of 
        Just (pt, rt) ->
          if (length p == length pt) then
            let tmp = Data.List.zipWith (\e' t' -> (lambdaMark e' t', t')) p pt
              in if (Data.List.all (\(e', Type t') -> 
                       case (typeof ct ctx e') of
                         Right (Type tp') -> subtyping ct tp' t'
                         _ -> False
                    ) tmp) then
                   return rt
                 else
                   throwError (ParamsTypeMismatch tmp) 
          else 
            throwError (ParamsTypeMismatch [])
        _ -> throwError (MethodNotFound m t)
    e -> e -- Error: Expression type not found
typeof ct ctx (CreateObject c p) = -- T-New
  case (fields ct c) of 
    Just flds ->
      if (length p == length flds) then 
        let tmp = Data.List.zipWith (\e (tp,_) -> (lambdaMark e tp,tp)) p flds 
          in if (Data.List.all (\(e,Type t) -> 
                   case (typeof ct ctx e) of 
                     Right (Type tp') -> subtyping ct tp' t
                     _ -> False
                 ) tmp) then
                return (Type c)
              else 
                throwError (ParamsTypeMismatch tmp)
      else 
        throwError (ParamsTypeMismatch [])
    _ -> throwError (ClassNotFound c)
typeof ct ctx (Cast i cl@(Closure cp e)) = -- T-Lam
  let cp' = Data.List.map (\(tp,nm) -> (nm,tp)) cp
      ctx' = Data.Map.union (Data.Map.fromList cp') ctx in
    case (absmethods ct i) of
      Just [(Sign (Type r) mn mp)] -> 
        case (typeof ct ctx' (lambdaMark e (Type r))) of
          Right (Type t) -> if (subtyping ct t r) && 
                                    (fst (unzip mp) == fst (unzip cp)) then
                                   return (Type i)
                                 else
                                   throwError (WrongClosure i cl)
          e -> e -- Error: Expression type not found
      _ -> throwError (WrongClosure i cl)
typeof ct ctx (Cast t e) = 
  let e' = lambdaMark e (Type t)
    in case (typeof ct ctx e') of 
         Right (Type tp)  
           | (subtyping ct tp t) -> return (Type t) -- T-UCast
           | (subtyping ct t tp) && (t /= tp) -> return (Type t) -- T-DCast
           | (not (subtyping ct t tp)) && (not (subtyping ct tp t)) -> 
               return (Type t) -- T-SCast
           | otherwise -> throwError (WrongCast t e)
         e -> e  -- Error: Expression type not found
typeof _ _ c@(Closure cp e) = -- Error: Lambda expression without a type
  throwError (WrongClosure "None" c)

-- Function: methodTyping
-- Objective: Check if a method is well formed.
-- Params: Class table, Type context, Class name, Method.
-- Returns: True for a well formed method, False otherwise.
-----------------------------------------------------------
methodTyping :: CT -> Env -> String -> Method -> Bool
methodTyping ct ctx t m@(Method (Sign r@(Type rt) mn mp) e) = 
  let e' = lambdaMark e r
      mp' = Data.List.map (\(tp,pn) -> (pn,tp)) mp
      ctx' = Data.Map.union (Data.Map.fromList mp') ctx
      ctx'' = Data.Map.insert "this" (Type t) ctx' 
    in case (typeof ct ctx'' e') of
         Right (Type tp) -> 
           case (methods ct t) of
             Just meths -> subtyping ct tp rt &&
                           Data.List.elem m meths
             _ -> False -- Error obtaining methods
         _ -> False -- Error obtaining type of expression

-- Function: classTyping
-- Objective: Check if a class is well-formed.
-- Params: Class, Type context, Class table.
-- Returns: True for a well-formed class, False otherwise.
----------------------------------------------------------
classTyping :: CT -> Env -> Class -> Bool
classTyping ct ctx cl@(Class c b _ attrs (Constr _ pc s ths) meths) = 
  case (fields ct b) of 
    Just flds -> 
      if (pc == (flds ++ attrs)) then
        if (Data.List.all (\(n',n'') -> n' == n'') ths) then
          let p' = Data.List.map (\(tp, nm) -> nm) pc 
              p'' = s ++ (Data.List.map (\(n',n'') -> n') ths) 
            in case (absmethods ct c) of
                 Just ameths -> Data.List.null ameths &&
                   (p' == p'') && (Data.List.all (methodTyping ct ctx c) meths)
                 _ -> False -- Error obtaining abstract methods
        else 
          False
      else 
         False
    _ -> False

-- Function: interfaceTyping
-- Objective: Check if an interface is well-formed.
-- Params: Class table, Type context, Interface.
-- Returns: True for a well-formed interface, False otherwise.
--------------------------------------------------------------
interfaceTyping :: CT -> Env -> Interface -> Bool
interfaceTyping ct ctx int@(Interface i il abs def) =
  (not (Data.List.null (absmethods ct i))) && 
  (Data.List.all (methodTyping ct ctx i) def)
