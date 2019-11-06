-- Haskell type checker for FJ + Lambda
-- Author: Samuel da Silva Feitosa
-- Date: 03/2018
---------------------------------------
module V1.FJTypeChecker where
import FJParser
import FJUtils
import Data.Map
import Data.List

-- Function: throwError
-- Objective: Launching a type error.
-- Params: Expected type, Found type, Expression presenting the error.
-- Returns: A type error structure.
----------------------------------------------------------------------
throwError :: TypeError -> Either TypeError (Type, Expr)
throwError e = Left e

-- Function: typeof
-- Objective: Check the type of a given expression.
-- Params: Type context, Class table, Expression.
-- Returns: The type of a given term or a type error.
-----------------------------------------------------
typeof :: CT -> Env -> Expr -> Either TypeError (Type, Expr)
typeof ct ctx exp@(Var v) = -- T-Var
  case (Data.Map.lookup v ctx) of 
    Just t -> return (t, exp)
    _ -> throwError (VariableNotFound v) 
typeof ct ctx exp@(FieldAccess e f) = -- T-Field
  case (typeof ct ctx e) of
    Right (Type c, e') ->
      case (fields ct c) of 
        Just flds ->
          case (Data.List.find (\(tp,nm) -> f == nm) flds) of
            Just (tp,nm) -> return (tp, FieldAccess e' f) 
            _ -> throwError (FieldNotFound f)
        _ -> throwError (ClassNotFound c)
    e -> e -- Error: Expression type not found
typeof ct ctx exp@(MethodInvk e m p) = -- T-Invk
  case (typeof ct ctx e) of
    Right (Type t, e') -> 
      case (mtype ct m t) of 
        Just (pt, rt) ->
          if (length p == length pt) then
            let tmp = Data.List.zipWith (\e'' t' -> 
                                           (lambdaMark e'' t', t')) p pt
                p' = Data.List.map (\(e'', Type t') -> 
                       case (typeof ct ctx e'') of
                         Right (Type tp', e''') -> (subtyping ct tp' t', e''')
                         _ -> (False, e)
                     ) tmp
              in if (Data.List.and (fst (unzip p'))) then
                   return (rt, MethodInvk e' m (snd (unzip p')))
                 else
                   throwError (ParamsTypeMismatch tmp) 
          else 
            throwError (ParamsTypeMismatch [])
        _ -> throwError (MethodNotFound m t)
    e -> e -- Error: Expression type not found
typeof ct ctx exp@(CreateObject c p) = -- T-New
  case (fields ct c) of 
    Just flds ->
      if (length p == length flds) then 
        let tmp = Data.List.zipWith (\e (tp,_) -> (lambdaMark e tp,tp)) p flds
            p' = Data.List.map (\(e, Type t) -> 
                   case (typeof ct ctx e) of 
                     Right (Type tp', e') -> (subtyping ct tp' t, e')
                     _ -> (False, e)
                 ) tmp
          in if (Data.List.and (fst (unzip p'))) then
               return (Type c, CreateObject c (snd (unzip p')))
             else 
               throwError (ParamsTypeMismatch tmp)
      else 
        throwError (ParamsTypeMismatch [])
    _ -> throwError (ClassNotFound c)
typeof ct ctx exp@(Cast i cl@(Closure cp e)) = -- T-Lam
  let cp' = Data.List.map (\(tp,nm) -> (nm,tp)) cp
      ctx' = Data.Map.union (Data.Map.fromList cp') ctx in
    case (absmethods ct i) of
      Just [(Sign (Type r) mn mp)] -> 
        let e' = lambdaMark e (Type r) in
          case (typeof ct ctx' e') of
            Right (Type t, e'') -> if (subtyping ct t r) && 
                                      (fst (unzip mp) == fst (unzip cp)) then
                                     return (Type i, Cast i (Closure cp e''))
                                   else
                                     throwError (WrongClosure i cl)
            e -> e -- Error: Expression type not found
      _ -> throwError (WrongClosure i cl)
typeof ct ctx (Cast t e) = 
  let e' = lambdaMark e (Type t)
    in case (typeof ct ctx e') of 
         Right (Type tp, e'')  
           | (subtyping ct tp t) -> return (Type t, e'') -- T-UCast
           | (subtyping ct t tp) && (t /= tp) -> return (Type t, e'') -- T-DCast
           | (not (subtyping ct t tp)) && (not (subtyping ct tp t)) -> 
               return (Type t, e'') -- T-SCast
           | otherwise -> throwError (WrongCast t e'')
         e -> e  -- Error: Expression type not found
typeof _ _ c@(Closure cp e) = -- Error: Lambda expression without a type
  throwError (WrongClosure "None" c)

-- Function: methodTyping
-- Objective: Check if a method is well formed.
-- Params: Class table, Type context, Class name, Method.
-- Returns: True for a well formed method, False otherwise.
-----------------------------------------------------------
methodTyping :: CT -> Env -> String -> Method -> (Bool, Method)
methodTyping ct ctx t m@(Method s@(Sign r@(Type rt) mn mp) e) = 
  let e' = lambdaMark e r
      mp' = Data.List.map (\(tp,pn) -> (pn,tp)) mp
      ctx' = Data.Map.union (Data.Map.fromList mp') ctx
      ctx'' = Data.Map.insert "this" (Type t) ctx' 
    in case (typeof ct ctx'' e') of
         Right (Type tp, e'') -> 
           case (methods ct t) of
             Just meths -> (subtyping ct tp rt &&
                           Data.List.elem m meths, Method s e'')
             _ -> (False, Method s e'') -- Error obtaining methods
         _ -> (False, Method s e') -- Error obtaining type of expression

-- Function: classTyping
-- Objective: Check if a class is well-formed.
-- Params: Class, Type context, Class table.
-- Returns: True for a well-formed class, False otherwise.
----------------------------------------------------------
classTyping :: CT -> Env -> Class -> (Bool, Class)
classTyping ct ctx cl@(Class c b il attrs con@(Constr _ pc s ths) meths) = 
  case (fields ct b) of 
    Just flds -> 
      if (pc == (flds ++ attrs)) then
        if (Data.List.all (\(n',n'') -> n' == n'') ths) then
          let p' = Data.List.map (\(tp, nm) -> nm) pc 
              p'' = s ++ (Data.List.map (\(n',n'') -> n') ths) 
            in case (absmethods ct c) of
                 Just ameths -> let tmp = Data.List.map (methodTyping ct ctx c) meths
                                  in (Data.List.null ameths && (p' == p'') &&
                                      Data.List.and (fst (unzip tmp)), 
                                      Class c b il attrs con (snd (unzip tmp)))
                 _ -> (False, cl) -- Error obtaining abstract methods
        else 
          (False, cl)
      else 
         (False, cl)
    _ -> (False, cl)

-- Function: interfaceTyping
-- Objective: Check if an interface is well-formed.
-- Params: Class table, Type context, Interface.
-- Returns: True for a well-formed interface, False otherwise.
--------------------------------------------------------------
interfaceTyping :: CT -> Env -> Interface -> (Bool, Interface)
interfaceTyping ct ctx int@(Interface i il abs def) =
  if (not (Data.List.null (absmethods ct i))) then
    let tmp = Data.List.map (methodTyping ct ctx i) def
      in (Data.List.and (fst (unzip tmp)), Interface i il abs (snd (unzip tmp)))
  else (False, int)


-- Function: ctTyping
-- Objective: Check if all classes in class table are well-formed.
-- Params: Class table, type context.
-- Returns: A class table with annotated types for lambda expressions.
----------------------------------------------------------------------
ctTyping :: CT -> Env -> CT
ctTyping ct ctx = 
  Data.Map.mapWithKey (\tn t -> 
    case t of
      TClass c -> case (classTyping ct ctx c) of
                    (r, c') -> if r then 
                                 TClass c'
                               else 
                                 error ("Error typing class " ++ tn)
      TInterface i -> case (interfaceTyping ct ctx i) of
                        (r, i') -> if r then
                                     TInterface i'
                                   else 
                                     error ("Error typing interface " ++ tn)
  ) ct
