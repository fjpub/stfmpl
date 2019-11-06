-- Random generators for FJ + Lambda
-- Author: Samuel da Silva Feitosa
-- Date: 04/2018
------------------------------------
module FJGenerator where
import FJParser
import FJUtils
import Test.QuickCheck
import Data.Map
import Data.List
import Data.Maybe
import Control.Monad

-- Function: maybeElements
-- Objective: Get one element of a given list.
-- Params: List of a generic value.
-- Returns: A monad maybe containing the element or Nothing.
------------------------------------------------------------
maybeElements :: [a] -> Maybe (Gen a)
maybeElements [] = Nothing
maybeElements xs = Just (elements xs)

-- Function: pickVar
-- Objective: Pick a variable of a given type from context.
-- Params: Context, Class name.
-- Returns: A variable of a given type.
-----------------------------------------------------------
pickVar :: Env -> Type -> Maybe (Gen Expr)
pickVar ctx t = maybeElements [Var x | (x, t') <- Data.Map.assocs ctx, t' == t]

-- Function: genClassName
-- Objective: Generate a random class name.
-- Params: None.
-- Returns: A string containing a valid class name.
--------------------------------------------------
genClassName :: Gen String
genClassName = do n <- elements ['A' .. 'Z']
                  return [n]

-- Function: genInstantiableType
-- Objective: Generate an instantiable type from the class table.
-- Params: Class table.
-- Returns: A string containing a class name.
-----------------------------------------------------------------
genInstantiableType :: CT -> Gen String
genInstantiableType ct = elements ("Object" : keys ct')
  where ct' = (Data.Map.filter
                (\t -> case t of 
                         (TClass _) -> True
                         (TInterface (Interface t' _ _ _)) -> 
                           case (absmethods ct t') of
                             Just [(Sign _ _ _)] -> True
                             _ -> False
              ) ct)

-- Function: genClassType
-- Objective: Generate a class name from the class table.
-- Params: Class table.
-- Returns: A string containing a class name.
---------------------------------------------------------
genClassType :: CT -> Gen String
genClassType ct = elements ("Object" : keys (Data.Map.filter
                                              (\t -> case t of 
                                                       (TClass _) -> True
                                                       _ -> False
                                              ) ct))


-- Function: genInterfaceTypeList
-- Objective: Generate a list of interface names from the class table.
-- Params: Class table.
-- Returns: A list of strings containing interface names.
----------------------------------------------------------------------
genInterfaceTypeList :: CT -> Gen [String]
genInterfaceTypeList ct = 
  sublistOf (keys (Data.Map.filter 
                    (\t -> case t of 
                             (TInterface _) -> True
                             _ -> False
                    ) ct))

-- Function: genVar
-- Objective: Generate a random variable name.
-- Params: None
-- Returns: A string containing a valid variable name.
-----------------------------------------------------
genVar :: Gen String
genVar = do n <- elements ['a' .. 'z']
            return [n]

-- Function: genAttrs
-- Objective: Generate a list of type/attributes for a given class.
-- Params: Class table, class name, base class.
-- Returns: A list of type/attributes.
-------------------------------------------------------------------
genAttrs :: CT -> String -> String -> Gen [(String,String)]
genAttrs ct c b = 
  do n <- choose (0,5)
     tl <- vectorOf n (genInstantiableType ct)
     vl <- (vectorOf n (genVar))
     tl' <- Control.Monad.mapM (\n -> if (subtyping ct n c) then 
                                        return "Object"
                                      else 
                                        return n
                                ) tl
     case (fields ct b) of 
       Just bflds -> return (zip tl' 
                       ((nub vl) Data.List.\\ (snd (unzip bflds))))
       _ -> return (zip tl' (nub vl))

-- Function: genMethod
-- Objective: Generate a random method for a given class.
-- Params: Class table, class name, Use of this.
-- Returns: A generated method.
---------------------------------------------------------
genMethod :: CT -> String -> Bool -> Gen Method
genMethod ct c ths = 
  do n <- choose (0,3) -- Number of params
     tl <- vectorOf n (genInstantiableType ct) -- Type of params
     vl <- vectorOf n (genVar) -- Name of params
     m <- genVar -- Method name
     r <- genInstantiableType ct -- Return type 
     e <- genExpression False ct (ctx vl tl) r -- Body expression
     return (Method (Sign 
               (Type r) 
               ('m':m ++ c)  
               (zip (Data.List.map (\t -> Type t) tl) (nub vl)))
               e
            )
  where ctx vl' tl' = let ctx' = zip (nub vl') 
                                     (Data.List.map (\t -> Type t) tl')
                        in if (ths) then
                             fromList (("this", Type c) : ctx')
                           else
                             fromList ctx'

-- Function: genSign
-- Objective: Generate a random signature for a given interface.
-- Params: Class table, interface name.
-- Returns: A generated signature.
----------------------------------------------------------------
genSign :: CT -> String -> Gen Sign
genSign ct i = 
  do n <- choose (0,2) -- Number of params
     tl <- vectorOf n (genInstantiableType ct) -- Type of params
     vl <- vectorOf n (genVar) -- Name of params
     m <- genVar -- Method name
     r <- genInstantiableType ct -- Return type
     return (Sign (Type r) 
                  ('s':m ++ i) 
                  (zip (Data.List.map (\t -> Type t) tl) 
                       (Data.List.map (\n -> 'c':n) (nub vl))
                  )
            )

-- Function: genMethods
-- Objective: Generate a list of random methods.
-- Params: Class table, class name, base class, use of this.
-- Returns: A list of methods.
-- @TODO: Generate polymorphic methods
------------------------------------------------------------
genMethods :: CT -> String -> [String] -> Bool -> Gen [Method]
genMethods ct t bl ths = 
 do n <- choose (0,3) -- Number of methods
    ml <- vectorOf n (genMethod ct t ths) 
    return (deleteFirstsBy (\(Method (Sign _ n' _) _) 
             (Method (Sign _ n'' _) _) -> n' == n'') 
             (nubBy (\(Method (Sign _ n' _) _) 
             (Method (Sign _ n'' _) _) -> n' == n'') ml)
            bml)
  where bml = Data.List.concatMap 
                (\t' -> case (methods ct t') of 
                          Just meths -> meths
                          _ -> []
                ) bl

-- Function: genSigns
-- Objective: Generate a list of random signatures.
-- Params: Class table, interface name, base interface list.
-- Returns: A list of signatures.
------------------------------------------------------------
genSigns :: CT -> String -> [String] -> Gen [Sign]
genSigns ct i il = 
  do n <- choose (0,2) -- Number of signatures
     sl <- vectorOf n (genSign ct i)
     return (deleteFirstsBy 
              (\(Sign _ n' _) (Sign _ n'' _) -> n' == n'')
              (nubBy (\(Sign _ n' _) (Sign _ n'' _) -> n' == n'') sl)
             bil)
  where bil = Data.List.concatMap
                (\i' -> case (absmethods ct i') of
                          Just absm -> absm
                          _ -> []
                ) il

-- Function: formatConstr
-- Objective: Format a class constructor.
-- Params: Class table, class name, base class, class attributes.
-- Returns: A constructor AST for the given class. 
-----------------------------------------------------------------
formatConstr :: CT -> String -> String -> [(Type,String)] -> Constr
formatConstr ct c b attrs = 
  case (fields ct b) of 
    Just flds -> Constr c -- Class name
                        (flds ++ attrs) -- Constr parameters
                        (snd (unzip flds)) -- Super parameters
                        (zip (snd (unzip attrs)) (snd (unzip attrs))) -- this
    _ -> Constr c attrs [] (zip (snd (unzip attrs)) (snd (unzip attrs)))

-- Function: genClass
-- Objective: Generate a random class with attributes, constructor and methods.
-- Params: Class table, class name, base class, base interface list.
-- Returns: A generated class.
-------------------------------------------------------------------------------
genClass :: CT -> String -> String -> [String] -> Gen Class
genClass ct c b il = 
  do attrs <- genAttrs ct c b
     -- Adding the current class on CT to use its attrs in method expressions
     meths <- genMethods 
                (Data.Map.insert c (TClass (cl attrs [])) ct) c (b:il) True
     -- Generating body expressions for abstract methods
     meths' <- (Control.Monad.mapM 
                 (\s@(Sign (Type r) m p) -> 
                    do e <- genExpression False ct (ctx p) r
                       return (Method s e)
                 ) abs')
     return (cl attrs (meths ++ meths'))
   where cl at mt = (Class c b il -- Class, base class and interface list
                      (Data.List.map (\(k,p) -> (Type k,p)) at) -- Attrs
                      (formatConstr ct c b -- Constructor
                      (Data.List.map (\(k,p) -> (Type k,p)) at)) -- Params
                      mt) -- Methods
         bmeths = case (methods ct b) of
                    Just bms -> Data.List.map (\(Method s _) -> s) bms
                    _ -> []
         abs = Data.List.concatMap 
                 (\i -> case (absmethods ct i) of 
                          Just am -> am
                          _ -> []
                 ) il
         abs' = deleteFirstsBy (\(Sign _ sn' _) (Sign _ sn'' _) -> sn' == sn'')
                  (nubBy (\(Sign _ sn' _) (Sign _ sn'' _) -> sn' == sn'') abs)
                  bmeths
         ctx pm = fromList (("this", Type c) : 
                            (Data.List.map (\(t',n') -> (n',t')) pm))

-- Function: genInterface
-- Objective: Generate a random interface with abstract and default methods.
-- Params: Class table, class name, base interface list.
-- Returns: A generated interface.
----------------------------------------------------------------------------
genInterface :: CT -> String -> [String] -> Gen Interface
genInterface ct i il = 
  do signs <- genSigns ct i il
     defms <- genMethods ct i il False
     return (Interface i il signs defms)

-- Function: addClass
-- Objective: Generate a class with the given name and add to the class table.
-- Params: Class table, Class name.
-- Returns: A class table containing the generated class.
-------------------------------------------------------------------------------
addClass :: CT -> String -> Gen CT
addClass ct c = do cb <- genClassType ct -- base class
                   il <- genInterfaceTypeList ct
                   cl <- genClass ct c cb il
                   return (Data.Map.insert c (TClass cl) ct)

-- Function: addInterface
-- Objective: Generate an interface with the given name and add it to the class
-- table.
-- Params: Class table, Interface name.
-- Returns: A class table containing the generated interface.
-------------------------------------------------------------------------------
addInterface :: CT -> String -> Gen CT
addInterface ct nm = do il <- genInterfaceTypeList ct
                        i <- genInterface ct nm il
                        return (Data.Map.insert nm (TInterface i) ct)

-- Function: addType
-- Objective: Generate an class or interface with the given name and add it to
-- the class table. 
-- Params: Class table, Type name.
-- Returns: A class table containing the generated class or interface.
------------------------------------------------------------------------------
addType :: CT -> String -> Gen CT
addType ct n = oneof [addClass ct n, addInterface ct n]

-- Function: genClassTable
-- Objective: Generate a random class table.
-- Params: None.
-- Returns: A random class table.
--------------------------------------------
genClassTable :: Gen CT
genClassTable = do n <- choose (1,10)
                   ns <- vectorOf n (genClassName)
                   ct <- Control.Monad.foldM (addType) Data.Map.empty (nub ns)
                   return ct

-- Function: genCreateObject
-- Objective: Generate an expression using CreateObject constructor.
-- Params: Size, Context, Class table, Class name.
-- Returns: A Closure expression.
------------------------------------------------------------------------------
genCreateObject :: Int -> Env -> CT -> String -> Gen Expr
genCreateObject size ctx ct c = 
  do el <- Control.Monad.mapM (genExpr (size `div` 3) False ct ctx) f
     return (CreateObject c el)
  where f = case (fields ct c) of
              Just lst -> Data.List.map (\((Type t),_) -> t) lst
              _ -> []

-- Function: genFieldAccess
-- Objective: Generate an expression using FieldAccess constructor.
-- Params: Size, Context, Class table, Class name, Field
-- Returns: A FieldAccess expression.
-------------------------------------------------------------------
genFieldAccess :: Int -> Env -> CT -> String -> String -> Gen Expr
genFieldAccess size ctx ct t f = do e <- genExpr (size `div` 2) False ct ctx t
                                    return (FieldAccess e f)

-- Function: genMethodInvk
-- Objective: Generate an expression using MethodInvk constructor.
-- Params: Size, Context, Class table, Class name, Method name, Method params.
-- Returns: A MethodInvk expression.
------------------------------------------------------------------------------
genMethodInvk :: Int -> Env -> CT -> String -> String -> [String] -> Gen Expr
genMethodInvk size ctx ct t m pt = 
  do e <- genExpr (size `div` 2) True ct ctx t
     el <- Control.Monad.mapM (genExpr (size `div` 3) False ct ctx) pt
     return (MethodInvk e m el) 

-- Function: genCast
-- Objective: Generate an expression using Cast constructor.
-- Params: Size, Context, Class table, Class name, Class name.
-- Returns: A Cast expression.
--------------------------------------------------------------
genCast :: Int -> Env -> CT -> String -> String -> Gen Expr
genCast size ctx ct t tc = do e <- genExpr (size `div` 2) False ct ctx tc
                              return (Cast t e)

-- Function: genClosure
-- Objective: Generate an expression using Closure constructor.
-- Params: Size, Context, Class table, Interface name, Closure params.
-- Returns: A Closure expression.
------------------------------------------------------------------------------
genClosure :: Int -> Env -> CT -> String -> [(Type,String)] -> Gen Expr
genClosure size ctx ct rt pc = 
  do e <- genExpr (size `div` 2) False ct ctx' rt
     return (Closure pc e)
  -- The only allowed variables inside closures are the closure parameters.
  where ctx' = fromList (Data.List.map (\(t,n) -> (n,t)) pc) 

-- Function: ccreateobject
-- Objective: Generate a list of candidates for CreateObject constructor.
-- Params: Size, Context, Class table, Class name.
-- Returns: A list containing Closure expressions of a given type.
-------------------------------------------------------------------------
ccreateobject :: Int -> Env -> CT -> String -> [Gen Expr]
ccreateobject size ctx ct t = 
  Data.List.concatMap
    (\c -> if (c == t) then
             [genCreateObject size ctx ct t]
           else 
             []
    ) ("Object" : keys (Data.Map.filter -- Only classes
                         (\t -> case t of
                                  (TClass _) -> True
                                  _ -> False
                         ) ct))


-- Function: cfieldsacess
-- Objective: Generate a list of candidates for FieldAccess constructor.
-- Params: Size, Context, Class table, Class name.
-- Returns: A list containing FieldAccess expressions of a given type.
----------------------------------------------------------------------
cfieldaccess :: Int -> Env -> CT -> String -> [Gen Expr]
cfieldaccess size ctx ct t =
  Data.List.concatMap 
    (\k -> case (fields ct k) of
             Just lst -> Data.List.concatMap (\((Type t'),f) -> 
                           if (t == t') then
                             [genFieldAccess size ctx ct k f]
                           else
                             [] 
                         ) lst
             _ -> []
    ) ("Object" : keys ct) 

-- Function: cmethodinvk
-- Objective: Generate a list of candidates for MethodInvk constructor.
-- Params: Size, Context, Class table, Class name.
-- Returns: A list containing MethodInvk expressions of a given type.
-----------------------------------------------------------------------
cmethodinvk :: Int -> Env -> CT -> String -> [Gen Expr]
cmethodinvk size ctx ct t = 
  Data.List.concatMap
    (\k -> case (methods ct k) of
             Just lst -> 
               Data.List.concatMap (\(Method (Sign (Type t') m pt) _) ->
                 if (t == t') then
                   let pt' = Data.List.map (\(Type t'',_) -> t'') pt
                     in [genMethodInvk size ctx ct k m pt']
                 else
                   []
               ) lst
             _ -> []
    ) ("Object" : keys ct') 
  ++ 
  Data.List.concatMap
    (\k -> case (absmethods ct k) of
             Just [(Sign (Type t') m pt)] -> 
               if (t == t') then
                 let pt' = Data.List.map (\(Type t'',_) -> t'') pt
                   in [genMethodInvk size ctx ct k m pt']
               else 
                 []
             _ -> []
    ) (keys ct'')
  where ct' = (Data.Map.filter -- Only instantiable class or interface
                (\t -> case t of
                         (TClass _) -> True
                         (TInterface (Interface t' _ _ _)) ->
                           case (absmethods ct t') of
                             Just [(Sign _ _ _)] -> True
                             _ -> False
                ) ct)
        ct'' = (Data.Map.filter -- Only instantiable interface
                 (\t -> case t of
                          (TInterface (Interface t' _ _ _)) ->
                            case (absmethods ct t') of
                              Just [(Sign _ _ _)] -> True
                              _ -> False
                          _ -> False
                 ) ct)


-- Function: cucast
-- Objective: Generate a list of candidates for Cast constructor.
-- Params: Size, Context, Class table, Class name.
-- Returns: A list containing Upcast candidates of a given type.
-----------------------------------------------------------------
cucast :: Int -> Env -> CT -> String -> [Gen Expr]
cucast size ctx ct t = 
  let le = Data.List.concatMap 
             (\k -> if (subtyping ct k t) then
                      [genCast size ctx ct t k]
                    else 
                      []  
             ) ("Object" : keys ct')
      le' = Data.List.concatMap
              (\k -> if (k == t) then
                       [genCast size ctx ct t k] 
                     else
                       []
              ) (keys ct'')
    in le ++ le'
  where ct' = (Data.Map.filter -- Only classes
                (\t -> case t of
                         (TClass _) -> True
                         _ -> False
                ) ct)
        ct'' = (Data.Map.filter -- Only instantiable interfaces
                 (\t -> case t of
                          (TInterface (Interface t' _ _ _)) ->
                            case (absmethods ct t') of
                              Just [(Sign _ _ _)] -> True
                              _ -> False
                          _ -> False
                 ) ct)


-- Function: cdcast
-- Objective: Generate a list of candidates for Cast constructor.
-- Params: Size, Context, Class table, Class name.
-- Returns: A list containing Downcast candidates of a given type.
------------------------------------------------------------------
cdcast :: Int -> Env -> CT -> String -> [Gen Expr]
cdcast size ctx ct t = 
  Data.List.concatMap
    (\k -> if (k /= t && subtyping ct t k) then
             [genCast size ctx ct t k]
           else
             []
    ) (keys ct)

-- Function: cscast
-- Objective: Generate a list of candidates for Cast constructor.
-- Params: Size, Context, Class table, Class name.
-- Returns: A list containing Stupid cast candidates of a given type.
---------------------------------------------------------------------
cscast :: Int -> Env -> CT -> String -> [Gen Expr]
cscast size ctx ct t = 
  Data.List.concatMap
    (\k -> if (not (subtyping ct t k) && not (subtyping ct k t)) then
             [genCast size ctx ct t k]
           else
             []
    ) (keys ct)

-- Function: cclosure
-- Objective: Generate a list of candidates for Closure constructor.
-- Params: Size, Context, Class table, Class name.
-- Returns: A list containing Closure expressions of a given type.
--------------------------------------------------------------------
cclosure :: Int -> Env -> CT -> String -> [Gen Expr]
cclosure size ctx ct t = 
  Data.List.concatMap
    (\i -> if i == t then
             case (absmethods ct i) of
               Just [(Sign (Type rt) mn pm)] -> -- Functional interfaces
                 [genClosure size ctx ct rt pm]
               _ -> []
           else 
             []
    ) (keys (Data.Map.filter -- Only interfaces
              (\t -> case t of
                       (TInterface _) -> True
                       _ -> False
              ) ct))

-- Function: genExpr
-- Objective: Generate an expression of a given type.
-- Params: Size, First call, Class table, Context, Class name.
-- Returns: An expression of a given type.
--------------------------------------------------------------
genExpr :: Int -> Bool -> CT -> Env -> String -> Gen Expr
genExpr size fstgen ct ctx t 
  | size > 0 = 
      if (fstgen) then
        -- Var, CreateObject, FieldAccess, MethodInvk, Cast
        oneof (maybeToList (pickVar ctx (Type t)) ++ 
               coc ++ fac ++ mic ++ ucc)
      else
        -- Var, CreateObject, FieldAccess, MethodInvk, Cast, Closure
        oneof (maybeToList (pickVar ctx (Type t)) ++ 
               coc ++ fac ++ mic ++ ucc ++ clc)
  | otherwise =
      if (fstgen) then
        -- Var, CreateObject, Closure
        do e <- oneof (maybeToList (pickVar ctx (Type t)) ++ coc ++ clc)
           case e of
             cl@(Closure _ _) -> return (Cast t cl) -- Typing the closure
             e' -> return e'
      else 
        -- Var, CreateObject, Closure
        oneof (maybeToList (pickVar ctx (Type t)) ++ coc ++ clc)
    where 
          -- CreateObject candidates
          coc = if (Data.List.length (ccreateobject size ctx ct t) > 0) then
                  [oneof (ccreateobject (size - 1) ctx ct t)]
                else
                  []
          -- FieldAccess candidates 
          fac = if (Data.List.length (cfieldaccess size ctx ct t) > 0) then
                  [oneof (cfieldaccess (size - 1) ctx ct t)]
                else 
                  []
          -- MethodInvk candidates
          mic = if (Data.List.length (cmethodinvk size ctx ct t) > 0) then
                  [oneof (cmethodinvk (size - 1) ctx ct t)]
                else 
                  []
          -- Upcast candidates
          ucc = if (Data.List.length (cucast size ctx ct t) > 0) then
                  [oneof (cucast (size - 1) ctx ct t)]
                else 
                  []
          -- Downcast candidates (not used for testing properties)
          dcc = if (Data.List.length (cdcast size ctx ct t) > 0) then
                  [oneof (cdcast (size - 1) ctx ct t)]
                else 
                  []
          -- Stupid cast candidates (not used for testing properties)
          scc = if (Data.List.length (cscast size ctx ct t) > 0) then
                  [oneof (cscast (size - 1) ctx ct t)]
                else
                  []
          -- Closure candidates
          clc = if (Data.List.length (cclosure size ctx ct t) > 0) then
                  [oneof (cclosure (size - 1) ctx ct t)]
                else
                  []

-- Function: genExpression
-- Objective: Generate an expression of a given type.
-- Params: Class name.
-- Returns: An expression of a given type.
-----------------------------------------------------
genExpression :: Bool -> CT -> Env -> String -> Gen Expr
genExpression fstgen ct ctx t = sized (\n -> genExpr n fstgen ct ctx t)

-- Type-class: Arbitrary Expr
-- Objective: Generate random well-typed expressions.
-----------------------------------------------------
instance Arbitrary Expr where
  arbitrary = do ct <- genClassTable
                 t <- elements ("Object" : keys ct)
                 sized (\n -> genExpr (n `div` 2) True ct Data.Map.empty t)

