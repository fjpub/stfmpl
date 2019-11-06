{-# LANGUAGE TemplateHaskell #-}
-- QuickCheck property-based testing for FJ + Lambda
-- Author: Samuel da Silva Feitosa
-- Date: 04/2018
----------------------------------------------------
module Tests where
import FJParser
import FJUtils
import FJGenerator
import V1.FJInterpreter
import V1.FJTypeChecker
import V2.FJInterpreter
import V2.FJTypeChecker
import Test.QuickCheck
import Data.List
import Data.Map

---------------------------------------------------------------
---------- Property-based testing for first approach ----------
---------------------------------------------------------------

-- Function: prop_genwelltypedct_v1
-- Objective: Test if the generated class table is well-formed.
-- Params: None.
-- Returns: True if the class tables are well-formed, False otherwise.
----------------------------------------------------------------------
prop_genwellformedct_v1 =
  forAll (genClassTable) $
    \ct -> 
      Data.List.all 
        (\(nm, t) -> 
          case (t) of 
            (TClass cl) -> 
              case (V1.FJTypeChecker.classTyping ct Data.Map.empty cl) of
                (r,_) -> r
            (TInterface i) -> 
              case (V1.FJTypeChecker.interfaceTyping ct Data.Map.empty i) of
                (r, _) -> r
        ) (Data.Map.toList ct)

-- Function: prop_gencastsafeexpr_v1
-- Objective: Test if the generated expressions are cast-safe.
-- Params: None.
-- Returns: True if the expression is cast-safe, False otherwise.
-----------------------------------------------------------------
prop_gencastsafeexpr_v1 = 
  forAll (genClassTable) $ 
    \ct -> let ct' = V1.FJTypeChecker.ctTyping ct Data.Map.empty
             in forAll (genInstantiableType ct') $
    \t -> forAll (genExpression True ct' Data.Map.empty t) $
    \e -> case e of 
            c@(Cast t' e') -> 
              case (V1.FJTypeChecker.typeof ct' Data.Map.empty c) of
                Right (Type t'', _) -> subtyping ct' t'' t'
                _ -> False
            _ -> True

-- Function: prop_genwelltypedexpr_v1
-- Objective: Test if the generated expressions are well-typed.
-- Params: None.
-- Returns: True if the expressions are well-typed, False otherwise.
--------------------------------------------------------------------
prop_genwelltypedexpr_v1 =
  forAll (genClassTable) $
    \ct -> forAll (genInstantiableType ct) $ 
    \t -> forAll (genExpression True ct Data.Map.empty t) $ 
    \e -> either (const False)
                 (\(Type t', _) -> t == t')
                 (V1.FJTypeChecker.typeof ct Data.Map.empty e)

-- Function: prop_progress_v1
-- Objective: Tests for the property of progress.
-- Params: None.
-- Returns: True if the property held for the test casts, False otherwise.
-------------------------------------------------------------------------- 
prop_progress_v1 =
  forAll (genClassTable) $
    \ct -> forAll (genInstantiableType ct) $
    \t -> forAll (genExpression True ct Data.Map.empty t) $
    \e -> isValue ct e || 
          maybe (False) (const True) (V1.FJInterpreter.eval' ct e)

-- Function: prop_preservation_v1
-- Objective: Tests for the property of preservation.
-- Params: None.
-- Returns: True if the property held for the test cases, False otherwise.
--------------------------------------------------------------------------
prop_preservation_v1 =
  forAll (genClassTable) $
    \ct -> let ct' = V1.FJTypeChecker.ctTyping ct Data.Map.empty 
             in forAll (genInstantiableType ct') $ 
    \t -> forAll (genExpression True ct' Data.Map.empty t) $
    \e -> case (V1.FJTypeChecker.typeof ct' Data.Map.empty e) of
            Right (tp, e') -> 
              either (const False)
                (\(Type t', _) -> subtyping ct' t' t)
                  (case (V1.FJInterpreter.eval' ct' e') of 
                     Just e'' -> 
                       V1.FJTypeChecker.typeof ct' Data.Map.empty e''
                     _ -> V1.FJTypeChecker.throwError (UnknownError e')
                  )
            _ -> False

----------------------------------------------------------------
---------- Property-based testing for second approach ----------
----------------------------------------------------------------

-- Function: prop_genwelltypedct_v2
-- Objective: Test if the generated class table is well-formed.
-- Params: None.
-- Returns: True if the class tables are well-formed, False otherwise.
----------------------------------------------------------------------
prop_genwellformedct_v2 =
  forAll (genClassTable) $
    \ct -> Data.List.all
             (\(nm, t) -> 
               case (t) of
                 (TClass cl) -> 
                   V2.FJTypeChecker.classTyping ct Data.Map.empty cl
                 (TInterface i) -> 
                   V2.FJTypeChecker.interfaceTyping ct Data.Map.empty i
             ) (Data.Map.toList ct)

-- Function: prop_gencastsafeexpr_v2
-- Objective: Test if the generated expressions are cast-safe.
-- Params: None.
-- Returns: True if the expression is cast-safe, False otherwise.
-----------------------------------------------------------------
prop_gencastsafeexpr_v2 =
  forAll (genClassTable) $
    \ct -> forAll (genInstantiableType ct) $
    \t -> forAll (genExpression True ct Data.Map.empty t) $
    \e -> case e of
            (Cast t' e) ->
              case (V2.FJTypeChecker.typeof ct Data.Map.empty 
                                            (lambdaMark e (Type t'))) of
                Right (Type t'') -> subtyping ct t'' t'
                _ -> False
            _ -> True

-- Function: prop_genwelltypedexpr_v2
-- Objective: Test if the generated expressions are well-typed.
-- Params: None.
-- Returns: True if the expressions are well-typed, False otherwise.
--------------------------------------------------------------------
prop_genwelltypedexpr_v2 =
  forAll (genClassTable) $
    \ct -> forAll (genInstantiableType ct) $
    \t -> forAll (genExpression True ct Data.Map.empty t) $
    \e -> either (const False)
                 (\(Type t') -> t == t')
                 (V2.FJTypeChecker.typeof ct Data.Map.empty e)

-- Function: prop_progress_v2
-- Objective: Tests for the property of progress.
-- Params: None.
-- Returns: True if the property held for the test casts, False otherwise.
-------------------------------------------------------------------------- 
prop_progress_v2 =
  forAll (genClassTable) $
    \ct -> forAll (genInstantiableType ct) $
    \t -> forAll (genExpression True ct Data.Map.empty t) $
    \e -> isValue ct e || 
          maybe (False) (const True) (V2.FJInterpreter.eval' ct e)

-- Function: prop_preservation_v2
-- Objective: Tests for the property of preservation.
-- Params: None.
-- Returns: True if the property held for the test cases, False otherwise.
--------------------------------------------------------------------------
prop_preservation_v2 =
  forAll (genClassTable) $
    \ct -> forAll (genInstantiableType ct) $
    \t -> forAll (genExpression True ct Data.Map.empty t) $
    \e -> either (const False)
                 (\(Type t') -> subtyping ct t' t)
                 (case (V2.FJInterpreter.eval' ct e) of
                    Just e' -> V2.FJTypeChecker.typeof ct Data.Map.empty e'
                    _ -> V2.FJTypeChecker.throwError (UnknownError e)
                 )

---------------------------------------------------------------------
---------- Equivalence testing for the proposed approaches ----------
---------------------------------------------------------------------

-- Function: prop_equivalence
-- Objective: Tests if both approaches are equivalent.
-- Params: None.
-- Returns: True if property held, False otherwise.
------------------------------------------------------
prop_equivalence = 
  forAll (genClassTable) $
    \ct -> forAll (genInstantiableType ct) $
    \t -> forAll (genExpression True ct Data.Map.empty t) $
    \e -> let ct' = V1.FJTypeChecker.ctTyping ct Data.Map.empty
            in case (V1.FJTypeChecker.typeof ct' Data.Map.empty e) of
                 Right (_, e') -> 
                   let v1r = removeRuntimeAnnotation (V1.FJInterpreter.eval ct' e')
                       v2r = removeRuntimeAnnotation (V2.FJInterpreter.eval ct e)
                     in v1r == v2r
                 _ -> False

-----------------------------------------------------------------
---------- Using QuickCheck for testing all properties ----------
-----------------------------------------------------------------
return []
main = $forAllProperties $
         quickCheckWithResult (stdArgs { maxSuccess = 10000 })


