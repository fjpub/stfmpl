-- Haskell parser for Featherweight Java
-- Author: Samuel da Silva Feitosa
-- Date: 01/2018
---------------------------------------------
module FJParser where

import Data.Map

-- Featherweight Java syntactic constructors
--------------------------------------------
-- class C extends C { C_ f_; K M_ }
data Class = Class String String [(Type,String)] Constr [Method]
           deriving (Eq)

-- C(C_ f_) { super(f_); this.f_.f_; }
data Constr = Constr String [(Type,String)] [String] [(String,String)]
            deriving (Eq)

-- C m(C_ x_) { return e; }
data Method = Method Type String [(Type,String)] Expr
            deriving (Eq)

data Expr = Var String                               -- Variable
          | FieldAccess Expr String                  -- Field Access
          | MethodInvk Expr String [Expr]            -- Method Invocation
          | CreateObject String [Expr]               -- Object Instantiation
          | Cast String Expr                         -- Cast
          deriving (Eq)

-- Featherweight Java nominal typing
------------------------------------
data Type = TypeClass String
          deriving (Eq)

-- Featherweight Java auxiliary definitions
-------------------------------------------
type Env = Map String Type
type CT = Map String Class

-- Auxiliary definitions to Type-Checking
-----------------------------------------
data TypeError = VariableNotFound String
               | FieldNotFound String
               | ClassNotFound String
               | MethodNotFound String String
               | WrongCast String Expr
               | ParamsTypeMismatch [(Expr,Type)]
               | UnknownError Expr
               deriving (Show,Eq)
    
    
-- Function: throwError
-- Objective: Launching a type error.
-- Params: Expected type, Found type, Expression presenting the error.
-- Returns: A type error structure.
----------------------------------------------------------------------
throwError :: TypeError -> Either TypeError Type 
throwError e = Left e


-------------------------------------------------------------------------------
----------------------------- FORMATTING FUNCTIONS ----------------------------
-------------------------------------------------------------------------------

-- Function: showAttrs
-- Objective: Format attributes as in a Java source-code.
-- Params: List of types and names.
-- Returns: A formatted string.
---------------------------------------------------------
showAttrs :: [(Type,String)] -> String
showAttrs [] = ""
showAttrs ((t,s):hs) = show t ++ " " ++ s ++ ";\n  " ++ showAttrs hs

-- Function: showFormalParams
-- Objective: Format formal parameters as a Java method.
-- Params: List of types and names.
-- Returns: A formatted string.
--------------------------------------------------------
showFormalParams :: [(Type,String)] -> String
showFormalParams [] = ""
showFormalParams [(t,s)] = show t ++ " " ++ s
showFormalParams ((t,s):hs) = show t ++ " " ++ s ++ ", " ++ showFormalParams hs

-- Function: showAttrAssign
-- Objective: Format the constructor assignments.
-- Params: A list containing the member names.
-- Returns: A formatted string.
-------------------------------------------------
showAttrAssign :: [(String,String)] -> String
showAttrAssign [] = ""
showAttrAssign [(f,s)] = "    this." ++ f ++ " = " ++ s ++ ";"
showAttrAssign ((f,s):hs) = "    this." ++ f ++ " = " ++ s ++ ";\n" ++ 
                              showAttrAssign hs

-- Function: showParams
-- Objective: Format the actual parameters as expected by a method invocation.
-- Params: A list containing the variable names.
-- Returns: A formatted string.
-------------------------------------------------------------------------------
showParams :: [String] -> String
showParams [] = ""
showParams [s] = s
showParams (h:hs) = h ++ "," ++ showParams hs

-- Function: showMethods
-- Objective: Format a method list.
-- Params: List of methods.
-- Returns: A formatted string.
-----------------------------------
showMethods :: [Method] -> String
showMethods [] = ""
showMethods [m] = show m
showMethods (h:hs) = show h ++ "\n  " ++ showMethods hs

-- Function: showExprs
-- Objective: Format a list of expressions.
-- Params: List of expressions.
-- Returns: A formatted string.
-------------------------------------------
showExprs :: [Expr] -> String
showExprs [] = ""
showExprs [e] = show e
showExprs (h:hs) = show h ++ "," ++ showExprs hs

-- Function: formatCT
-- Objective: Format a class table as a sequence of classes.
-- Params: A list of classes.
-- Returns: A string containing a formatted list of classes.
------------------------------------------------------------
formatCT :: [Class] -> String
formatCT [] = "\n"
formatCT (h:hs) = (show h) ++ "\n" ++ formatCT hs

-- Function: formatExpr
-- Objective: Generate the source-code of the main class.
-- Params: An expression.
-- Returns: A string containing the source-code of the main class.
------------------------------------------------------------------
formatExpr :: Expr -> String
formatExpr e = "class FJMain {\n" ++ 
               "  public static void main(String args[]) {\n" ++
               "    System.out.println((" ++ show e ++ ").toString());\n" ++
               "  }\n" ++
               "}\n"
               
-- Function: formatJavaProgram
-- Objective: Generate a string containing a complete Java program.
-- Params: Class table, Expression.
-- Returns: A string containing a compilable Java program.
-------------------------------------------------------------------
formatJavaProgram :: CT -> Expr -> String
formatJavaProgram ct e = formatCT (elems ct) ++ "\n" ++ formatExpr e

-------------------------------------------------------------------------------
----------------------------- FORMATTING INSTANCES ----------------------------
-------------------------------------------------------------------------------

-- Formatting classes
---------------------
instance Show Class where
  show (Class c b at cn m) = "class " ++ c ++ " extends " ++ b ++ " {\n  " ++ 
    showAttrs at ++ show cn ++ "\n  " ++ showMethods m ++ "\n}"

-- Formatting constructors
--------------------------
instance Show Constr where
  show (Constr c fp at ths) = c ++ "(" ++ showFormalParams fp ++ 
    ") {\n    super(" ++ showParams at ++ ");\n" ++ 
    showAttrAssign ths ++ "\n  }"

-- Formatting methods
---------------------
instance Show Method where
  show (Method r m fp e) = show r ++ " " ++ m ++ "(" ++ 
    showFormalParams fp ++ ") {\n    return " ++ show e ++ ";\n  }"

-- Formatting types
-------------------
instance Show Type where
  show (TypeClass c) = c

-- Formatting expressions
-------------------------
instance Show Expr where
  show (Var v) = v
  show (FieldAccess e f) = show e ++ "." ++ f
  show (MethodInvk e m p) = show e ++ "." ++ m ++ "(" ++ showExprs p ++ ")"
  show (CreateObject c p) = "new " ++ c ++ "(" ++ showExprs p ++ ")"
  show (Cast c e) = "((" ++ c ++ ") " ++ show e ++ ")"

