module Ast where
import Data.Unique
import qualified Data.List as List

data Type
  = IntType
  | BoolType
  | StringType
  | RealType

  | Name String [Type]
  | Array Type
  | Tuple [Type]
  | Record Bool [(String, Type)]
  | Forall Unique Type
  | Arrow Type Type
  | Union Type Type
  | Intersect Type Type
  | TypeVar Unique
  | Error
    deriving (Eq, Ord)

instance Show Type where
  show IntType = "Int"
  show BoolType = "Bool"
  show StringType = "String"
  show RealType = "Real"

  show (Union t1 (Union t2 t3)) = show t1 ++ " | " ++ "(" ++ show t2 ++ " | " ++ show t3 ++ ")"
  show (Union t1 t2) = show t1 ++ " | " ++ show t2

  show (Intersect t1 (Intersect t2 t3)) = show t1 ++ " & (" ++ show t2 ++ " & " ++ show t3 ++ ")"

  show (Intersect t1 (Union t2 t3)) = show t1 ++ " & (" ++ show t2 ++ " | " ++ show t3 ++ ")"
  show (Intersect (Union t1 t2) t3) = "(" ++ show t1 ++ " | " ++ show t2 ++ ") & " ++ show t1
  show (Intersect t1 t2) = show t1 ++ " & " ++ show t2

  show (Arrow t1 (Union t2 t3)) = show t1 ++ " -> (" ++ show t2 ++ " | " ++ show t3 ++ ")"
  show (Arrow (Union t1 t2) t3) = "(" ++ show t1 ++ " | " ++ show t2 ++ ") -> " ++ show t3 ++ ")"
  show (Arrow t1 t2) = show t1 ++ " -> " ++ show t2

  show (Name s []) = s
  show (Name s tys) = s ++ "<" ++ (List.intercalate ", " (List.map show tys)) ++ ">"
  show (Array t) = "[" ++ show t ++ "]"
  show (Tuple tys) = "(" ++ List.intercalate "," (List.map show tys) ++ ")"
  show (Record _ fields) = "{" ++ List.intercalate ", " (List.map showField fields) ++ "}"
    where showField (s, t) = s ++ ": " ++ show t
  show (Forall u ty) = "forall " ++ show u ++ ". " ++ show ty
  show (TypeVar u) = show u
  show Error = "Error"

instance Show Unique where
  show u = "t" ++ show (hashUnique u)

data Decl = TypeDecl String [String] Type
          | FunDecl String [String] [MatchExpr] (Maybe Type) Statement
    deriving (Show)

data Expr = IntExpr Int
          | RealExpr Double
          | BoolExpr Bool
          | StringExpr String
          | OrExpr Expr Expr
          | AndExpr Expr Expr
          | EqExpr Expr Expr
          | NeqExpr Expr Expr
          | LtExpr Expr Expr
          | GtExpr Expr Expr
          | LeExpr Expr Expr
          | GeExpr Expr Expr
          | AddExpr Expr Expr
          | SubExpr Expr Expr
          | MultExpr Expr Expr
          | DivExpr Expr Expr
          | UnaryMinusExpr Expr
          | BangExpr Expr
          | CallExpr Expr Expr
          | TypeConstrainedExpr Expr Type
          | ListExpr [Expr]
          | TupleExpr [Expr]
          | RecordExpr [(String, Expr)]
          | LValue LValueExpr
          | LambdaExpr [MatchExpr] Statement
  deriving (Show)

data MatchExpr = TupleMatchExpr [MatchExpr]
               | ListMatchExpr [MatchExpr]
               | RecordMatchExpr [(String, MatchExpr)]
               | TypedMatchExpr MatchExpr Type
               | VarMatch String
               | IntMatchExpr Int
               | StringMatchExpr String
               | BoolMatchExpr Bool
  deriving (Show)

data LValueExpr = VarExpr String
                | FieldAccessExpr LValueExpr String
                | ArrayAccessExpr LValueExpr Expr
  deriving (Show)

data Statement = IfStatement Expr Statement (Maybe Statement)
               | WhileStatement Expr Statement
               | ForStatement MatchExpr Expr Statement
               | CompoundStatement [Statement]
               | AssignStatement (Either MatchExpr LValueExpr) Expr
               | MatchStatement Expr [(MatchExpr, Statement)]
               | ReturnStatement Expr
               | BreakStatement
               | ContinueStatement
               | DeclStatement Decl
  deriving (Show)

-------------------------------------------------------
-- Type simplications
-------------------------------------------------------
contains :: Type -> Type -> Bool
contains IntType IntType = True
contains BoolType BoolType = True
contains StringType StringType = True
contains RealType RealType = True
contains (Union t1 t2) t3
  | t1 == t3 = True
  | t2 == t3 = True
  | otherwise = contains t1 t3 || contains t1 t3
contains (Intersect t1 t2) t3
  | t1 == t3 && t2 == t3 = True
  | otherwise = contains t1 t3 && contains t1 t3
contains (Arrow t1 t2) (Arrow t3 t4) =
  t1 == t3 && t2 == t4
contains (Name s1 tys1) (Name s2 tys2) =
  s1 == s2 && tys1 == tys2
contains (Array t1) (Array t2) =
  t1 == t2
contains (Tuple tys1) (Tuple tys2)
  | List.length tys1 == List.length tys2 =
     List.all (uncurry contains) (List.zip tys1 tys2)
  | otherwise = False
contains (Record _ fields1) (Record _ fields2)
  | List.length fields1 == List.length fields2 =
    List.all (uncurry (==)) (List.zip fields1 fields2)
  | otherwise = False
contains (Forall u1 ty1) (Forall u2 ty2)
  | u1 == u2 && ty1 == ty2 = True
  | otherwise = False
contains (Forall u t1) t2 = contains t1 t2
contains (TypeVar u1) (TypeVar u2) =
  u1 == u2
contains Error Error = True
contains _ _ = False

union :: Type -> Type -> Type
union t1 (Union t2 t3) = union (union t1 t2) t3
union t1 t2
  | t1 `contains` t2 = t1
  | otherwise = Union t1 t2

intersect :: Type -> Type -> Type
intersect t1 (Intersect t2 t3) = intersect (intersect t1 t2) t3
intersect t1 t2
  | t1 `contains` t2 = t2
  | otherwise = Intersect t1 t2
