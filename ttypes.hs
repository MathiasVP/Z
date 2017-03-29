module TTypes(Identifier(..), stringOf, idOf, identifier,
             fromString, placeholder, TType(..), tunion, tintersect) where
import qualified Data.List as List
import Hash
import Data.Map()
import Data.Foldable()
import Data.Hashable

data TType
  = TIntType
  | TBoolType
  | TStringType
  | TRealType
  | TName Identifier [TType]
  | TArray TType
  | TTuple [TType]
  | TRecord Bool [(String, TType)]
  | TForall Identifier TType
  | TArrow TType TType
  | TUnion TType TType
  | TIntersect TType TType
  | TTypeVar Identifier
  | TRef String [TType]
  | TError
    deriving (Eq, Ord, Show)

instance Hashable TType where
  hashWithSalt n TIntType = n `combine` 3
  hashWithSalt n TBoolType = n `combine` 5
  hashWithSalt n TStringType = n `combine` 7
  hashWithSalt n TRealType = n `combine` 7
  hashWithSalt n (TName name tys) =
    hashWithSalt n (name, tys)
  hashWithSalt n (TArray ty) =
    hashWithSalt n ty `combine` 9
  hashWithSalt n (TTuple tys) =
    hashWithSalt n tys `combine` 11
  hashWithSalt n (TRecord _ fields) =
    hashWithSalt n fields `combine` 13
  hashWithSalt n (TForall uint ty) =
    hashWithSalt n (uint, ty) `combine` 15
  hashWithSalt n (TArrow tyDom tyCod) =
    hashWithSalt n (tyDom, tyCod) `combine` 17
  hashWithSalt n (TUnion ty1 ty2) =
    hashWithSalt n (ty1, ty2) `combine` 19
  hashWithSalt n (TIntersect ty1 ty2) =
    hashWithSalt n (ty1, ty2) `combine` 23
  hashWithSalt n (TRef name tys) =
    hashWithSalt n (name, tys) `combine` 29
  hashWithSalt n (TTypeVar u) =
    hashWithSalt n u `combine` 29
  hashWithSalt n TError = n `combine` 31

{-
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
  show (Arrow (Arrow t1 t2) t3) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")" ++ " -> " ++ show t3
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
-}
-------------------------------------------------------
-- Type simplications
-------------------------------------------------------
tcontains :: TType -> TType -> Bool
tcontains TIntType TIntType = True
tcontains TBoolType TBoolType = True
tcontains TStringType TStringType = True
tcontains TRealType TRealType = True
tcontains (TUnion t1 t2) t3
  | t1 == t3 = True
  | t2 == t3 = True
  | otherwise = tcontains t1 t3 || tcontains t1 t3
tcontains (TIntersect t1 t2) t3
  | t1 == t3 && t2 == t3 = True
  | otherwise = tcontains t1 t3 && tcontains t1 t3
tcontains (TArrow t1 t2) (TArrow t3 t4) =
  t1 == t3 && t2 == t4
tcontains (TName s1 tys1) (TName s2 tys2) =
  s1 == s2 && tys1 == tys2
tcontains (TArray t1) (TArray t2) =
  t1 == t2
tcontains (TTuple tys1) (TTuple tys2)
  | List.length tys1 == List.length tys2 =
     List.all (uncurry tcontains) (List.zip tys1 tys2)
  | otherwise = False
tcontains (TRecord _ fields1) (TRecord _ fields2)
  | List.length fields1 == List.length fields2 =
    List.all (uncurry (==)) (List.zip fields1 fields2)
  | otherwise = False
tcontains (TForall u1 ty1) (TForall u2 ty2)
  | u1 == u2 && ty1 == ty2 = True
  | otherwise = False
tcontains (TForall _ t1) t2 = tcontains t1 t2
tcontains (TTypeVar u1) (TTypeVar u2) =
  u1 == u2
tcontains TError TError = True
tcontains _ _ = False

tunion :: TType -> TType -> TType
tunion t1 (TUnion t2 t3) = (t1 `tunion` t2) `tunion` t3
tunion t1 t2
  | t1 `tcontains` t2 = t1
  | otherwise = TUnion t1 t2

tintersect :: TType -> TType -> TType
tintersect t1 (TIntersect t2 t3) = (t1 `tintersect` t2) `tintersect` t3
tintersect t1 t2
  | t1 `tcontains` t2 = t2
  | otherwise = TIntersect t1 t2
