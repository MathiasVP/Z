module Types(Identifier(..), stringOf, idOf, identifier,
             fromString, placeholder, Type(..), union) where
import qualified Data.List as List
import Hash
import Data.Map()
import Data.Foldable()
import Data.Hashable

data Type
  = IntType
  | BoolType
  | StringType
  | RealType
  | Name String [Type]
  | Array Type
  | Tuple [Type]
  | Record Bool [(String, Type)]
  | Arrow Type Type
  | Union Type Type
    deriving (Eq, Ord, Show)

instance Hashable Type where
  hashWithSalt n IntType = n `combine` 3
  hashWithSalt n BoolType = n `combine` 5
  hashWithSalt n StringType = n `combine` 7
  hashWithSalt n RealType = n `combine` 7
  hashWithSalt n (Name name tys) =
    hashWithSalt n (name, tys)
  hashWithSalt n (Array ty) =
    hashWithSalt n ty `combine` 9
  hashWithSalt n (Tuple tys) =
    hashWithSalt n tys `combine` 11
  hashWithSalt n (Record _ fields) =
    hashWithSalt n fields `combine` 13
  hashWithSalt n (Arrow tyDom tyCod) =
    hashWithSalt n (tyDom, tyCod) `combine` 17
  hashWithSalt n (Union ty1 ty2) =
    hashWithSalt n (ty1, ty2) `combine` 19

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
contains _ _ = False

union :: Type -> Type -> Type
union t1 (Union t2 t3) = (t1 `union` t2) `union` t3
union t1 t2
  | t1 `contains` t2 = t1
  | otherwise = Union t1 t2
