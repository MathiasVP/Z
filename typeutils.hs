{-# LANGUAGE TupleSections #-}

module TypeUtils where
import Data.Map (Map)
import Control.Monad
import Data.Ord
import Data.Foldable
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List
import TypedAst
import Types
import Unique

type Substitution = Map UniqueInt Type
type Env = Map String (UniqueInt, Type)
type ArgOrd = Map String (Map Int String)
type Bindings = Map String Type

exprOf = fst
typeOf = snd

normaliseFields :: Ord a => [(a, b)] -> [(a, b)]
normaliseFields = List.sortBy (comparing fst)

equalRecordFields fields1 fields2 =
  let f fields = List.map fst (normaliseFields fields)
  in f fields1 == f fields2

inferList :: (a -> Env -> ArgOrd -> Substitution -> IO (b, Env, ArgOrd, Substitution)) ->
              Env -> ArgOrd -> Substitution -> [a] -> IO ([b], Env, ArgOrd, Substitution)
inferList inferer env argOrd subst list =
  do (list', env', argOrd', subst') <- foldM f ([], env, argOrd, subst) list
     return (List.reverse list', env', argOrd', subst')
  where f (list', env, argOrd, subst) elem = do
        (elem', env', argOrd', subst') <- inferer elem env argOrd subst
        return (elem' : list', env', argOrd', subst')

follow :: Substitution -> Type -> Type
follow subst = fol Set.empty
  where
    fol visited (TypeVar u)
      | Set.member u visited = TypeVar u
      | otherwise =
        case Map.lookup u subst of
          Just t -> fol (Set.insert u visited) t
          Nothing -> TypeVar u
    fol visited (Array ty) = Array (fol visited ty)
    fol visited (Tuple types) = Tuple (List.map (fol visited) types)
    fol visited (Record b fields) =
      let f (s, ty) = (s, fol visited ty)
      in Record b (List.map f fields)
    fol visited (Arrow tDom tCod) = Arrow (fol visited tDom) (fol visited tCod)
    fol visited (Union t1 t2) = union (fol visited t1) (fol visited t2)
    fol visited (Forall u ty) = Forall u (fol visited ty)
    fol visited (Intersect t1 t2) = Intersect (fol visited t1) (fol visited t2)
    fol _ t = t

free :: Type -> Substitution -> Bool
free ty subst =
  case follow subst ty of
    TypeVar _ -> True
    _         -> False
    
makeBindings :: ArgOrd -> Identifier -> [Type] -> Bindings
makeBindings argOrd s types =
  case Map.lookup (stringOf s) argOrd of
    Just argOrd -> Map.fromList $ List.zip (Map.elems argOrd) types
    Nothing -> Map.empty

instansiate :: String -> Type -> Type -> Type
instansiate name ty t =
  let inst (Name s [])
        | stringOf s == name = ty
        | otherwise = Name s []
      inst (Name s tys) = Name s (List.map inst tys)
      inst (Forall u ty) = Forall u (inst ty)
      inst (Arrow tDom tCod) = Arrow (inst tDom) (inst tCod)
      inst (Union t1 t2) = union (inst t1) (inst t2)
      inst (Tuple tys) = Tuple (List.map inst tys)
      inst (Record b fields) = Record b (List.map (\(s, ty) -> (s, inst ty)) fields)
      inst (Array ty) = Array (inst ty)
      inst (TypeVar u) = TypeVar u
      inst (Intersect t1 t2) = intersect (inst t1) (inst t2)
      inst t = t
  in inst t

instansiates :: Type -> Map String Type -> Type
instansiates = Map.foldrWithKey instansiate

mkTypeVar :: IO Type
mkTypeVar = unique >>= return . TypeVar

makeArrow :: [Type] -> Type -> Type
makeArrow types retTy = List.foldr Arrow retTy types

typevars :: Type -> [UniqueInt]
typevars (TypeVar u) = [u]
typevars (Forall u ty) =
  if List.elem u uniques then uniques
  else u : uniques
  where uniques = typevars ty
typevars (Arrow t1 t2) = List.nub $ typevars t1 ++ typevars t2
typevars (Union t1 t2) = List.nub $ typevars t1 ++ typevars t2
typevars (Tuple tys) = List.nub $ List.concatMap typevars tys
typevars (Record _ fields) = List.nub $ List.concatMap typevars (List.map snd fields)
typevars (Array ty) = typevars ty
typevars (Intersect t1 t2) = List.nub $ typevars t1 ++ typevars t2
typevars _ = []

isQuantified :: Substitution -> UniqueInt -> Type -> Bool
isQuantified subst u ty = isQuant ty
  where
    isQuant (Forall u' ty)
      | follow subst (TypeVar u') == follow subst (TypeVar u) =
        True
      | otherwise = isQuant ty
    isQuant (Arrow t1 t2) = isQuant t1 || isQuant t2
    isQuant (Union t1 t2) = isQuant t1 || isQuant t2
    isQuant (Tuple tys) = List.any isQuant tys
    isQuant (Record _ fields) = List.any (isQuant . snd) fields
    isQuant (Array ty) = isQuant ty
    isQuant (Intersect t1 t2) = isQuant t1 || isQuant t2
    isQuant _ = False

rename :: UniqueInt -> UniqueInt -> Type -> Type
rename new old ty =
  let re (Name s tys) = Name s (List.map re tys)
      re (Forall u ty) = Forall u (re ty)
      re (Arrow tDom tCod) = Arrow (re tDom) (re tCod)
      re (Union t1 t2) = union (re t1) (re t2)
      re (Tuple tys) = Tuple (List.map re tys)
      re (Record b fields) = Record b (List.map (\(s, ty) -> (s, re ty)) fields)
      re (Array ty) = Array (re ty)
      re (TypeVar u)
        | u == old = TypeVar new
        | otherwise = TypeVar u
      re (Intersect t1 t2) = intersect (re t1) (re t2)
      re t = t
  in re ty

makeForall :: Substitution -> Type -> Type -> IO Type
makeForall subst ty1 ty2 =
  foldrM make ty2 (typevars (follow subst ty1))
  where make u ty
          | isQuantified subst u ty ||
            not (free (TypeVar u) subst) = return (follow subst ty)
          | otherwise =
            do TypeVar u' <- mkTypeVar
               return $ Forall u' (rename u' u (follow subst ty))