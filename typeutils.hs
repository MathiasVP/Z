module TypeUtils (Env, Substitution, ArgOrd, Bindings,
                  generalize, follow, makeBindings,
                  instansiate, instansiates, instansiatePoly) where
import qualified Data.Unique as U
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List
import TypedAst

type Substitution = Map U.Unique Type
type Env = Map String Type
type ArgOrd = Map String (Map Int String)
type Bindings = Map String Type

generalize :: U.Unique -> Substitution -> IO Substitution
generalize u subst =
  case Map.lookup u subst of
    Just (TypeVar u') -> generalize u' (Map.delete u subst)
    Just _ -> return $ Map.delete u subst
    Nothing -> return subst
 
follow :: Substitution -> Type -> Type
follow subst = fol Set.empty
  where
    fol visited (TypeVar u) =
      case Map.lookup u subst of
        Just (TypeVar u') ->
          if u == u' then TypeVar u'
          else if Set.member u' visited then (TypeVar u')
               else fol (Set.insert u visited) (TypeVar u')
        Just t -> fol visited t
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

makeBindings :: ArgOrd -> String -> [Type] -> Bindings
makeBindings argOrd s types =
  case Map.lookup s argOrd of
    Just argOrd -> Map.fromList $ List.zip (Map.elems argOrd) types
    Nothing -> Map.empty

instansiatePoly :: Substitution -> Type -> Type -> Type
instansiatePoly subst t1 t2 = inst t2
  where
    inst t =
      case follow subst t of
        TypeVar u -> t1
        Name s tys -> Name s (List.map inst tys)
        Forall u ty -> Forall u (inst ty)
        Arrow tDom tCod -> Arrow (inst tDom) (inst tCod)
        Union t1 t2 -> union (inst t1) (inst t2)
        Tuple tys -> Tuple (List.map inst tys)
        Record b fields -> Record b (List.map (\(s, ty) -> (s, inst ty)) fields)
        Array ty -> Array (inst ty)
        Intersect t1 t2 -> intersect (inst t1) (inst t2)
        t -> t

instansiate :: String -> Type -> Type -> Type
instansiate name ty t =
  let inst (Name s [])
        | s == name = ty
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