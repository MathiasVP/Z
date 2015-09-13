module TypeUtils (Env, Substitution, ArgOrd, Bindings,
                  generalize, follow, makeBindings,
                  instansiate, instansiate') where
import qualified Data.Unique as U
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List
import TypedAst

type Substitution = Map U.Unique Type
type Env = Map String Type
type ArgOrd = Map String (Map Int String)
type Bindings = Map String Type

generalize :: U.Unique -> Substitution -> Substitution
generalize u subst =
  case Map.lookup u subst of
    Just (TypeVar u') -> generalize u' (Map.delete u subst)
    Just ty -> Map.delete u subst
    Nothing -> subst
    
follow :: Substitution -> Type -> Type
follow subst = fol
  where
    fol (TypeVar u) =
      case Map.lookup u subst of
        Just (TypeVar u') ->
          if u == u' then TypeVar u'
          else fol (TypeVar u')
        Just t -> fol t
        Nothing -> TypeVar u
    fol IntType = IntType
    fol StringType = StringType
    fol BoolType = BoolType
    fol RealType = RealType
    fol (Name s types) = Name s types
    fol (Array ty) = Array (fol ty)
    fol (Tuple types) = Tuple (List.map fol types)
    fol (Record b fields) =
      let f (s, ty) = (s, fol ty)
      in Record b (List.map f fields)
    fol (Arrow tDom tCod) = Arrow (fol tDom) (fol tCod)
    fol (Union t1 t2) = union (fol t1) (fol t2)
    fol (Forall u ty) = Forall u (fol ty)
    fol Error = Error
    fol (Intersect t1 t2) = Intersect (fol t1) (fol t2)
    
makeBindings :: ArgOrd -> String -> [Type] -> Bindings
makeBindings argOrd s types =
  case Map.lookup s argOrd of
    Just argOrd -> Map.fromList $ List.zip (Map.elems argOrd) types
    Nothing -> Map.empty
    
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
      inst Error = Error
      inst IntType = IntType
      inst RealType = RealType
      inst BoolType = BoolType
      inst StringType = StringType
      inst (Intersect t1 t2) = Intersect (inst t1) (inst t2)
  in inst t

instansiate' :: Type -> Map String Type -> Type
instansiate' = Map.foldrWithKey instansiate