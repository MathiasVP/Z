{-# LANGUAGE TupleSections, LambdaCase #-}

module TypeUtils where
import Data.Map (Map)
import Control.Monad
import Control.Monad.Loops
import Data.Ord
import Data.Foldable
import Control.Monad.State.Lazy
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

type Infer a = StateT (Substitution, Env, ArgOrd) IO a


substitution :: Infer Substitution
substitution = gets (\(s, _, _) -> s)

environment :: Infer Env
environment = gets (\(_, e, _) -> e)

argumentOrder :: Infer ArgOrd
argumentOrder = gets (\(_, _, a) -> a)

modifySubst :: (Substitution -> Substitution) -> Infer ()
modifySubst f = modify $ \(s, e, a) -> (f s, e, a)

modifyEnv :: (Env -> Env) -> Infer ()
modifyEnv f = modify $ \(s, e, a) -> (s, f e, a)

modifyArgOrd :: (ArgOrd -> ArgOrd) -> Infer ()
modifyArgOrd f = modify $ \(s, e, a) -> (s, e, f a)


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

follow :: Type -> Infer Type
follow = fol Set.empty
  where
    fol visited (TypeVar u)
      | Set.member u visited = return $ TypeVar u
      | otherwise = do
		substitution >>= \subst ->
		  case Map.lookup u subst of
		    Just t -> fol (Set.insert u visited) t
		    Nothing -> return $ TypeVar u
    fol visited (Array ty) = fol visited ty >>= return . Array
    fol visited (Tuple types) = mapM (fol visited) types >>= return . Tuple
    fol visited (Record b fields) =
      let f (s, ty) = fol visited ty >>= return . (s,)
      in mapM f fields >>= return . Record b
    fol visited (Arrow tDom tCod) = do
		tDom' <- fol visited tDom
		tCod' <- fol visited tCod
		return $ Arrow tDom' tCod'
    fol visited (Union t1 t2) = do
		t1' <- fol visited t1
		t2' <- fol visited t2
		return $ union t1 t2
    fol visited (Forall u ty) = fol visited ty >>= return . Forall u
    fol visited (Intersect t1 t2) = do
		t1' <- fol visited t1
		t2' <- fol visited t2
		return $ Intersect t1 t2
    fol _ t = return t

free :: Type -> Infer Bool
free ty =
  follow ty >>= \case
    TypeVar _ -> return True
    _         -> return False

makeBindings :: Identifier -> [Type] -> Infer Bindings
makeBindings s types = do
  argOrd <- argumentOrder
  case Map.lookup (stringOf s) argOrd of
    Just argOrd -> return $ Map.fromList $ List.zip (Map.elems argOrd) types
    Nothing -> return Map.empty

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

isQuantified :: UniqueInt -> Type -> Infer Bool
isQuantified u ty = isQuant ty
  where
    isQuant (Forall u' ty) = do
	  t <- follow (TypeVar u')
	  t' <- follow (TypeVar u)
	  if t == t' then return True else isQuant ty
    isQuant (Arrow t1 t2) = isQuant t1 `or` isQuant t2
    isQuant (Union t1 t2) = isQuant t1 `or` isQuant t2
    isQuant (Tuple tys) = anyM isQuant tys
    isQuant (Record _ fields) = anyM (isQuant . snd) fields
    isQuant (Array ty) = isQuant ty
    isQuant (Intersect t1 t2) = isQuant t1 `or` isQuant t2
    isQuant _ = return False
    or = liftM2 (||)

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

local :: Infer a -> Infer (a, Substitution, Env, ArgOrd)
local infer =
  do env <- environment
     argOrd <- argumentOrder
     subst <- substitution
     r <- infer
     modifyEnv (const env)
     modifyArgOrd (const argOrd)
     modifySubst (const subst)
     return (r, subst, env, argOrd)

makeForall :: Type -> Type -> Infer Type
makeForall ty1 ty2 = do
  ty1' <- follow ty1
  foldrM make ty2 (typevars ty1')
  where make u ty = do
          isquant <- isQuantified u ty
          isfree <- free (TypeVar u)
          if isquant || not isfree then follow ty
          else do
          TypeVar u' <- lift mkTypeVar
          ty' <- follow ty
          return $ Forall u' (rename u' u ty')
