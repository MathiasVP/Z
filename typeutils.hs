{-# LANGUAGE TupleSections, LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module TypeUtils where
import Data.Map (Map)
import Control.Arrow
import Control.Monad
import Control.Monad.Loops
import Data.Ord
import Data.Foldable
import Control.Monad.State.Lazy
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List
import TypedAst()
import Types
import Unique

type Substitution = Map UniqueInt Type
type Env = Map String (UniqueInt, Type)
type ArgOrd = Map String (Map Int String)
type Bindings = Map String Type

data InferSt = InferSt { subst :: Substitution, env :: Env, argOrd :: ArgOrd }

emptySt :: InferSt
emptySt = InferSt { subst = Map.empty
                  , env = Map.empty
                  , argOrd = Map.empty }

type Infer a = StateT InferSt IO a


substitution :: Infer Substitution
substitution = fmap subst get

environment :: Infer Env
environment = fmap env get

argumentOrder :: Infer ArgOrd
argumentOrder = fmap argOrd get

modifySubst :: (Substitution -> Substitution) -> Infer ()
modifySubst f = modify $ \st -> st { subst = f (subst st) }

modifyEnv :: (Env -> Env) -> Infer ()
modifyEnv f = modify $ \st -> st { env = f (env st) }

modifyArgOrd :: (ArgOrd -> ArgOrd) -> Infer ()
modifyArgOrd f = modify $ \st -> st { argOrd = f (argOrd st) }

exprOf :: (a, b) -> a
exprOf = fst

typeOf :: (a, b) -> b
typeOf = snd

normaliseFields :: Ord a => [(a, b)] -> [(a, b)]
normaliseFields = List.sortBy (comparing fst)

equalRecordFields :: Ord b => [(b, b1)] -> [(b, b2)] -> Bool
equalRecordFields fields1 fields2 =
  let f fields = List.map fst (normaliseFields fields)
  in f fields1 == f fields2

follow :: Type -> Infer Type
follow = fol Set.empty
  where
    fol visited (TypeVar u)
      | Set.member u visited = return $ TypeVar u
      | otherwise =
        substitution >>= \subst ->
          case Map.lookup u subst of
            Just t -> fol (Set.insert u visited) t
            Nothing -> return $ TypeVar u
    fol visited (Array ty) = fmap Array (fol visited ty)
    fol visited (Tuple types) = fmap Tuple (mapM (fol visited) types)
    fol visited (Record b fields) =
      let f (s, ty) = fmap (s,) (fol visited ty)
      in fmap (Record b) (mapM f fields)
    fol visited (Arrow tDom tCod) = do
      tDom' <- fol visited tDom
      tCod' <- fol visited tCod
      return $ Arrow tDom' tCod'
    fol visited (Union t1 t2) = do
      t1' <- fol visited t1
      t2' <- fol visited t2
      return $ union t1' t2'
    fol visited (Forall u ty) = fmap (Forall u) (fol visited ty)
    fol visited (Intersect t1 t2) = do
      t1' <- fol visited t1
      t2' <- fol visited t2
      return $ Intersect t1' t2'
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
    Just a -> return $ Map.fromList $ List.zip (Map.elems a) types
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
      inst (Record b fields) = Record b (List.map (second inst) fields)
      inst (Array ty) = Array (inst ty)
      inst (TypeVar u) = TypeVar u
      inst (Intersect t1 t2) = intersect (inst t1) (inst t2)
      inst t = t
  in inst t

instansiates :: Type -> Map String Type -> Type
instansiates = Map.foldrWithKey instansiate

mkTypeVar :: IO Type
mkTypeVar = fmap TypeVar unique

makeArrow :: [Type] -> Type -> Type
makeArrow types retTy = List.foldr Arrow retTy types

typevars :: Type -> [UniqueInt]
typevars (TypeVar u) = [u]
typevars (Forall u ty) =
  if u `elem` uniques then uniques
  else u : uniques
  where uniques = typevars ty
typevars (Arrow t1 t2) = List.nub $ typevars t1 ++ typevars t2
typevars (Union t1 t2) = List.nub $ typevars t1 ++ typevars t2
typevars (Tuple tys) = List.nub $ List.concatMap typevars tys
typevars (Record _ fields) = List.nub $ List.concatMap (typevars . snd) fields
typevars (Array ty) = typevars ty
typevars (Intersect t1 t2) = List.nub $ typevars t1 ++ typevars t2
typevars _ = []

isQuantified :: UniqueInt -> Type -> Infer Bool
isQuantified u = isQuant
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
      re (Record b fields) = Record b (List.map (second re) fields)
      re (Array ty) = Array (re ty)
      re (TypeVar u)
        | u == old = TypeVar new
        | otherwise = TypeVar u
      re (Intersect t1 t2) = intersect (re t1) (re t2)
      re t = t
  in re ty

local :: Infer a -> Infer (a, InferSt)
local infer =
  do env' <- environment
     argOrd' <- argumentOrder
     subst' <- substitution
     r <- infer
     modifyEnv (const env')
     modifyArgOrd (const argOrd')
     modifySubst (const subst')
     return (r, InferSt {env = env', subst = subst', argOrd = argOrd'})

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
