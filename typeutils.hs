{-# LANGUAGE TupleSections, LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module TypeUtils where
import Control.Arrow
import Control.Monad
import Control.Monad.Loops
import Data.Ord
import Data.Foldable
import Control.Monad.State.Lazy
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.List as List
import TypedAst
import TTypes
import Unique

type Substitution = Map Identifier TType
type Env = Map String (UniqueInt, TType)
type ArgOrd = Map Identifier (Map Int Identifier)
type Bindings = Map Identifier TType
type Trace = Set Identifier

data FunctionInfo
  = FunctionInfo { name :: Identifier
                  , targs :: [Identifier]
                  , args :: [TypedMatchExpr]
                  , funty :: TType
                  , body :: TypedStatement }
  deriving Show

data InferSt = InferSt { subst :: Substitution
                       , env :: Env
                       , argOrd :: ArgOrd
                       , allFuncs :: Map Identifier FunctionInfo }

emptySt :: InferSt
emptySt = InferSt { subst = Map.empty
                  , env = Map.empty
                  , argOrd = Map.empty
                  , allFuncs = Map.empty }

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

addFunc :: Identifier -> [Identifier] -> [TypedMatchExpr]
            -> TType -> TypedStatement -> Infer ()
addFunc name targs mes ty stmt =
  modify $ \st -> st { allFuncs =
    Map.insert name FunctionInfo{ name = name
                                , targs = targs
                                , args = mes
                                , funty = ty
                                , body = stmt} (allFuncs st) }

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

follow :: TType -> Infer TType
follow = fol Set.empty
  where
    fol visited (TTypeVar ident)
      | Set.member ident visited = return $ TTypeVar ident
      | otherwise =
        substitution >>= \subst ->
          case Map.lookup ident subst of
            Just t -> fol (Set.insert ident visited) t
            Nothing -> return $ TTypeVar ident
    fol visited (TArray ty) = fmap TArray (fol visited ty)
    fol visited (TTuple types) = fmap TTuple (mapM (fol visited) types)
    fol visited (TRecord b fields) =
      let f (s, ty) = fmap (s,) (fol visited ty)
      in fmap (TRecord b) (mapM f fields)
    fol visited (TArrow tDom tCod) = do
      tDom' <- fol visited tDom
      tCod' <- fol visited tCod
      return $ TArrow tDom' tCod'
    fol visited (TUnion t1 t2) = do
      t1' <- fol visited t1
      t2' <- fol visited t2
      return $ tunion t1' t2'
    fol visited (TForall u ty) = fmap (TForall u) (fol visited ty)
    fol visited (TIntersect t1 t2) = do
      t1' <- fol visited t1
      t2' <- fol visited t2
      return $ TIntersect t1' t2'
    fol _ t = return t

free :: TType -> Infer Bool
free ty =
  follow ty >>= \case
    TTypeVar _ -> return True
    _          -> return False

-- TODO: FIXME
makeBindings :: Identifier -> Bindings -> [TType] -> Infer Bindings
makeBindings s binds types = do
  argOrd <- argumentOrder
  case Map.lookup s argOrd of
    Just a ->
      let binds' = Map.fromList $ List.zip (Map.elems a) types
      in return $
        Map.foldrWithKey (\ident newTy binds ->
         case Map.lookup ident binds of
           Just oldTy -> Map.insert ident (instansiate ident newTy oldTy) binds
           Nothing -> Map.insert ident newTy binds) binds binds'
    Nothing -> return binds

instansiate :: Identifier -> TType -> TType -> TType
instansiate name ty t =
  let inst (TName s [])
        | s == name = ty
        | otherwise = TName s []
      inst (TName s tys) = TName s (List.map inst tys)
      inst (TForall u ty) = TForall u (inst ty)
      inst (TArrow tDom tCod) = TArrow (inst tDom) (inst tCod)
      inst (TUnion t1 t2) = tunion (inst t1) (inst t2)
      inst (TTuple tys) = TTuple (List.map inst tys)
      inst (TRecord b fields) = TRecord b (List.map (second inst) fields)
      inst (TArray ty) = TArray (inst ty)
      inst (TTypeVar u) = TTypeVar u
      inst (TIntersect t1 t2) = tintersect (inst t1) (inst t2)
      inst t = t
  in inst t

instansiates :: TType -> Bindings -> TType
instansiates = Map.foldrWithKey instansiate

mkTypeVar :: IO TType
mkTypeVar = TTypeVar <$> fromString "t"

makeArrow :: [TType] -> TType -> TType
makeArrow types retTy = List.foldr TArrow retTy types

typevars :: TType -> [Identifier]
typevars (TTypeVar ident) = [ident]
typevars (TForall ident ty) =
  if ident `elem` uniques then uniques
  else ident : uniques
  where uniques = typevars ty
typevars (TArrow t1 t2) = List.nub $ typevars t1 ++ typevars t2
typevars (TUnion t1 t2) = List.nub $ typevars t1 ++ typevars t2
typevars (TTuple tys) = List.nub $ List.concatMap typevars tys
typevars (TRecord _ fields) = List.nub $ List.concatMap (typevars . snd) fields
typevars (TArray ty) = typevars ty
typevars (TIntersect t1 t2) = List.nub $ typevars t1 ++ typevars t2
typevars _ = []

isQuantified :: Identifier -> TType -> Infer Bool
isQuantified ident = isQuant
  where
    isQuant (TForall ident' ty) = do
      t' <- follow (TTypeVar ident')
      t <- follow (TTypeVar ident)
      if t == t' then return True else isQuant ty
    isQuant (TArrow t1 t2) = isQuant t1 `or` isQuant t2
    isQuant (TUnion t1 t2) = isQuant t1 `or` isQuant t2
    isQuant (TTuple tys) = anyM isQuant tys
    isQuant (TRecord _ fields) = anyM (isQuant . snd) fields
    isQuant (TArray ty) = isQuant ty
    isQuant (TIntersect t1 t2) = isQuant t1 `or` isQuant t2
    isQuant _ = return False
    or = liftM2 (||)

rename :: Identifier -> Identifier -> TType -> TType
rename new old ty =
  let re (TName s tys) = TName s (List.map re tys)
      re (TForall u ty) = TForall u (re ty)
      re (TArrow tDom tCod) = TArrow (re tDom) (re tCod)
      re (TUnion t1 t2) = tunion (re t1) (re t2)
      re (TTuple tys) = TTuple (List.map re tys)
      re (TRecord b fields) = TRecord b (List.map (second re) fields)
      re (TArray ty) = TArray (re ty)
      re (TTypeVar ident)
        | ident == old = TTypeVar new
        | otherwise = TTypeVar ident
      re (TIntersect t1 t2) = tintersect (re t1) (re t2)
      re t = t
  in re ty

local :: Infer a -> Infer (a, InferSt)
local infer =
  do st <- get
     r <- infer
     st' <- get
     put st
     return (r, st')

makeForall :: TType -> TType -> Infer TType
makeForall ty1 ty2 = do
  ty1' <- follow ty1
  foldrM make ty2 (typevars ty1')
  where make u ty = do
          isquant <- isQuantified u ty
          isfree <- free (TTypeVar u)
          if isquant || not isfree then follow ty
          else do
            TTypeVar u' <- lift mkTypeVar
            ty' <- follow ty
            return $ TForall u' (rename u' u ty')
