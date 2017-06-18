{-# LANGUAGE TupleSections, LambdaCase, GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module TypeUtils where
import Control.Arrow
import Control.Monad
import Control.Monad.Loops
import Data.Ord
import Data.Foldable
import Control.Monad.State.Lazy
import Prelude hiding (lookup)
import qualified Data.Map as Map
import Control.Monad.Writer
import Data.Map (Map, (!))
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.List as List
import Hash
import TypedAst
import TTypes
import Unique

type Substitution = Map Identifier TType
type Env = Map String (UniqueInt, TType)
type Bindings = Map Identifier TType
type Trace = Set Identifier

data InferSt = InferSt { subst :: Substitution
                       , env :: Env }

emptySt :: InferSt
emptySt =
  InferSt { subst = Map.empty
          , env = Map.empty }

newtype Infer a = Infer (StateT InferSt IO a)
  deriving (Functor, Applicative, Monad, MonadState InferSt, MonadIO)

runInfer :: Infer a -> InferSt -> IO (a, InferSt)
runInfer (Infer i) = runStateT i

evalInfer :: Infer a -> InferSt -> IO a
evalInfer (Infer i) = evalStateT i

substitution :: Infer Substitution
substitution = fmap subst get

environment :: Infer Env
environment = fmap env get

modifySubst :: (Substitution -> Substitution) -> Infer ()
modifySubst f = modify $ \st -> st { subst = f (subst st) }

modifyEnv :: (Env -> Env) -> Infer ()
modifyEnv f = modify $ \st -> st { env = f (env st) }

modifyEnvM :: (Env -> Infer Env) -> Infer ()
modifyEnvM f = do
  env <- environment
  env' <- f env
  modifyEnv (const env')

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
    fol visited (TTypeVar ident b)
      | Set.member ident visited = return $ TTypeVar ident b
      | otherwise =
        substitution >>= \subst ->
          case Map.lookup ident subst of
            Just t -> fol (Set.insert ident visited) t
            Nothing -> return $ TTypeVar ident b
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
    fol _ t = return t

free :: TType -> Infer Bool
free ty =
  follow ty >>= \case
    TTypeVar {} -> return True
    _          -> return False

makeBindings :: Map Int Identifier -> [TType] -> Bindings
makeBindings a = Map.fromList . List.zip (List.map snd (Map.toAscList a))

instantiate :: TType -> TType -> TType
instantiate t ty =
  let
    inst :: TType -> State (Maybe Identifier) TType
    inst (TForall u ty') =
      get >>= \case
        Nothing -> modify (const (Just u)) >> inst ty'
        Just _ -> TForall u <$> inst ty'
    inst (TArrow tDom tCod) = TArrow <$> inst tDom <*> inst tCod
    inst (TTypeApp t1 t2) = do
      t1' <- inst t1
      t2' <- inst t2
      return $ TTypeApp t1' t2'
    inst (TUnion t1 t2) = TUnion <$> inst t1 <*> inst t2
    inst (TTuple tys) = TTuple <$> mapM inst tys
    inst (TRecord b fields) = TRecord b <$> mapM (\(s, ty) -> (s,) <$> inst ty) fields
    inst (TArray ty) = TArray <$> inst ty
    inst (TTypeVar u b) =
      get >>= \case
        Nothing -> return $ TTypeVar u b
        Just u'
          | u == u'   -> return ty
          | otherwise -> return $ TTypeVar u b
    inst (TMu x ty) = TMu x <$> inst ty
    inst t = return t
  in evalState (inst t) Nothing

lookup :: Bindings -> Identifier -> Infer TType
lookup bind s = do
  env <- environment
  case Map.lookup (stringOf s) env of
    Just (_, ty) -> return ty
    Nothing -> return $ bind ! s

mkTypeVar :: Bool -> IO TType
mkTypeVar b = flip TTypeVar b <$> fromString "t"

makeArrow :: [TType] -> TType -> TType
makeArrow types retTy = List.foldr TArrow retTy types

typevars :: TType -> [Identifier]
typevars (TTypeVar ident _) = [ident]
typevars (TForall ident ty) =
  if ident `elem` uniques then uniques
  else ident : uniques
  where uniques = typevars ty
typevars (TArrow t1 t2) = List.nub $ typevars t1 ++ typevars t2
typevars (TUnion t1 t2) = List.nub $ typevars t1 ++ typevars t2
typevars (TTuple tys) = List.nub $ List.concatMap typevars tys
typevars (TRecord _ fields) = List.nub $ List.concatMap (typevars . snd) fields
typevars (TArray ty) = typevars ty
typevars _ = []

isQuantified :: Identifier -> TType -> Infer Bool
isQuantified ident = isQuant
  where
    isQuant (TForall ident' ty) = do
      t' <- follow (TTypeVar ident' True) -- True / False does not matter here
      t <- follow (TTypeVar ident True)
      if t == t' then return True else isQuant ty
    isQuant (TArrow t1 t2) = isQuant t1 `or` isQuant t2
    isQuant (TUnion t1 t2) = isQuant t1 `or` isQuant t2
    isQuant (TTuple tys) = anyM isQuant tys
    isQuant (TRecord _ fields) = anyM (isQuant . snd) fields
    isQuant (TArray ty) = isQuant ty
    isQuant _ = return False
    or = liftM2 (||)

rename :: Identifier -> Identifier -> TType -> TType
rename new old ty =
  let re (TForall u ty) = TForall u (re ty)
      re (TArrow tDom tCod) = TArrow (re tDom) (re tCod)
      re (TUnion t1 t2) = tunion (re t1) (re t2)
      re (TTuple tys) = TTuple (List.map re tys)
      re (TRecord b fields) = TRecord b (List.map (second re) fields)
      re (TArray ty) = TArray (re ty)
      re (TTypeVar ident b)
        | ident == old = TTypeVar new b
        | otherwise = TTypeVar ident b
      re t = t
  in re ty

zLocal :: Infer a -> Infer (a, InferSt)
zLocal infer =
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
          isfree <- free (TTypeVar u True) -- True / False does not matter here
          if isquant || not isfree then follow ty
          else do
            TTypeVar u' _ <- liftIO $ mkTypeVar True
            ty' <- follow ty
            return $ TForall u' (rename u' u ty')
