{-# LANGUAGE LambdaCase, TupleSections #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Replace where
import TTypes
import TypeUtils
import TypedAst
import Control.Arrow
import Control.Monad.Trans
import Control.Monad.IO.Class
import Control.Monad.State
import Control.Monad.Trans.Either
import qualified Data.Map as Map
import qualified Data.Set as Set
import Hash
import Data.Map()

replaceTypeHelper :: TType -> Maybe String -> Infer TType
replaceTypeHelper ty mself = do
  let replace :: Trace -> TType -> StateT (Maybe Identifier) Infer TType
      replace _ TIntType = return TIntType
      replace _ TNumber = return TNumber
      replace _ TBoolType = return TBoolType
      replace _ TStringType = return TStringType
      replace _ TRealType = return TRealType
      replace trace (TMu ident ty) = do
        ty' <- replace trace ty
        return $ TMu ident ty'
      replace trace (TArray ty) = do
        ty' <- replace trace ty
        return $ TArray ty'
      replace trace (TTuple [ty]) = replace trace ty
      replace trace (TTuple tys) = do
        tys' <- mapM (replace trace) tys
        return $ TTuple tys'
      replace trace (TRecord b fields) = do
        fields' <- mapM field fields
        return $ TRecord b fields'
        where field (s, ty) = fmap (s,) (replace trace ty)
      replace trace (TArrow tDom tCod) = do
        tDom' <- replace trace tDom
        tCod' <- replace trace tCod
        return $ TArrow tDom' tCod'
      replace trace (TUnion t1 t2) = do
        t1' <- replace trace t1
        t2' <- replace trace t2
        return $ TUnion t1' t2'
      replace trace (TRef name) =
        Map.lookup name <$> lift environment >>= \case
          Just (_, TRef s)
            | Just s == mself ->
              do x <- liftIO $ fromString "X"
                 modify $ const (Just x)
                 return (TTypeVar x)
            | otherwise -> replace trace (TRef s)
          Just (_, t) -> return t
          Nothing -> error $ "Undefined type name " ++ name
      replace trace (TForall ident ty) = do
        ty' <- replace trace ty
        return $ TForall ident ty'
      replace trace (TTypeVar ident)
        | Set.member ident trace = return $ TTypeVar ident
        | otherwise = do
          subst <- lift substitution
          case Map.lookup ident subst of
            Just ty -> replace (Set.insert ident trace) ty
            Nothing -> return $ TTypeVar ident
      replace trace (TTypeApp t1 t2) = do
        t1' <- replace trace t1
        t2' <- replace trace t2
        return $ TTypeApp t1' t2'
      replace _ TError = return TError
  do (ty', mself) <- runStateT (replace Set.empty ty) Nothing
     case mself of
       Just self -> return $ TMu self ty'
       Nothing -> return ty'

replaceType :: TType -> Infer TType
replaceType = flip replaceTypeHelper Nothing

replaceDecl :: TypedDecl -> Infer TypedDecl
replaceDecl (ident, td) = fmap (ident, ) (replaceDeclData ident td)

replaceDeclData :: Identifier -> TypedDeclData -> Infer TypedDeclData
replaceDeclData ident td =
  case td of
    TTypeDecl t -> do
      t' <- replaceTypeHelper t (Just (stringOf ident))
      environment >>= liftIO . print
      modifyEnv $ Map.update (Just . second (const t')) (stringOf ident)
      environment >>= liftIO . print
      return $ TTypeDecl t'
    TFunDecl args ty s -> do
      args' <- mapM replaceMatchExpr args
      ty' <- replaceType ty
      s' <- replaceStatement s
      return $ TFunDecl args' ty' s'

replaceMatchExpr :: TypedMatchExpr -> Infer TypedMatchExpr
replaceMatchExpr (tme, ty) =
  let replace (TTupleMatchExpr tmes, ty) = do
        ty' <- replaceType ty
        tmes' <- mapM replace tmes
        return (TTupleMatchExpr tmes', ty')
      replace (TListMatchExpr tmes, ty) = do
        ty' <- replaceType ty
        tmes' <- mapM replace tmes
        return (TListMatchExpr tmes', ty')
      replace (TRecordMatchExpr fields, ty) = do
        ty' <- replaceType ty
        let f (s, tme) = fmap (s, ) (replace tme)
        fields' <- mapM f fields
        return (TRecordMatchExpr fields', ty')
      replace (tme, ty) = fmap (tme, ) (replaceType ty)
  in replace (tme, ty)

replaceStatement :: TypedStatement -> Infer TypedStatement
replaceStatement (TIfStatement te tsTrue tsmElse) = do
  te' <- replaceExpr te
  tsTrue' <- replaceStatement tsTrue
  case tsmElse of
    Nothing -> return $ TIfStatement te' tsTrue' Nothing
    Just tsElse -> do
      tsElse' <- replaceStatement tsElse
      return $ TIfStatement te' tsTrue' (Just tsElse')
replaceStatement (TWhileStatement te ts) = do
  te' <- replaceExpr te
  ts' <- replaceStatement ts
  return $ TWhileStatement te' ts'
replaceStatement (TForStatement tme te ts) = do
  tme' <- replaceMatchExpr tme
  te' <- replaceExpr te
  ts' <- replaceStatement  ts
  return $ TForStatement tme' te' ts'
replaceStatement (TCompoundStatement tss) =
  fmap TCompoundStatement (mapM replaceStatement tss)
replaceStatement (TAssignStatement tme_tlve te) =
  replaceExpr te >>= \te ->
    eitherT (fmap Left . replaceMatchExpr) (fmap Right . replaceLValueExpr)
      (hoistEither tme_tlve) >>= \tme_tlve ->
      return $ TAssignStatement tme_tlve te
replaceStatement (TMatchStatement te actions) = do
  let f (tme, ts) = replaceMatchExpr tme >>= \tme' ->
        fmap (tme',) (replaceStatement ts)
  te' <- replaceExpr te
  actions' <- mapM f actions
  return $ TMatchStatement te' actions'
replaceStatement (TReturnStatement tem) =
  fmap TReturnStatement (replaceExpr tem)
replaceStatement TBreakStatement = return TBreakStatement
replaceStatement TContinueStatement = return TContinueStatement
replaceStatement (TDeclStatement td) = fmap TDeclStatement (replaceDecl td)

replaceExpr :: TypedExpr -> Infer TypedExpr
replaceExpr (TIntExpr n, ty) = do
  ty' <- replaceType ty
  return (TIntExpr n, ty')
replaceExpr (TRealExpr d, ty) = do
  ty' <- replaceType ty
  return (TRealExpr d, ty')
replaceExpr (TBoolExpr b, ty) = do
  ty' <- replaceType ty
  return (TBoolExpr b, ty')
replaceExpr (TStringExpr s, ty) = do
  ty' <- replaceType ty
  return (TStringExpr s, ty')
replaceExpr (TOrExpr te1 te2, ty) = do
  ty' <- replaceType ty
  te1' <- replaceExpr te1
  te2' <- replaceExpr te2
  return (TOrExpr te1' te2', ty')
replaceExpr (TAndExpr te1 te2, ty) = do
  ty' <- replaceType ty
  te1' <- replaceExpr te1
  te2' <- replaceExpr te2
  return (TAndExpr te1' te2', ty')
replaceExpr (TEqExpr te1 te2, ty) = do
  ty' <- replaceType ty
  te1' <- replaceExpr te1
  te2' <- replaceExpr te2
  return (TEqExpr te1' te2', ty')
replaceExpr (TNeqExpr te1 te2, ty) = do
  ty' <- replaceType ty
  te1' <- replaceExpr te1
  te2' <- replaceExpr te2
  return (TNeqExpr te1' te2', ty')
replaceExpr (TLtExpr te1 te2, ty) = do
  ty' <- replaceType ty
  te1' <- replaceExpr te1
  te2' <- replaceExpr te2
  return (TLtExpr te1' te2', ty')
replaceExpr (TGtExpr te1 te2, ty) = do
  ty' <- replaceType ty
  te1' <- replaceExpr te1
  te2' <- replaceExpr te2
  return (TGtExpr te1' te2', ty')
replaceExpr (TLeExpr te1 te2, ty) = do
  ty' <- replaceType ty
  te1' <- replaceExpr te1
  te2' <- replaceExpr te2
  return (TLeExpr te1' te2', ty')
replaceExpr (TGeExpr te1 te2, ty) = do
  ty' <- replaceType ty
  te1' <- replaceExpr te1
  te2' <- replaceExpr te2
  return (TGeExpr te1' te2', ty')
replaceExpr (TAddExpr te1 te2, ty) = do
  ty' <- replaceType ty
  te1' <- replaceExpr te1
  te2' <- replaceExpr te2
  return (TAddExpr te1' te2', ty')
replaceExpr (TSubExpr te1 te2, ty) = do
  ty' <- replaceType ty
  te1' <- replaceExpr te1
  te2' <- replaceExpr te2
  return (TSubExpr te1' te2', ty')
replaceExpr (TMultExpr te1 te2, ty) = do
  ty' <- replaceType ty
  te1' <- replaceExpr te1
  te2' <- replaceExpr te2
  return (TMultExpr te1' te2', ty')
replaceExpr (TDivExpr te1 te2, ty) = do
  ty' <- replaceType ty
  te1' <- replaceExpr te1
  te2' <- replaceExpr te2
  return (TDivExpr te1' te2', ty')
replaceExpr (TUnaryMinusExpr te, ty) = do
  ty' <- replaceType ty
  te' <- replaceExpr te
  return (TUnaryMinusExpr te', ty')
replaceExpr (TBangExpr te, ty) = do
  ty' <- replaceType ty
  te' <- replaceExpr te
  return (TBangExpr te', ty')
replaceExpr (TCallExpr teFun teArg, ty) = do
  teFun' <- replaceExpr teFun
  teArg' <- replaceExpr teArg
  ty' <- replaceType ty
  return (TCallExpr teFun' teArg', ty')
replaceExpr (TListExpr tes, ty) = do
  tes' <- mapM replaceExpr tes
  ty' <- replaceType ty
  return (TListExpr tes', ty')
replaceExpr (TTupleExpr tes, ty) = do
  tes' <- mapM replaceExpr tes
  ty' <- replaceType ty
  return (TTupleExpr tes', ty')
replaceExpr (TRecordExpr fields, ty) = do
  ty' <- replaceType ty
  let f (s, te) = fmap (s,) (replaceExpr te)
  fields' <- mapM f fields
  return (TRecordExpr fields', ty')
replaceExpr (TLValue tlve, ty) = do
  tlve' <- replaceLValueExpr tlve
  ty' <- replaceType ty
  return (TLValue tlve', ty')
replaceExpr (TLambdaExpr tmes ts, ty) = do
  tmes' <- mapM replaceMatchExpr tmes
  ts' <- replaceStatement ts
  ty' <- replaceType ty
  return (TLambdaExpr tmes' ts', ty')

replaceLValueExpr :: TypedLValueExpr -> Infer TypedLValueExpr
replaceLValueExpr (TVarExpr s, ty) = do
  ty' <- replaceType ty
  return (TVarExpr s, ty')
replaceLValueExpr (TFieldAccessExpr tlve s, ty) = do
  ty' <- replaceType ty
  tlve' <- replaceLValueExpr tlve
  return (TFieldAccessExpr tlve' s, ty')
replaceLValueExpr (TArrayAccessExpr tlve te, ty) = do
  ty' <- replaceType ty
  tlve' <- replaceLValueExpr tlve
  te' <- replaceExpr te
  return (TArrayAccessExpr tlve' te', ty')
