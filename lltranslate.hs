{-# LANGUAGE TupleSections, FlexibleContexts, LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing
                -fno-warn-unused-binds
                -fno-warn-unused-matches
                -fno-warn-unused-do-bind #-}

module LLTranslate where
  import TypedAst as A
  import Types
  import TypeUtils
  import LLAst
  import Control.Monad
  import Control.Monad.Writer
  import Control.Monad.State
  import Control.Arrow
  import qualified Data.List as List
  import qualified Data.Map as Map
  import Data.Map(Map, (!))
  import Data.Maybe
  import Utils
  import Prelude hiding (seq, read)

  type ZIdentifier = Identifier
  type LLIdentifier = Identifier

  data Access = Access { read :: LL LLStatement LLIdentifier
                       , write :: LLIdentifier -> LL LLStatement () }

  instance Show Access where
    show _ = "Access"

  type LLState = StateT (Map ZIdentifier Access, Env) IO
  type LL a b = WriterT a LLState b

  execLL :: Monoid c => LL a b -> LL c a
  execLL a = do
    st <- get
    (a', st') <- liftIO $ runStateT (execWriterT a) st
    put st'
    return a'

  runLL :: Monoid c => LL a b -> LL c (b, a)
  runLL a = do
    st <- get
    (a', st') <- liftIO $ runStateT (runWriterT a) st
    put st'
    return a'

  translate :: Env -> [TypedDecl] -> IO [LLDecl]
  translate env = fmap (`evalStateT` (Map.empty, env)) (concatMapM (execWriterT . transDecl))

  seq :: [LLStatement] -> LLStatement
  seq = List.foldl1' LLSeq

  transDecl :: TypedDecl -> LL [LLDecl] ()
  transDecl (name, TTypeDecl ty) = tell [LLTypeDecl name ty]
  transDecl (name, TFunDecl tyargs args returnTy stmt) = do
    (args', init_args) <- runLL $ mapM (\(n, me) -> do
      t <- liftIO $ fromString ("arg_" ++ show n)
      stmt <- execLL $ go me Access { read = return t, write = tell . LLAssign t }
      tell stmt
      return t) (List.zip [0..] args)
    stmt' <- execLL (transStmt stmt)
    tell [LLFunDecl name args' returnTy (init_args `mappend` stmt')]
    where
      go :: TypedMatchExpr -> Access -> LL LLStatement LLIdentifier
      go (TTupleMatchExpr mes, _) acc = do
        t_tuple <- read acc
        mapM_ (\(idx, me) ->
               go me Access {
                       read = do
                         t <- liftIO $ fromString "t_tuple_read"
                         tell $ LLPred (IsTuple $ List.length mes) t_tuple
                                  (LLGetProj t t_tuple idx)
                                  (LLInternalExpr Nothing "bind_error_callback" [])
                         return t,
                        write = error "Cannot modify tuple" })
              (List.zip [0..] mes)
        return t_tuple
      go (TListMatchExpr mes, _) acc = do
        t_list <- read acc
        mapM_ (\(idx, me) ->
         go me Access {
                 read = do
                   t <- liftIO $ fromString "t_list_read"
                   t_idx <- liftIO $ fromString "t_idx"
                   tell $ LLPred (IsList $ List.length mes) t_list
                            (LLLitExpr t_idx (IntLit idx) `mappend`
                             LLGetIdx t t_list t_idx)
                            (LLInternalExpr Nothing "bind_error_callback" [])
                   return t,
                  write = \ident -> do
                    t_idx <- liftIO $ fromString "t_idx"
                    tell $ LLLitExpr t_idx (IntLit idx)
                    tell $ LLSetIdx t_list t_idx ident })
          (List.zip [0..] mes)
        return t_list
      go (TRecordMatchExpr fields, _) acc = do
        t_rec <- read acc
        mapM_ (\(idx, (s, me)) ->
          go me Access {
                  read = do
                           t <- liftIO $ fromString "t_rec_read"
                           tell $
                             LLPred IsRecord t_rec
                               (LLPred (HasField s) t_rec
                                 (LLGetField t t_rec s)
                                 (LLInternalExpr Nothing "bind_error_callback" []))
                               (LLInternalExpr Nothing "bind_error_callback" [])
                           return t,
                          write = tell . LLSetField t_rec s })
          (List.zip [0..] fields)
        return t_rec
      go (TVarMatch s, _) acc = do
        modify (first $ Map.insert s acc)
        return s
      go (TIntMatchExpr n, _) acc = do
        t_num <- read acc
        tell $ LLPred (IsInt n) t_num LLNop
                 (LLInternalExpr Nothing "bind_error_callback" [])
        return t_num
      go (TStringMatchExpr s, _) acc = do
        t_str <- read acc
        tell $ LLPred (IsString s) t_str LLNop
                 (LLInternalExpr Nothing "bind_error_callback" [])
        return t_str
      go (TBoolMatchExpr b, _) acc = do
        t_bool <- read acc
        tell $ LLPred (IsBool b) t_bool LLNop
                 (LLInternalExpr Nothing "bind_error_callback" [])
        return t_bool

  transLval :: TypedLValueExpr -> LL LLStatement LLIdentifier
  transLval (TVarExpr ident, _) =
    gets ((! ident) . fst) >>= read
  transLval (TFieldAccessExpr lve' s, _) = do
    x <- transLval lve'
    ident <- liftIO $ fromString "t_field_access"
    tell $ LLGetField ident x s
    return ident
  transLval (TArrayAccessExpr lve' e, _) = do
    x <- transLval lve'
    idx <- transExpr e
    ident <- liftIO $ fromString "t_array_access"
    tell $ LLGetIdx ident x idx
    return ident

  transExpr :: TypedExpr -> LL LLStatement Identifier
  transExpr (TIntExpr n, _) = do
    ident <- liftIO $ fromString "t_int"
    tell $ LLLitExpr ident (IntLit n)
    return ident
  transExpr (TRealExpr d, _) = do
    ident <- liftIO $ fromString "t_real"
    tell $ LLLitExpr ident (RealLit d)
    return ident
  transExpr (TBoolExpr b, _) = do
    ident <- liftIO $ fromString "t_bool"
    tell $ LLLitExpr ident (BoolLit b)
    return ident
  transExpr (TStringExpr s, _) = do
    ident <- liftIO $ fromString "t_str"
    tell $ LLLitExpr ident (StringLit s)
    return ident
  transExpr (TOrExpr e1 e2, _) = do
    [ident1, ident2] <- mapM transExpr [e1, e2]
    ident <- liftIO $ fromString "t_or"
    tell $ LLBinOp Or ident ident1 ident2
    return ident
  transExpr (TAndExpr e1 e2, _) = do
    [ident1, ident2] <- mapM transExpr [e1, e2]
    ident <- liftIO $ fromString "t_and"
    tell $ LLBinOp And ident ident1 ident2
    return ident
  transExpr (TEqExpr e1 e2, _) = do
    [ident1, ident2] <- mapM transExpr [e1, e2]
    ident <- liftIO $ fromString "t_eq"
    tell $ LLBinOp Eq ident ident1 ident2
    return ident
  transExpr (TNeqExpr e1 e2, _) = do
    [ident1, ident2] <- mapM transExpr [e1, e2]
    ident <- liftIO $ fromString "t_neq"
    tell $ LLBinOp Neq ident ident1 ident2
    return ident
  transExpr (TLtExpr e1 e2, _) = do
    [ident1, ident2] <- mapM transExpr [e1, e2]
    ident <- liftIO $ fromString "t_lt"
    tell $ LLBinOp Lt ident ident1 ident2
    return ident
  transExpr (TGtExpr e1 e2, _) = do
    [ident1, ident2] <- mapM transExpr [e1, e2]
    ident <- liftIO $ fromString "t_gt"
    tell $ LLBinOp Gt ident ident1 ident2
    return ident
  transExpr (TLeExpr e1 e2, _) = do
    [ident1, ident2] <- mapM transExpr [e1, e2]
    ident <- liftIO $ fromString "t_le"
    tell $ LLBinOp Le ident ident1 ident2
    return ident
  transExpr (TGeExpr e1 e2, _) = do
    [ident1, ident2] <- mapM transExpr [e1, e2]
    ident <- liftIO $ fromString "t_ge"
    tell $ LLBinOp Ge ident ident1 ident2
    return ident
  transExpr (TAddExpr e1 e2, _) = do
    [ident1, ident2] <- mapM transExpr [e1, e2]
    ident <- liftIO $ fromString "t_add"
    tell $ LLBinOp Add ident ident1 ident2
    return ident
  transExpr (TSubExpr e1 e2, _) = do
    [ident1, ident2] <- mapM transExpr [e1, e2]
    ident <- liftIO $ fromString "t_sub"
    tell $ LLBinOp Sub ident ident1 ident2
    return ident
  transExpr (TMultExpr e1 e2, _) = do
    [ident1, ident2] <- mapM transExpr [e1, e2]
    ident <- liftIO $ fromString "t_mult"
    tell $ LLBinOp Mult ident ident1 ident2
    return ident
  transExpr (TDivExpr e1 e2, _) = do
    [ident1, ident2] <- mapM transExpr [e1, e2]
    ident <- liftIO $ fromString "t_div"
    tell $ LLBinOp Div ident ident1 ident2
    return ident
  transExpr (TUnaryMinusExpr e, _) = do
    ident' <- transExpr e
    ident <- liftIO $ fromString "t_uminus"
    tell $ LLUnaryOp UMinus ident ident'
    return ident
  transExpr (TBangExpr e, _) = do
    ident' <- transExpr e
    ident <- liftIO $ fromString "t_bang"
    tell $ LLUnaryOp Bang ident ident'
    return ident
  transExpr (TCallExpr e1 e2, ty) = do
    let collect (TCallExpr (TCallExpr e1 e2, _) e3, _) = [e1, e2, e3] ++ collect e1
        collect (TCallExpr e1 e2, _) = [e1, e2]
        es = collect (TCallExpr e1 e2, ty)
    f_ident : args_ident <- mapM transExpr es
    ident <- liftIO $ fromString "t_call"
    tell $ LLCallExpr (Just ident) f_ident args_ident
    return ident
  transExpr (TListExpr es, _) = do
    ident <- liftIO $ fromString "t_list"
    idents <- mapM transExpr es
    tell $ LLListExpr ident idents
    return ident
  transExpr (TTupleExpr es, _) = do
    ident <- liftIO $ fromString "t_tuple"
    idents <- mapM transExpr es
    tell $ LLTupleExpr ident idents
    return ident
  transExpr (TRecordExpr fields, _) = do
    ident <- liftIO $ fromString "t_rec"
    fields' <- mapM (\(name, e) -> fmap (name,) (transExpr e)) fields
    tell $ LLRecordExpr ident fields'
    return ident
  transExpr (TLValue lve, _) = transLval lve

  transExpr (TLambdaExpr mes stmt, _) = undefined

  transStmt :: TypedStatement -> LL LLStatement ()
  transStmt (TIfStatement e stmt1 (Just stmt2)) = do
    ident <- transExpr e
    stmt1' <- execLL $ transStmt stmt1
    stmt2' <- execLL $ transStmt stmt2
    tell $ LLIf ident stmt1' stmt2'
  transStmt (TIfStatement e stmt1 Nothing) = do
    ident <- transExpr e
    stmt1' <- execLL $ transStmt stmt1
    tell $ LLIf ident stmt1' LLNop
  transStmt (TWhileStatement e stmt) = do
    (ident, ident_stmt) <- runLL $ transExpr e
    stmt' <- execLL $ transStmt stmt
    tell (LLWhile ident_stmt ident stmt')
  transStmt (TForStatement me e stmt) = undefined
  transStmt (TCompoundStatement stmts) = mapM_ transStmt stmts
  transStmt (TAssignStatement (Left me) e) = do
    res <- transExpr e
    go me res
    where
      go (TTupleMatchExpr mes, _) res = do
        stmt <- execLL $ mapM_ (\(idx, me) -> do
                  ident <- case me of
                             (TVarMatch s, _) -> return s
                             _ -> liftIO $ fromString "t_tuple_match"
                  tell $ LLGetProj ident res idx
                  go me ident
                ) (List.zip [0..] mes)
        tell $ LLPred (IsTuple $ List.length mes) res
               stmt
               (LLInternalExpr Nothing "bind_error_callback" [])
      go (TListMatchExpr mes, _) res = do
        stmt <- execLL $ mapM_ (\(idx, me) -> do
                  ident <- case me of
                             (TVarMatch s, _) -> return s
                             _ -> liftIO $ fromString "t_tuple_match"
                  idx_ident <- liftIO $ fromString "idx_ident"
                  tell $ LLLitExpr idx_ident (IntLit idx)
                  tell $ LLGetIdx ident res idx_ident
                  go me ident
                ) (List.zip [0..] mes)
        tell $ LLPred (IsList $ List.length mes) res
               stmt
               (LLInternalExpr Nothing "bind_error_callback" [])
      go (TRecordMatchExpr fields, _) res = do
        stmt <- execLL $ mapM_ (\(s, me) -> do
                  ident <- case me of
                             (TVarMatch s, _) -> return s
                             _ -> liftIO $ fromString "t_tuple_match"
                  tell $ LLPred (HasField s) res
                           (LLGetField ident res s)
                           (LLInternalExpr Nothing "bind_error_callback" [])
                  go me ident) fields
        tell $ LLPred IsRecord res
               stmt
               (LLInternalExpr Nothing "bind_error_callback" [])
      go (TVarMatch s, _) res =
       modify (first $ Map.insert s
                 Access{read = return s,
                        write = void . tell . LLAssign s})
      go (TIntMatchExpr n, _) res =
        tell $ LLPred (IsInt n) res
                 LLNop
                 (LLInternalExpr Nothing "bind_error_callback" [])
      go (TStringMatchExpr s, _) res =
        tell $ LLPred (IsString s) res
                 LLNop
                 (LLInternalExpr Nothing "bind_error_callback" [])
      go (TBoolMatchExpr b, _) res =
        tell $ LLPred (IsBool b) res
                 LLNop
                 (LLInternalExpr Nothing "bind_error_callback" [])
  transStmt (TAssignStatement (Right (lve, _)) e) = do
    res <- transExpr e
    case lve of
      TVarExpr s ->
        modify (first $ Map.insert s
                  Access{read = return s,
                         write = void . tell . LLAssign s})
      TFieldAccessExpr lve s -> do
        base <- transLval lve
        tell $ LLSetField base s res
        return ()
      TArrayAccessExpr lve e_idx -> do
        base <- transLval lve
        idx <- transExpr e_idx
        tell $ LLSetIdx base idx res
        return ()
  transStmt (TMatchStatement e matches) = undefined
  transStmt (TReturnStatement e) = do
    ident <- transExpr e
    tell $ LLReturn ident
  transStmt TBreakStatement = tell LLBreak
  transStmt TContinueStatement = tell LLContinue
  transStmt (TDeclStatement decl) = return ()
