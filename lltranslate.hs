{-# LANGUAGE TupleSections, FlexibleContexts, LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing
                -fno-warn-unused-binds
                -fno-warn-unused-matches
                -fno-warn-unused-do-bind #-}

module LLTranslate where
  import TypedAst as A
  import Types
  import TTypes
  import TypeUtils
  import LLAst
  import Data.Foldable
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

  failureCrash :: LLStatement
  failureCrash = LLInternalExpr Nothing "bind_error_callback" []

  transMatchExpr :: LLStatement -> TypedMatchExpr -> Access -> LL LLStatement LLIdentifier
  transMatchExpr failure_stmt (TTupleMatchExpr mes, _) acc = do
    t_tuple <- read acc
    tell $ LLPred (IsTuple $ List.length mes) t_tuple
             LLNop
             failure_stmt
    mapM_ (\(idx, me) ->
      transMatchExpr failure_stmt me Access {
              read = do
                t <- liftIO $ fromString "t_tuple_read"
                tell $ LLGetProj t t_tuple idx
                return t,
              write = error "BUG: Cannot modify tuple" })
     (List.zip [0..] mes)
    return t_tuple
  transMatchExpr failure_stmt (TListMatchExpr mes, _) acc = do
    t_list <- read acc
    tell $ LLPred IsList t_list
           (LLPred (HasLength $ List.length mes) t_list LLNop failure_stmt)
           failure_stmt
    mapM_ (\(idx, me) ->
     transMatchExpr failure_stmt me Access {
             read = do
                t <- liftIO $ fromString "t_list_read"
                t_idx <- liftIO $ fromString "t_idx"
                tell $ LLLitExpr t_idx (IntLit idx)
                tell $ LLGetIdx t t_list t_idx
                return t,
              write = \ident -> do
                t_idx <- liftIO $ fromString "t_idx"
                tell $ LLLitExpr t_idx (IntLit idx)
                tell $ LLSetIdx t_list t_idx ident })
      (List.zip [0..] mes)
    return t_list
  transMatchExpr failure_stmt (TRecordMatchExpr fields, _) acc = do
    t_rec <- read acc
    tell $ LLPred IsRecord t_rec LLNop failure_stmt
    mapM_ (\(idx, (s, me)) -> do
      tell $ LLPred (HasField s) t_rec LLNop failure_stmt
      transMatchExpr failure_stmt me Access {
              read = do
                t <- liftIO $ fromString "t_rec_read"
                tell $ LLGetField t t_rec s
                return t,
              write = tell . LLSetField t_rec s })
      (List.zip [0..] fields)
    return t_rec
  transMatchExpr failure_stmt (TVarMatch s, ty) acc = do
    ident <- read acc
    verifyType ident failure_stmt ty
    modify (first $ Map.insert s acc)
    return s
    where
        verifyType ident failure_stmt TIntType =
          tell $ LLPred IsInt ident LLNop failure_stmt
        verifyType ident failure_stmt TBoolType =
          tell $ LLPred IsBool ident LLNop failure_stmt
        verifyType ident failure_stmt TRealType =
          tell $ LLPred IsReal ident LLNop failure_stmt
        verifyType ident failure_stmt TStringType =
          tell $ LLPred IsString ident LLNop failure_stmt
        verifyType ident failure_stmt (TUnion t1 t2) = do
          test1 <- execLL $ verifyType ident failure_stmt t1
          verifyType ident test1 t2
        verifyType ident failure_stmt (TTuple tys) = do
          test <- execLL $ mapM_ (\(idx, ty) -> do
                            t <- liftIO $ fromString $
                                    "t_tuple_proj" ++ show idx
                            tell $ LLGetProj t ident idx
                            verifyType t failure_stmt ty) (List.zip [0..] tys)
          tell $ LLPred (IsTuple $ List.length tys) ident test failure_stmt

  transMatchExpr failure_stmt (TIntMatchExpr n, _) acc = do
    t_num <- read acc
    t_res <- liftIO $ fromString "t_int_match"
    ident_n <- liftIO $ fromString $ "t_" ++ show n
    tell $ LLPred IsInt t_num
           (mconcat [LLLitExpr ident_n (IntLit n),
                     LLBinOp Eq t_res t_num ident_n,
                     LLIf t_res LLNop failure_stmt])
           failure_stmt
    return t_num
  transMatchExpr failure_stmt (TStringMatchExpr s, _) acc = do
    t_str <- read acc
    t_res <- liftIO $ fromString "t_str_match"
    ident_n <- liftIO $ fromString "t_str"
    tell $ LLPred IsString t_str
           (mconcat [LLLitExpr ident_n (StringLit s),
                     LLBinOp Eq t_res t_str ident_n,
                     LLIf t_res LLNop failure_stmt])
           failure_stmt
    return t_str
  transMatchExpr failure_stmt (TBoolMatchExpr b, _) acc = do
    t_bool <- read acc
    t_res <- liftIO $ fromString "t_bool_match"
    ident_n <- liftIO $ fromString "t_bool"
    tell $ LLPred IsBool t_bool
           (mconcat [LLLitExpr ident_n (BoolLit b),
                     LLBinOp Eq t_res t_bool ident_n,
                     LLIf t_res LLNop failure_stmt])
           failure_stmt
    return t_bool

  transDecl :: TypedDecl -> LL [LLDecl] ()
  transDecl (name, TTypeDecl ty) = tell [LLTypeDecl name ty]
  transDecl (name, TFunDecl tyargs args ty stmt) = do
    (args', init_args) <- runLL $ mapM (\(n, me) -> do
      t <- liftIO $ fromString ("arg_" ++ show n)
      stmt <- execLL $ transMatchExpr failureCrash me
                         Access { read = return t, write = tell . LLAssign t }
      tell stmt
      return t) (List.zip [0..] args)
    stmt' <- execLL (transStmt stmt)
    modify $ second $ Map.insert (stringOf name) (idOf name, ty)
    modify $ first $ Map.insert name
      Access { read = return name,
               write = error "BUG: Cannot write to function" }
    tell [LLFunDecl name args' ty (init_args `mappend` stmt')]

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
  transExpr (TCallExpr e1 e2, ty) = error "TODO"
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

  transExpr (TLambdaExpr mes stmt, ty) = do
    (args', init_args) <- runLL $ mapM (\(n, me) -> do
      t <- liftIO $ fromString ("arg_" ++ show n)
      stmt <- execLL $ transMatchExpr failureCrash me
                         Access { read = return t, write = tell . LLAssign t }
      tell stmt
      return t) (List.zip [0..] mes)
    stmt' <- execLL (transStmt stmt)
    func <- liftIO $ fromString "fun"
    tell $ LLDeclare (LLFunDecl func args' ty (init_args `mappend` stmt'))
    return func

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
  transStmt (TForStatement me e stmt) = do
    (list_ident, list_init_stmt) <- runLL $ transExpr e
    t <- liftIO $ fromString "t_loop_var"
    t_stmt <- execLL $ transMatchExpr failureCrash me
                             Access{ read = return t,
                                     write = tell . LLAssign t}
    stmt' <- execLL $ transStmt stmt
    tell list_init_stmt
    tell $ LLFor t_stmt t list_ident stmt'
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
                  go me ident) (List.zip [0..] mes)
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
                  go me ident) (List.zip [0..] mes)
        tell $ LLPred IsList res
               (LLPred (HasLength $ List.length mes) res
                 stmt
                 (LLInternalExpr Nothing "bind_error_callback" []))
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
      go (TVarMatch s, _) res = do
       modify (first $ Map.insert s
                 Access{read = return s,
                        write = tell . LLAssign s})
       tell $ LLAssign s res
      go (TIntMatchExpr n, _) res = do
        ident_test <- liftIO $ fromString "t_int_match"
        ident_n <- liftIO $ fromString $ "t_" ++ show n
        let error_bind_callback =
              LLInternalExpr Nothing "bind_error_callback" []
        tell $ LLPred IsInt res
                 (mconcat [LLLitExpr ident_n (IntLit n),
                           LLBinOp Eq ident_test res ident_n,
                           LLIf ident_test LLNop error_bind_callback])
                 error_bind_callback
      go (TStringMatchExpr s, _) res = do
        ident_test <- liftIO $ fromString "t_str_match"
        ident_str <- liftIO $ fromString "t_str"
        let error_bind_callback =
              LLInternalExpr Nothing "bind_error_callback" []
        tell $ LLPred IsString res
                 (mconcat [LLLitExpr ident_str (StringLit s),
                           LLBinOp Eq ident_test res ident_str,
                           LLIf ident_test LLNop error_bind_callback])
                 error_bind_callback
      go (TBoolMatchExpr b, _) res = do
        ident_test <- liftIO $ fromString "t_bool_match"
        ident_bool <- liftIO $ fromString $ "t_bool_" ++ show b
        let error_bind_callback =
              LLInternalExpr Nothing "bind_error_callback" []
        tell $ LLPred IsBool res
                 (mconcat [LLLitExpr ident_bool (BoolLit b),
                           LLBinOp Eq ident_test res ident_bool,
                           LLIf ident_test LLNop error_bind_callback])
                 error_bind_callback
  transStmt (TAssignStatement (Right (lve, _)) e) = do
    res <- transExpr e
    case lve of
      TVarExpr s ->
        modify (first $ Map.insert s
                  Access{read = return s,
                         write = tell . LLAssign s})
      TFieldAccessExpr lve s -> do
        base <- transLval lve
        tell $ LLSetField base s res
      TArrayAccessExpr lve e_idx -> do
        base <- transLval lve
        idx <- transExpr e_idx
        tell $ LLSetIdx base idx res
  transStmt (TMatchStatement e matches) = do
    (ident, ident_stmt) <- runLL $ transExpr e
    tell ident_stmt
    stmts <- mapM (onMatch ident) matches
    tell $ LLMatch stmts
    where
      onMatch ident (me, stmt) = do
        test <- execLL $ transMatchExpr LLNext me
                           Access{ read = return ident,
                                   write = tell . LLAssign ident }
        stmt' <- execLL $ transStmt stmt
        return (test `mappend` stmt')
  transStmt (TReturnStatement e) = do
    ident <- transExpr e
    tell $ LLReturn ident
  transStmt TBreakStatement = tell LLBreak
  transStmt TContinueStatement = tell LLContinue
  transStmt (TDeclStatement decl) = do
    decls <- execLL $ transDecl decl
    mapM_ (tell . LLDeclare) decls
