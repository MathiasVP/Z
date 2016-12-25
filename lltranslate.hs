{-# LANGUAGE TupleSections, FlexibleContexts, LambdaCase,
             DeriveTraversable, DeriveFunctor #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing
                -fno-warn-unused-binds
                -fno-warn-unused-matches
                -fno-warn-unused-do-bind #-}

module LLTranslate where
  import TypedAst as A
  import Types
  import TypeUtils
  import LLAst
  import Control.Monad.Writer
  import Control.Monad.State
  import qualified Data.List as List
  import qualified Data.Map as Map
  import Data.Map(Map)
  import Data.Maybe
  import Utils
  import Prelude hiding (seq, read)

  type ZIdentifier = Identifier
  type LLIdentifier = Identifier

  data Access = Access { read :: LL LLStatement LLIdentifier
                       , write :: LLIdentifier -> LL LLStatement () }

  type LLState = StateT (Map ZIdentifier Access) IO
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
  translate env = fmap (`evalStateT` Map.empty) (concatMapM (execWriterT . transDecl))

  seq :: [LLStatement] -> LLStatement
  seq = List.foldl1' LLSeq

  transDecl :: TypedDecl -> LL [LLDecl] ()
  transDecl (TTypeDecl name targs ty) = tell [LLTypeDecl name targs ty]
  transDecl (TFunDecl name _ args returnTy stmt) = undefined

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
    tell $ LLCallExpr ident f_ident args_ident
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
  transExpr (TLValue lve, _) = undefined

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
  transStmt (TAssignStatement (Left me) e) = undefined
  transStmt (TAssignStatement (Right (lve, _)) e) =
    case lve of
      TVarExpr s -> return ()
      TFieldAccessExpr lve s -> undefined
      TArrayAccessExpr lve e_idx -> undefined
  transStmt (TMatchStatement e matches) = undefined
  transStmt (TReturnStatement e) = do
    ident <- transExpr e
    tell $ LLReturn ident
  transStmt TBreakStatement = tell LLBreak
  transStmt TContinueStatement = tell LLContinue
  transStmt (TDeclStatement decl) = return ()
