module PPLLAst(ppLLAst) where

import Text.PrettyPrint
import TypedAst
import TTypes
import LLAst
import Data.List as List

ppLLAst :: [LLDecl] -> String
ppLLAst decls = render $ vcat (List.map ppLLDecl decls)

ppLLDecl :: LLDecl -> Doc
ppLLDecl (LLTypeDecl ident ty) = text "type" <+>
                                 ppIdentWithId ident <+>
                                 text "=" <+> ppTType ty
ppLLDecl (LLFunDecl ident args retTy stmt) =
  text "fun" <+>
  ppIdentWithId ident <+>
  parens (hsep (List.map ppIdentWithId args)) <+>
  text "=" <+>
  ppLLStmt stmt

ppLit :: Lit -> Doc
ppLit(IntLit n) = text $ show n
ppLit(BoolLit b) = text $ show b
ppLit(StringLit s) = text $ show s
ppLit(RealLit d) = text $ show d

ppBinOp :: BinOp -> Doc
ppBinOp binop =
  case binop of
    Or -> text "or"
    And -> text "and"
    Eq -> text "=="
    Neq -> text "!="
    Lt -> text "<"
    Gt -> text ">"
    Le -> text "<="
    Ge -> text ">="
    Add -> text "+"
    Sub -> text "-"
    Mult -> text "*"
    Div -> text "/"

ppUnaryOp :: UnaryOp -> Doc
ppUnaryOp UMinus = text "-"
ppUnaryOp Bang = text "*"

ppPred :: Pred -> Doc
ppPred(IsTuple n) = text "IsTuple" <+> text (show n)
ppPred IsList = text "IsList"
ppPred (HasLength n) = text "HasLength" <+> text (show n)
ppPred IsRecord = text "IsRecord"
ppPred (HasField s) = text "HasField" <+> text (show s)
ppPred IsInt = text "IsInt"
ppPred IsString = text "IsString"
ppPred IsBool = text "IsBool"

ppLLStmt :: LLStatement -> Doc
ppLLStmt (LLLitExpr ident lit) =
  ppIdentWithId ident <+> text "=" <+> ppLit lit
ppLLStmt (LLBinOp op res lhs rhs) =
    ppIdentWithId res <+> text "=" <+>
    ppIdentWithId lhs <+> ppBinOp op <+> ppIdentWithId rhs
ppLLStmt (LLUnaryOp op res ident) =
  ppIdentWithId res <+> text "=" <+> ppUnaryOp op <+> ppIdentWithId ident
ppLLStmt (LLCallExpr Nothing func args) =
  ppIdentWithId func <+> parens (commaSep (List.map ppIdentWithId args))
ppLLStmt (LLCallExpr (Just res) func args) =
  ppIdentWithId res <+> text "=" <+> ppIdentWithId func <+>
    parens (commaSep $ List.map ppIdentWithId args)
ppLLStmt (LLInternalExpr Nothing func args) =
  text func <+> parens (commaSep (List.map ppIdentWithId args))
ppLLStmt (LLInternalExpr (Just res) func args) =
  ppIdentWithId res <+> text "=" <+> text func <+>
    parens (commaSep $ List.map ppIdentWithId args)
ppLLStmt (LLListExpr res args) =
  ppIdentWithId res <+> text "=" <+>
    brackets (commaSep $ List.map ppIdentWithId args)
ppLLStmt (LLTupleExpr res args) =
    ppIdentWithId res <+> text "=" <+>
      parens (commaSep $ List.map ppIdentWithId args)
ppLLStmt (LLRecordExpr res fields) =
    ppIdentWithId res <+> text "=" <+>
    braces (commaSep $ List.map onField fields)
    where onField (s, ident) = text s <+> text "=" <+> ppIdentWithId ident
ppLLStmt (LLGetIdx res list_ident idx_ident) =
  ppIdentWithId res <+> text "=" <+> ppIdentWithId list_ident <+>
  brackets (ppIdentWithId idx_ident)
ppLLStmt (LLSetIdx list_ident idx_ident ident) =
  ppIdentWithId list_ident <+> brackets (ppIdentWithId idx_ident) <+>
  text "=" <+> ppIdentWithId ident
ppLLStmt (LLGetField res rec_ident s) =
  ppIdentWithId res <+> text "=" <+> ppIdentWithId rec_ident <> text "." <> text s
ppLLStmt (LLSetField rec_ident s ident) =
  ppIdentWithId rec_ident <> text "." <> text s <+> text "=" <+> ppIdentWithId ident
ppLLStmt (LLGetProj res tuple_ident idx) =
  ppIdentWithId res <+> text "=" <+>
  ppIdentWithId tuple_ident <> text "." <> text (show idx)
ppLLStmt (LLAssign res ident) =
  ppIdentWithId res <+> text "=" <+> ppIdentWithId ident
ppLLStmt (LLLambdaExpr res args body) =
  ppIdentWithId res <+> text "=" <+> text "fun " <+>
  parens (hsep (List.map ppIdentWithId args)) <+> text "=>"
  $$ nest 2 (ppLLStmt body)
ppLLStmt (LLIf ident thenStmt elseStmt) =
  text "if" <+> ppIdentWithId ident <+> char ':' $$
    nest 2 (braces $ ppLLStmt thenStmt) $$
  text "else" $$ nest 2 (braces $ ppLLStmt elseStmt)
ppLLStmt (LLPred predicate ident thenStmt elseStmt) =
  ppPred predicate <+> ppIdentWithId ident $$
    nest 2 (braces $ ppLLStmt thenStmt) $$
    nest 2 (braces $ ppLLStmt elseStmt)
ppLLStmt (LLWhile gen_ident ident body) =
  text "while" $$
    nest 2 (ppLLStmt gen_ident $$ ppIdentWithId ident) $$
    nest 2 (ppLLStmt body)
ppLLStmt (LLFor gen_i i list_ident body) =
  text "for" $$
    nest 2 (ppLLStmt gen_i) $$
    nest 2 (ppIdentWithId i <+> text "in" <+> ppIdentWithId list_ident) $$
    nest 2 (ppLLStmt body)
ppLLStmt (LLMatch stmts) =
  text "match" $$
    nest 2 (vcat (List.map ppLLStmt stmts))
ppLLStmt (LLSeq stmt1 stmt2) = ppLLStmt stmt1 $$ ppLLStmt stmt2
ppLLStmt (LLReturn ident) = text "return" <+> ppIdentWithId ident
ppLLStmt LLBreak = text "break"
ppLLStmt LLContinue = text "continue"
ppLLStmt LLNext = text "next"
ppLLStmt (LLDeclare decl) = ppLLDecl decl
ppLLStmt LLNop = text "nop"
