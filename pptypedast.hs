module PPTypedAst(ppAst) where

import Text.PrettyPrint
import TypedAst
import TTypes
import Data.List as List

ppAst :: [TypedDecl] -> String
ppAst decls = render $ vcat (List.map ppTypedDecl decls)

ppIdent :: Identifier -> Doc
ppIdent = text . stringOf

commaSep :: [Doc] -> Doc
commaSep xs = hsep (punctuate (char ',') xs)

ppTypedDeclData :: TypedDeclData -> Doc
ppTypedDeclData (TTypeDecl ty) =
  ppTType ty
ppTypedDeclData (TFunDecl [] tmes retTy body) =
  parens (hsep (List.map ppTypedMatchExpr tmes)) <+>
  text "->" <+> ppTType retTy <+> equals $$ ppTypedStatement body
ppTypedDeclData (TFunDecl tyargs tmes retTy body) =
  char '<' <> commaSep (List.map ppIdent tyargs) <> char '>' <+>
  parens (hsep (List.map ppTypedMatchExpr tmes)) <+>
  text "->" <+> ppTType retTy <+> equals $$ ppTypedStatement body

ppTypedMatchExpr :: TypedMatchExpr -> Doc
ppTypedMatchExpr (TTupleMatchExpr tmexprs, _) =
  parens $ commaSep $ List.map ppTypedMatchExpr tmexprs
ppTypedMatchExpr (TListMatchExpr tmexprs, _) =
  brackets $ commaSep $ List.map ppTypedMatchExpr tmexprs
ppTypedMatchExpr (TRecordMatchExpr fields, _) =
  braces $ commaSep (List.map (\(name, tmexpr) ->
    text name <+> equals <+> ppTypedMatchExpr tmexpr) fields)
ppTypedMatchExpr (TVarMatch ident, ty) =
  text "(" <> ppIdent ident <+> colon <+> ppTType ty <> text ")"
ppTypedMatchExpr (TIntMatchExpr n, _) = text $ show n
ppTypedMatchExpr (TStringMatchExpr s, _) = text "\"" <> text s <> text "\""
ppTypedMatchExpr (TBoolMatchExpr b, _) = text $ show b

ppTypedStatement :: TypedStatement -> Doc
ppTypedStatement (TIfStatement texpr thenStmt (Just elseStmt)) =
  text "if" <+> ppTypedExpr texpr <+> char ':' $$
    nest 2 (ppTypedStatement thenStmt) $$
  text "else" $$ nest 2 (ppTypedStatement elseStmt)
ppTypedStatement (TIfStatement texpr thenStmt Nothing) =
  text "if" <+> ppTypedExpr texpr <+> char ':' $$
    nest 2 (ppTypedStatement thenStmt)
ppTypedStatement (TWhileStatement texpr body) =
  text "while" <+> ppTypedExpr texpr $$ nest 2 (ppTypedStatement body)
ppTypedStatement (TForStatement tmexpr texpr body) =
  text "for" <+> ppTypedMatchExpr tmexpr <+> text "in" <+>
  ppTypedExpr texpr <+> char ':' $$
    nest 2 (ppTypedStatement body)
ppTypedStatement (TCompoundStatement stmts) =
  braces $ vcat (List.map ppTypedStatement stmts)
ppTypedStatement (TAssignStatement lhs texpr) =
  either ppTypedMatchExpr ppTypedLValueExpr lhs <+>
  char '=' <+> ppTypedExpr texpr
ppTypedStatement (TMatchStatement texpr matches) =
  text "match" <+> ppTypedExpr texpr <+> char ':' $$
  vcat (List.map (\(tmexpr, stmt) -> ppTypedMatchExpr tmexpr <+>
  text "=>" $$ nest 2 (ppTypedStatement stmt)) matches)
ppTypedStatement (TReturnStatement texpr) = text "return" <+> ppTypedExpr texpr
ppTypedStatement TBreakStatement = text "break"
ppTypedStatement TContinueStatement = text "continue"
ppTypedStatement (TDeclStatement tdecl) = ppTypedDecl tdecl

ppTypedDecl :: TypedDecl -> Doc
ppTypedDecl (ident, decl@TTypeDecl{}) =
  text "type" <+> ppIdent ident <+> char '=' <+> ppTypedDeclData decl
ppTypedDecl (ident, decl@TFunDecl{}) =
  text "fun" <+> ppIdent ident <+> ppTypedDeclData decl

ppTypedLValueExpr :: TypedLValueExpr -> Doc
ppTypedLValueExpr (TVarExpr ident, ty) =
  text "(" <> ppIdent ident <+> colon <+> ppTType ty <> text ")"
ppTypedLValueExpr (TFieldAccessExpr tlve name, ty) =
  ppTypedLValueExpr tlve <+> char '.' <+> text name <+> colon <+> ppTType ty
ppTypedLValueExpr (TArrayAccessExpr tlve texpr, ty) =
  ppTypedLValueExpr tlve <+> brackets (ppTypedExpr texpr) <+> colon <+>
  ppTType ty

between :: TypedExpr -> Doc -> TypedExpr -> Doc
between texpr1 sep texpr2 =
  ppTypedExpr texpr1 <+> sep <+> ppTypedExpr texpr2

ppTypedExpr :: TypedExpr -> Doc
ppTypedExpr (TIntExpr n, _) = text $ show n
ppTypedExpr (TRealExpr d, _) = text $ show d
ppTypedExpr (TBoolExpr b, _) = text $ show b
ppTypedExpr (TStringExpr s, _) = text "\"" <> text s <> text "\""
ppTypedExpr (TOrExpr texpr1 texpr2, _) =
  parens $ between texpr1 (text "or") texpr2
ppTypedExpr (TAndExpr texpr1 texpr2, _) =
  parens $ between texpr1 (text "and") texpr2
ppTypedExpr (TEqExpr texpr1 texpr2, _) =
  parens $ between texpr1 (text "==") texpr2
ppTypedExpr (TNeqExpr texpr1 texpr2, _) =
  parens $ between texpr1 (text "!=") texpr2
ppTypedExpr (TLtExpr texpr1 texpr2, _) =
  parens $ between texpr1 (text "<") texpr2
ppTypedExpr (TGtExpr texpr1 texpr2, _) =
  parens $ between texpr1 (text ">") texpr2
ppTypedExpr (TLeExpr texpr1 texpr2, _) =
  parens $ between texpr1 (text "<=") texpr2
ppTypedExpr (TGeExpr texpr1 texpr2, _) =
  parens $ between texpr1 (text ">=") texpr2
ppTypedExpr (TAddExpr texpr1 texpr2, _) =
  parens $ between texpr1 (text "+") texpr2
ppTypedExpr (TSubExpr texpr1 texpr2, _) =
  parens $ between texpr1 (text "-") texpr2
ppTypedExpr (TMultExpr texpr1 texpr2, _) =
  parens $ between texpr1 (text "*") texpr2
ppTypedExpr (TDivExpr texpr1 texpr2, _) =
  parens $ between texpr1 (text "/") texpr2
ppTypedExpr (TUnaryMinusExpr texpr, _) =
  parens $ text "-" <> ppTypedExpr texpr
ppTypedExpr (TBangExpr texpr, _) =
  parens $ text "!" <> ppTypedExpr texpr
ppTypedExpr (TCallExpr texpr1 texpr2, _) =
  parens $ ppTypedExpr texpr1 <+> ppTypedExpr texpr2
ppTypedExpr (TListExpr texprs, _) =
  brackets $ commaSep (List.map ppTypedExpr texprs)
ppTypedExpr (TTupleExpr texprs, _) =
  parens $ commaSep (List.map ppTypedExpr texprs)
ppTypedExpr (TRecordExpr fields, _) =
  braces $ commaSep (List.map (\(name, texpr) ->
    text name <+> equals <+> ppTypedExpr texpr) fields)
ppTypedExpr (TLValue tlve, _) = ppTypedLValueExpr tlve
ppTypedExpr (TLambdaExpr targs body, _) =
  parens $ text "fn" <+> hsep (List.map ppTypedMatchExpr targs) <+>
    text "=>" $$ nest 2 (ppTypedStatement body)

ppTType :: TType -> Doc
ppTType TIntType = text "Int"
ppTType TBoolType = text "Bool"
ppTType TStringType = text "String"
ppTType TRealType = text "Real"
ppTType (TName ident []) = ppIdent ident
ppTType (TName ident tys) =
  ppIdent ident <> char '<' <> commaSep (List.map ppTType tys) <> char '>'
ppTType (TArray ty) = brackets $ ppTType ty
ppTType (TTuple tys) = parens $ commaSep $ List.map ppTType tys
ppTType (TRecord _ fields) =
  braces $ commaSep $ List.map (\(name, ty) ->
    text name <+> colon <+> ppTType ty) fields
ppTType (TForall ident ty) =
  parens $ text "∀" <+> ppIdent ident <> char '.' <+> ppTType ty
ppTType (TArrow ty1 ty2) = ppTType ty1 <+> text "->" <+> ppTType ty2
ppTType (TUnion ty1 ty2) = ppTType ty1 <+> char '|' <+> ppTType ty2
ppTType (TIntersect ty1 ty2) = ppTType ty1 <+> char '&' <+> ppTType ty2
ppTType (TTypeVar (Identifier (s, u))) = text $ s ++ show u
ppTType (TRef name []) = text name
ppTType (TRef name tys) =
  text name <> char '<' <> commaSep (List.map ppTType tys) <> char '>'
ppTType TError = text "Error"
