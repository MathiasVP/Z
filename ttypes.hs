module TTypes where
import qualified Data.List as List
import Hash
import Text.PrettyPrint
import Data.Map()
import Data.Foldable()

data TType
  = TIntType
  | TBoolType
  | TStringType
  | TRealType
  | TNumber
  | TMu Identifier TType
  | TArray TType
  | TTuple [TType]
  | TRecord Bool [(String, TType)]
  | TForall Identifier TType
  | TArrow TType TType
  | TUnion TType TType
  | TTypeVar Identifier
  | TTypeApp TType TType
  | TRef String
  | TError
    deriving (Eq, Ord)

instance Show TType where
  show ty = render (ppTType ty)
  
-------------------------------------------------------
-- Type simplications
-------------------------------------------------------
tcontains :: TType -> TType -> Bool
tcontains TIntType TIntType = True
tcontains TNumber TNumber = True
tcontains TBoolType TBoolType = True
tcontains TStringType TStringType = True
tcontains TRealType TRealType = True
tcontains (TUnion t1 t2) t3
  | t1 == t3 = True
  | t2 == t3 = True
  | otherwise = tcontains t1 t3 || tcontains t1 t3
tcontains (TArrow t1 t2) (TArrow t3 t4) =
  t1 == t3 && t2 == t4
tcontains (TMu u1 ty1) (TMu u2 ty2) =
  u1 == u2 && ty1 == ty2
tcontains (TArray t1) (TArray t2) =
  t1 == t2
tcontains (TTuple tys1) (TTuple tys2)
  | List.length tys1 == List.length tys2 =
     List.all (uncurry tcontains) (List.zip tys1 tys2)
  | otherwise = False
tcontains (TRecord _ fields1) (TRecord _ fields2)
  | List.length fields1 == List.length fields2 =
    List.all (uncurry (==)) (List.zip fields1 fields2)
  | otherwise = False
tcontains (TForall u1 ty1) (TForall u2 ty2)
  | u1 == u2 && ty1 == ty2 = True
  | otherwise = False
tcontains (TForall _ t1) t2 = tcontains t1 t2
tcontains (TTypeVar u1) (TTypeVar u2) =
  u1 == u2
tcontains TError TError = True
tcontains _ _ = False

tunion :: TType -> TType -> TType
tunion t1 (TUnion t2 t3) = (t1 `tunion` t2) `tunion` t3
tunion t1 t2
  | t1 `tcontains` t2 = t1
  | otherwise = TUnion t1 t2

ppIdent :: Identifier -> Doc
ppIdent = text . stringOf

ppIdentWithId :: Identifier -> Doc
ppIdentWithId ident = text (stringOf ident ++ show (idOf ident))

commaSep :: [Doc] -> Doc
commaSep xs = hsep (punctuate (char ',') xs)

ppTType :: TType -> Doc
ppTType TIntType = text "Int"
ppTType TBoolType = text "Bool"
ppTType TStringType = text "String"
ppTType TRealType = text "Real"
ppTType TNumber = text "Number"
ppTType (TMu ident ty) =
  text "μ" <+> ppIdentWithId ident <> char '.' <+> ppTType ty
ppTType (TArray ty) = brackets $ ppTType ty
ppTType (TTuple tys) = parens $ commaSep $ List.map ppTType tys
ppTType (TRecord _ fields) =
  braces $ commaSep $ List.map (\(name, ty) ->
    text name <+> colon <+> ppTType ty) fields
ppTType (TForall ident ty) =
  parens $ text "∀" <+> ppIdentWithId ident <> char '.' <+> ppTType ty
ppTType (TArrow ty1 ty2) = ppTType ty1 <+> text "->" <+> ppTType ty2
ppTType (TUnion ty1 ty2) = ppTType ty1 <+> char '|' <+> ppTType ty2
ppTType (TTypeVar ident) = ppIdentWithId ident
ppTType (TTypeApp ty1 ty2) = parens (ppTType ty1) <+> parens (ppTType ty2)
ppTType (TRef name) = text name
ppTType TError = text "Error"
