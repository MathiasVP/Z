module Unification where
import qualified Data.Unique as U
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad
import Ast
import TypedAst
import qualified Data.Graph.Inductive as G
import Data.Ord
import qualified Debug.Trace as Debug

type Substitution = Map.Map U.Unique Type
type Env = Map.Map String Type

mkTypeVar :: IO Type  
mkTypeVar = do
  u <- U.newUnique
  return (TypeVar u)

unify :: Type -> Type -> Substitution -> TypeGraph -> IO (Type, Substitution)
unify (Name s1 types1) (Name s2 types2) subst gr = undefined
{-  if s1 == s2 && List.length types1 == List.length types2 then do
    (types, subst') <- unifyPairwise types1 types2 subst gr
    return (Name s1 types, subst')
  else return (Union (Name s1 types1) (Name s2 types2), subst) -}
unify (Name s types) ty subst gr = undefined
unify ty (Name s types) subst gr = undefined
unify (Array t1) (Array t2) subst gr = do
  (t, subst') <- unify t1 t2 subst gr
  return (Array t, subst')
unify (Tuple [t1]) (Tuple [t2]) subst gr = do
  (t, subst') <- unify t1 t2 subst gr
  return (Tuple [t], subst')
unify (Tuple [t1]) t2 subst gr = do
  (t, subst') <- unify t1 t2 subst gr
  return (t, subst')
unify t1 (Tuple [t2]) subst gr = do
  (t, subst') <- unify t1 t2 subst gr
  return (t, subst')
unify (Tuple types1) (Tuple types2) subst gr =
  if List.length types1 == List.length types2 then do
    (types, subst') <- unifyPairwise types1 types2 subst gr
    return (Tuple types, subst')
  else return (Union (Tuple types1) (Tuple types2), subst)
unify (Set t1) (Set t2) subst gr = do
  (t, subst') <- unify t1 t2 subst gr
  return (Set t, subst')
unify (Record fields1) (Record fields2) subst gr = do
  (types, subst') <- unifyPairwise types1 types2 subst gr
  let fields = List.zip names1 types
  if names1 == names2 then
    return (Record fields, subst')
  else return (Union (Record fields1) (Record fields2), subst)
  where fields1' = List.sortBy (comparing fst) fields1
        fields2' = List.sortBy (comparing fst) fields2
        (names1, types1) = List.unzip fields1'
        (names2, types2) = List.unzip fields2'
unify (Arrow tyDom1 tyCod1) (Arrow tyDom2 tyCod2) subst gr = do
  (tyDom, subst') <- unify tyDom1 tyDom2 subst gr
  (tyCod, subst'') <- unify tyCod1 tyCod2 subst' gr
  return (Arrow tyDom tyCod, subst'')
unify (Union t1 t2) (Union t3 t4) subst gr = do
  (t13, subst') <- unify t1 t3 subst gr
  (t24, subst'') <- unify t2 t4 subst' gr
  return (Union t13 t24, subst'')
unify (TypeVar u) (TypeVar u') subst gr =
  case (follow subst (TypeVar u), follow subst (TypeVar u')) of
    (TypeVar u, TypeVar u') -> return (TypeVar u, Map.insert u (TypeVar u') subst)
    (TypeVar u, t) -> return (t, Map.insert u t subst)
    (t, TypeVar u') -> return (t, Map.insert u' t subst)
    (t, t') -> unify t t' subst gr
unify (TypeVar u) t subst gr =
  case follow subst (TypeVar u) of
    TypeVar u -> return (t, Map.insert u t subst)
    t'        -> do (t'', subst') <- unify t t' subst gr
                    return (t'', Map.insert u t'' subst')
unify t (TypeVar u) subst gr = unify (TypeVar u) t subst gr
unify (AllOf ts1) (AllOf ts2) subst gr =
  return (AllOf $ Set.toList $ Set.intersection (Set.fromList ts1) (Set.fromList ts2), subst)
unify (AllOf ts) t subst gr =
  if Set.member t (Set.fromList ts) then
    return (t, subst)
  else
    return (Union (AllOf ts) t, subst)
unify t (AllOf ts) subst gr = unify (AllOf ts) t subst gr
unify t1 t2 subst gr = return (Union t1 t2, subst)

unifyTypes :: [Type] -> Substitution -> TypeGraph -> IO (Type, Substitution)
unifyTypes types subst gr = do
  t <- mkTypeVar
  foldM f (t, subst) types
  where f (ty, subst) ty' =
          unify ty ty' subst gr

unifyPairwise :: [Type] -> [Type] -> Substitution -> TypeGraph -> IO ([Type], Substitution)
unifyPairwise types1 types2 subst gr = do
  let types = List.zip types1 types2
  let f (types, subst) (t1, t2) = do (t, subst') <- unify t1 t2 subst gr
                                     return (t : types, subst')
  (types', subst') <- foldM f ([], subst) types
  return (List.reverse types', subst')

follow :: Substitution -> Type -> Type
follow subst (TypeVar u) =
  case Map.lookup u subst of
    Nothing             -> TypeVar u
    Just (TypeVar u')   -> if u == u' then TypeVar u'
                           else follow subst (TypeVar u')
    Just (Name s types) -> Name s types
    Just (Array ty) -> Array (follow subst ty)
    Just (Tuple types) -> Tuple (List.map (follow subst) types)
    Just (Set ty) -> Set (follow subst ty)
    Just (Record fields) -> let f (s, ty) = (s, follow subst ty)
                            in Record (List.map f fields)
    Just (Arrow tDom tCod) -> Arrow (follow subst tDom) (follow subst tCod)
    Just (Union t1 t2) -> Union (follow subst t1) (follow subst t2)
    Just Error -> Error
    Just (AllOf types) -> AllOf (List.map (follow subst) types)
follow subst t = t
  
unify' :: Type -> Type -> Substitution -> TypeGraph -> Maybe (Type, Substitution)
unify' (Name s1 types1) (Name s2 types2) subst gr@(_, _, _, tmap) =
  case (Map.lookup s1 tmap, Map.lookup s2 tmap) of
    (Just formalmap1, Just formalmap2) ->
      case subtype' formalmap1 formalmap2 (n1, inst1) (n2, inst2) subst gr'' of
        (True, subst') -> Just (Name s1 types1, subst')
        (False, _) -> Nothing
    (_, _) -> Nothing
  where Just n1 = lookupType s1 gr
        Just n2 = lookupType s2 gr
        (gr', nodes1) = List.foldl' f (gr, []) types1
        (gr'', nodes2) = List.foldl' f (gr', []) types2
        f (gr, nodes) ty = (gr', n : nodes)
          where (gr', n) = type2graph ty Map.empty gr
        inst1 = Map.fromList $ List.zip [0..] (List.reverse nodes1)
        inst2 = Map.fromList $ List.zip [0..] (List.reverse nodes2)
unify' (Name s types) ty subst gr@(_, _, _, tmap) =
  case Map.lookup s tmap of
    Just formalmap ->
      case subtype' formalmap Map.empty (n1, inst1) (n2, Map.empty) subst gr'' of
        (True, subst') -> Just (Name s types, subst')
        (False, _) -> Nothing
  where Just n1 = lookupType s gr
        (gr', n2) = type2graph ty Map.empty gr
        (gr'', nodes) = List.foldl' f (gr', []) types
        f (gr, nodes) ty = (gr', n : nodes)
          where (gr', n) = type2graph ty Map.empty gr
        inst1 = Map.fromList $ List.zip [0..] (List.reverse nodes)
unify' ty (Name s types) subst gr@(_, _, _, tmap) =
  case Map.lookup s tmap of
    Just formalmap ->
      case subtype' Map.empty formalmap (n1, Map.empty) (n2, inst2) subst gr'' of
        (True, subst') -> Just (ty, subst')
        (False, _) -> Nothing
  where Just n2 = lookupType s gr
        (gr', n1) = type2graph ty Map.empty gr
        (gr'', nodes) = List.foldl' f (gr', []) types
        f (gr, nodes) ty = (gr', n : nodes)
          where (gr', n) = type2graph ty Map.empty gr
        inst2 = Map.fromList $ List.zip [0..] (List.reverse nodes)
unify' (Array t1) (Array t2) subst gr =
  case unify' t1 t2 subst gr of
    Just (t, subst') -> Just (Array t, subst')
    Nothing -> Nothing
unify' (Tuple [t1]) (Tuple [t2]) subst gr =
  unify' t1 t2 subst gr
unify' (Tuple [t1]) t2 subst gr =
  unify' t1 t2 subst gr
unify' t1 (Tuple [t2]) subst gr =
  unify' t1 t2 subst gr
unify' (Tuple types1) (Tuple types2) subst gr =
  case unifyPairwise' types1 types2 subst gr of
    Just (types, subst') -> Just (Tuple types, subst')
    Nothing -> Nothing
unify' (Set t1) (Set t2) subst gr =
  case unify' t1 t2 subst gr of
    Just (t, subst') -> Just (Set t, subst')
    Nothing -> Nothing
unify' (Record fields1) (Record fields2) subst gr =
  if names1 == names2 then
    case unifyPairwise' types1 types2 subst gr of
      Just (types, subst') ->
        let fields = List.zip names1 types
        in Just (Record fields, subst')
      Nothing -> Nothing
  else Nothing
  where fields1' = List.sortBy (comparing fst) fields1
        fields2' = List.sortBy (comparing fst) fields2
        (names1, types1) = List.unzip fields1'
        (names2, types2) = List.unzip fields2'
unify' (Arrow tyDom1 tyCod1) (Arrow tyDom2 tyCod2) subst gr =
  case unify' tyDom2 tyDom1 subst gr of
    Just (tyDom, subst') ->
      case unify' tyCod1 tyCod2 subst' gr of
        Just (tyCod, subst'') -> Just (Arrow tyDom tyCod, subst'')
        Nothing -> Nothing
    Nothing -> Nothing
unify' (Union t1 t2) (Union t3 t4) subst gr =
  case unify' t1 t3 subst gr of
    Just (t13, subst') ->
      case unify' t2 t4 subst' gr of
        Just (t24, subst'') -> Just (Union t13 t24, subst'')
        Nothing -> Nothing
    Nothing -> Nothing
unify' ty (Union t1 t2) subst gr =
  case unify' ty t1 subst gr of
    Just (t, subst') -> Just (t, subst')
    Nothing -> unify' ty t2 subst gr
unify' (Union t1 t2) ty subst gr =
  case unify' t1 ty subst gr of
    Just (t, subst') -> Just (t, subst')
    Nothing -> unify' t2 ty subst gr
unify' (TypeVar u) (TypeVar u') subst gr =
  case (follow subst (TypeVar u), follow subst (TypeVar u')) of
    (TypeVar u, TypeVar u') -> Just (TypeVar u, Map.insert u (TypeVar u') subst)
    (TypeVar u, t) -> Just (t, Map.insert u t subst)
    (t, TypeVar u') -> Just (t, Map.insert u' t subst)
    (t, t') -> unify' t t' subst gr
unify' (TypeVar u) t subst gr =
  case follow subst (TypeVar u) of
    TypeVar u -> Just (t, Map.insert u t subst)
    t'        -> case unify' t' t subst gr of
                  Just (t'', subst') -> Just (t'', Map.insert u t'' subst')
                  Nothing            -> Nothing
unify' t (TypeVar u) subst gr =
  case follow subst (TypeVar u) of
    TypeVar u -> Just (t, Map.insert u t subst)
    t'        -> case unify' t t' subst gr of
                  Just (t'', subst') -> Just (t'', Map.insert u t'' subst')
                  Nothing            -> Nothing
unify' (AllOf ts1) (AllOf ts2) subst gr =
  Just (AllOf $ Set.toList $ Set.intersection (Set.fromList ts1) (Set.fromList ts2), subst)
unify' (AllOf ts) t subst gr =
  if Set.member t (Set.fromList ts) then
    Just (t, subst)
  else Nothing
unify' t (AllOf ts) subst gr = unify' (AllOf ts) t subst gr
unify' t1 t2 subst gr = Nothing

unifyPairwise' :: [Type] -> [Type] -> Substitution -> TypeGraph -> Maybe ([Type], Substitution)
unifyPairwise' types1 types2 subst gr =
  if List.length types1 /= List.length types2 then
    Nothing
  else List.foldr f (Just ([], subst)) (List.zip types1 types2)
  where f (t1, t2) (Just (types, subst)) =
            case unify' t1 t2 subst gr of
              Just (t, subst') -> (Just (t : types, subst'))
              Nothing -> Nothing
        f _ Nothing = Nothing
        
-------------------------------------------------------
-- Subtype relation <:
-------------------------------------------------------
        
data TypeTag
  = NameTag String
  | NameDefTag String [String]
  | ArrayTag
  | SetTag
  | TupleTag
  | UnionTag
  | ArrowTag
  | RecordTag
  | TypeVarTag U.Unique
  | AllOfTag
  | ErrorTag
  deriving (Show, Eq)

data GraphEdge
  = DefEdge
  | NumEdge Int
  | RecordEdge String
  | InstEdge Int G.Node
  deriving (Show, Eq)
  
instance Ord GraphEdge where
  DefEdge `compare` DefEdge = EQ
  NumEdge n `compare` NumEdge m = n `compare` m
  RecordEdge s1 `compare` RecordEdge s2 = s1 `compare` s2
  InstEdge n n1 `compare` InstEdge m n2
    | n == m    = n1 `compare` n2
    | otherwise = n `compare` m
             
type TypeGraph = (Map.Map String G.Node, Map.Map G.Node String, G.Gr TypeTag GraphEdge, Map.Map String (Map.Map String Int))
type InstType = (G.Node, Map.Map Int G.Node)
type Assumptions = Set.Set (InstType, InstType)

initialAssumptions :: TypeGraph
initialAssumptions =
  (Map.fromList [("Int", 0), ("Real", 1), ("Bool", 2), ("String", 3)],
   Map.fromList [(0, "Int"), (1, "Real"), (2, "Bool"), (3, "String")],
   G.mkGraph [(0, NameTag "Int"), (1, NameTag "Real"), (2, NameTag "Bool"), (3, NameTag "String")] [],
   Map.fromList [("Int", Map.empty), ("Real", Map.empty), ("Bool", Map.empty), ("String", Map.empty)])

lookupType :: String -> TypeGraph -> Maybe G.Node
lookupType name (map, _, _, _) = Map.lookup name map

lookupNode :: G.Node -> TypeGraph -> Maybe String
lookupNode node (_, map', _, _) = Map.lookup node map'

newNode :: TypeTag -> TypeGraph -> (TypeGraph, G.Node)
newNode tag (map, map', gr, tmap) = ((map, map', G.insNode (node, tag) gr, tmap), node)
  where [node] = G.newNodes 1 gr
  
insertName :: String -> [String] -> G.Node -> TypeGraph -> TypeGraph
insertName name args node (map, map', gr, tmap) =
  (Map.insert name node map, Map.insert node name map', gr, Map.insert name (Map.fromList (List.zip args [0..])) tmap)

insertEdge :: G.Node -> G.Node -> GraphEdge -> TypeGraph -> TypeGraph
insertEdge from to label (map, map', gr, tmap) = (map, map', G.insEdge (from, to, label) gr, tmap)

insertNode :: G.Node -> TypeTag -> TypeGraph -> TypeGraph
insertNode node tag (map, map', gr, tmap) = (map, map', G.insNode (node, tag) gr, tmap)

lab :: TypeGraph -> G.Node -> Maybe TypeTag
lab (map, _, gr, _) node = G.lab gr node

lsuc :: G.Node -> TypeGraph -> [(G.Node, GraphEdge)]
lsuc node (_, _, gr, _) = G.lsuc gr node

type2graph :: Type -> Map.Map String G.Node -> TypeGraph -> (TypeGraph, G.Node)
type2graph (Name name args) mapt gr =
  case Map.lookup name mapt of
    Just targetnode ->
      (gr, targetnode)
    Nothing ->
      case lookupType name gr of
        Just targetnode -> (gr'', node)
          where (gr', node) = newNode (NameTag name) gr
                gr'' = List.foldl' f gr' (List.zip [0..] args)
                f gr (n, ty) = insertEdge node targetnode (InstEdge n node') gr'
                  where (gr', node') = type2graph ty mapt gr
type2graph (Tuple tys) mapt gr =
  (List.foldl' f gr' (List.zip [0..] tys), node)
  where (gr', node) = newNode TupleTag gr
        f gr (n, ty) = insertEdge node node' (NumEdge n) gr'
          where (gr', node') = type2graph ty mapt gr
type2graph (Array t) mapt gr = (gr''', node)
  where (gr', node) = newNode ArrayTag gr
        (gr'', node') = type2graph t mapt gr'
        gr''' = insertEdge node node' (NumEdge 0) gr''
type2graph (Set t) mapt gr = (gr''', node)
  where (gr', node) = newNode SetTag gr
        (gr'', node') = type2graph t mapt gr'
        gr''' = insertEdge node node' (NumEdge 0) gr''
type2graph (Union t1 t2) mapt gr = (gr''', node)
  where (gr', node) = newNode UnionTag gr
        (gr1, node1) = type2graph t1 mapt gr'
        (gr2, node2) = type2graph t2 mapt gr1
        gr'' = insertEdge node node1 (NumEdge 0) gr2
        gr''' = insertEdge node node2 (NumEdge 1) gr''
type2graph (Arrow t1 t2) mapt gr = (gr''', node)
  where (gr', node) = newNode ArrowTag gr
        (gr1, node1) = type2graph t1 mapt gr'
        (gr2, node2) = type2graph t2 mapt gr1
        gr'' = insertEdge node node1 (NumEdge 0) gr2
        gr''' = insertEdge node node2 (NumEdge 1) gr''
type2graph (Record fields) mapt gr = (gr'', node)
  where (gr', node) = newNode RecordTag gr
        gr'' = List.foldl' f gr' fields
        f gr (name, ty) = insertEdge node node' (RecordEdge name) gr'
          where (gr', node') = type2graph ty mapt gr
type2graph (AllOf tys) mapt gr = (gr'', node)
  where (gr', node) = newNode AllOfTag gr
        gr'' = List.foldl' f gr' (List.zip tys [0..])
        f gr (ty, n) = insertEdge node node' (NumEdge n) gr'
          where (gr', node') = type2graph ty mapt gr
type2graph (TypeVar u) mapt gr = newNode (TypeVarTag u) gr
type2graph Error mapt gr = newNode ErrorTag gr

graph2type :: Map.Map String Int -> InstType -> TypeGraph -> Type
graph2type map (n, inst) gr =
  graph2type' (n, inst)
  where    
    graph2type' (n, inst) =
      case lab gr n of
        Just (NameTag name) ->
          case Map.lookup name map of
            Just argnum ->
              case Map.lookup argnum inst of
                Just n -> graph2type' (n, inst)
                Nothing -> Name name inst'
            Nothing -> Name name inst'
            where inst' = List.map f $ List.sortBy (comparing snd) $ lsuc n gr
                  f (_, InstEdge _ n) = graph2type' (n, inst)
        Just (NameDefTag name args)
          | Map.size inst == List.length args ->
            graph2type' (n', inst)
          where [(n', DefEdge)] = lsuc n gr
        Just ArrayTag -> Array (graph2type' (n', inst))
          where [(n', _)] = lsuc n gr
        Just SetTag -> Set (graph2type' (n', inst))
          where [(n', _)] = lsuc n gr
        Just TupleTag -> Tuple $ List.map (\n -> graph2type' (n, inst)) nodes
          where (nodes, _) = List.unzip $ lsuc n gr
        Just UnionTag -> Union t1 t2
          where [(n1, _), (n2, _)] = lsuc n gr
                t1 = graph2type' (n1, inst)
                t2 = graph2type' (n2, inst)
        Just ArrowTag -> Arrow t1 t2
          where [(n1, _), (n2, _)] = lsuc n gr
                t1 = graph2type' (n1, inst)
                t2 = graph2type' (n2, inst)
        Just RecordTag -> Record fields
          where fields = List.map (\(n, RecordEdge s) ->
                                    (s, graph2type' (n, inst))) $ lsuc n gr
        Just (TypeVarTag u) -> TypeVar u
        Just AllOfTag -> AllOf tys
          where tys = List.map (\(n, _) -> graph2type' (n, inst)) $ lsuc n gr
        Just ErrorTag -> Error

translateTypeDecl :: String -> Type -> [String] -> TypeGraph -> TypeGraph
translateTypeDecl name ty args gr =
  case (lookupType name gr) of
    Just n  -> gr
    Nothing -> insertEdge root n DefEdge gr''''
      where (gr', root) = newNode (NameDefTag name args) gr
            gr'' = insertName name args root gr'
            (gr''', mapt) = List.foldr f (gr'', Map.empty) args
            f name (gr, mapt) = (gr', Map.insert name node mapt)
              where (gr', node) = newNode (NameTag name) gr
            (gr'''', n) = type2graph ty mapt gr'''

assumption :: InstType -> InstType -> TypeGraph -> Assumptions -> Bool
assumption t1@(n1, ts1) t2@(n2, ts2) gr assum
  | Set.member (t1, t2) assum = True
  | otherwise = 
    List.length ts1' == List.length ts2' &&
    lab gr n1 == lab gr n2 &&
    List.all f (List.zip ts1' ts2')
  where ts1' = List.sortBy (comparing fst) $ Map.toList ts1
        ts2' = List.sortBy (comparing fst) $ Map.toList ts2
        f ((n, node1), (m, node2)) =
          n == m && assumption (node1, ts1) (node2, ts2) gr assum
--TODO: (ts1, ts2) or (Map.empty, Map.empty) ?

assumptions :: Assumptions
assumptions = Set.fromList [((0, Map.empty), (0, Map.empty))]
  
subtype' :: Map.Map String Int -> Map.Map String Int -> InstType -> InstType -> Substitution -> TypeGraph -> (Bool, Substitution)
subtype' map1 map2 (n1, inst1) (n2, inst2) subst gr =
  let (b, _, subst') = subtype'' assumptions (n1, inst1) (n2, inst2) subst
  in (b, subst')
  where
    subtype'' :: Assumptions -> InstType -> InstType -> Substitution -> (Bool, Assumptions, Substitution)
    subtype'' assum (n1, inst1) (n2, inst2) subst =
      case (lab gr n1, lab gr n2) of
        (Just ErrorTag, Just _) -> (True, assum, subst)
        (Just _, Just ErrorTag) -> (True, assum, subst)
        (Just (NameDefTag s1 args), Just _) ->
          case lsuc n1 gr of
            [(n, DefEdge)] ->
              if assumption (n, inst1) (n2, inst2) gr assum then (True, assum, subst)
              else subtype'' (Set.insert ((n, inst1), (n2, inst2)) assum) (n, inst1) (n2, inst2) subst
        (Just _, Just (NameDefTag s2 args)) ->
          case lsuc n2 gr of
            [(n, DefEdge)] ->
              if assumption (n1, inst1) (n, inst2) gr assum then (True, assum, subst)
              else subtype'' (Set.insert ((n1, inst1), (n, inst2)) assum) (n1, inst1) (n, inst2) subst
        (Just _, Just (NameTag s2)) ->
          case Map.lookup s2 map2 of
            Just n ->
              if assumption (n1, inst1) (n, inst2) gr assum then (True, assum, subst)
              else subtype'' (Set.insert ((n1, inst1), (n, inst2)) assum) (n1, inst1) (n, inst2) subst
            Nothing ->
              case lsuc n2 gr of
                [] -> (assumption (n1, inst1) (n2, inst2) gr assum, assum, subst)
                sucs@((n, _):_) ->
                  if assumption (n1, inst1) (n, inst2') gr assum then (True, assum, subst)
                  else subtype'' (Set.insert ((n1, inst1),(n, inst2')) assum) (n1, inst1) (n, inst2') subst
                  where inst2' = Map.fromList $ List.map (\(_, InstEdge s n) -> (s, n)) sucs
        (Just (NameTag s1), Just _) ->
          case Map.lookup s1 map1 of
            Just n ->
              if assumption (n, inst1) (n2, inst2) gr assum then (True, assum, subst)
              else subtype'' (Set.insert ((n, inst1), (n2, inst2)) assum) (n, inst1) (n2, inst2) subst
            Nothing ->
              case lsuc n1 gr of
                [] -> (assumption (n1, inst1) (n2, inst2) gr assum, assum, subst)
                sucs@((n, _):_) ->
                  if assumption (n, inst1') (n2, inst2) gr assum then (True, assum, subst)
                  else subtype'' (Set.insert ((n, inst1'), (n2, inst2)) assum) (n, inst1') (n2, inst2) subst
                  where inst1' = Map.fromList $ List.map (\(_, InstEdge s n) -> (s, n)) sucs
        (Just ArrayTag, Just ArrayTag) ->
          case (lsuc n1 gr, lsuc n2 gr) of
            ([(n1, _)], [(n2, _)]) ->
              subtype'' assum (n1, inst1) (n2, inst2) subst
        (Just SetTag, Just SetTag) ->
          case (lsuc n1 gr, lsuc n2 gr) of
            ([(n1, _)], [(n2, _)]) ->
              subtype'' assum (n1, inst1) (n2, inst2) subst
        (Just UnionTag, Just UnionTag) -> ((b11 || b12) && (b21 || b22), a4, subst4)
          {-TODO:
            We shouldn't use the substitution from one subtype''
            call in the next subtype'' calls -}
          where [(a, _), (b, _)] = lsuc n1 gr
                [(c, _), (d, _)] = lsuc n2 gr
                (b11, a1, subst1) = subtype'' assum (a, inst1) (c, inst2) subst
                (b12, a2, subst2) = subtype'' a1 (a, inst1) (d, inst2) subst1
                (b21, a3, subst3) = subtype'' a2 (b, inst1) (c, inst2) subst2
                (b22, a4, subst4) = subtype'' a3 (b, inst1) (d, inst2) subst3
        (Just _, Just UnionTag) -> (b1 || b2, a2, Map.unionWith Union subst1 subst2)
          where [(a, _), (b, _)] = lsuc n2 gr
                (b1, a1, subst1) = subtype'' assum (n1, inst1) (a, inst2) subst
                (b2, a2, subst2) = subtype'' assum (n1, inst1) (b, inst2) subst
        (Just UnionTag, Just _) -> (b1 && b2, a2, Map.unionWith Union subst1 subst2)
          where [(a, _), (b, _)] = lsuc n1 gr
                (b1, a1, subst1) = subtype'' assum (a, inst1) (n2, inst2) subst
                (b2, a2, subst2) = subtype'' assum (b, inst1) (n2, inst2) subst
        (Just AllOfTag, Just _) -> List.foldl' f (True, assum, subst) nodes
          where (nodes, _) = List.unzip $ lsuc n1 gr
                f (b, assum, subst) node =
                  if b then subtype'' assum (node, inst1) (n2, inst2) subst
                  else (False, assum, subst)
        (Just _, Just AllOfTag) -> List.foldl' f (True, assum, subst) nodes
          where (nodes, _) = List.unzip $ lsuc n2 gr
                f (b, assum, subst) node =
                  if b then subtype'' assum (n1, inst1) (node, inst2) subst
                  else (False, assum, subst)
        (Just (TypeVarTag u), Just _) ->
          case unify' (TypeVar u) (graph2type map2 (n2, inst2) gr) subst gr of
            Just (_, subst') -> (True, assum, subst')
            Nothing -> (False, assum, subst)
        (Just _, Just (TypeVarTag u)) ->
          case unify' (graph2type map1 (n1, inst1) gr) (TypeVar u) subst gr of
            Just (_, subst') -> (True, assum, subst')
            Nothing -> (False, assum, subst)
        (Just TupleTag, Just TupleTag)
          | List.length sucs1 == List.length sucs2 ->
            List.foldl' f (True, assum, subst) (List.zip sucs1 sucs2)
          | otherwise -> (False, assum, subst)
          where sucs1 = List.map fst $ List.sort $ lsuc n1 gr
                sucs2 = List.map fst $ List.sort $ lsuc n2 gr
                f (b, assum, subst) (n1, n2) =
                  if b then subtype'' assum (n1, inst1) (n2, inst2) subst
                  else (False, assum, subst)
        (Just ArrowTag, Just ArrowTag) -> (b1 && b2, a2, subst2)
          where [(dom1, _), (cod1, _)] = List.sort $ lsuc n1 gr
                [(dom2, _), (cod2, _)] = List.sort $ lsuc n2 gr
                (b1, a1, subst1) = subtype'' assum (dom1, inst1) (dom2, inst2) subst
                (b2, a2, subst2) = subtype'' a1 (cod2, inst2) (cod1, inst1) subst1
        (Just RecordTag, Just RecordTag) ->
          Map.foldlWithKey g (True, assum, subst) fields1
          where fields1 = Map.fromList $ List.map f $ lsuc n1 gr
                fields2 = Map.fromList $ List.map f $ lsuc n2 gr
                f (n, RecordEdge s) = (s, n)
                g (b, assum, subst) s n =
                  if b then
                    case Map.lookup s fields2 of
                      Just n' -> subtype'' assum (n, inst1) (n', inst2) subst
                      Nothing -> (False, assum, subst)
                  else (False, assum, subst)
        (Just _, Just _) -> (False, assum, subst)

foldlWithKeyM :: Monad m => (a -> k -> b -> m a) -> a -> Map.Map k b -> m a
foldlWithKeyM f acc = Map.foldlWithKey f' (return acc) 
    where
        f' ma k b = ma >>= \a -> f a k b
        
subtype :: Map.Map String Int -> Map.Map String Int -> InstType -> InstType -> Substitution -> TypeGraph -> IO (Bool, Substitution)
subtype map1 map2 (n1, inst1) (n2, inst2) subst gr =
  subtype'' assumptions (n1, inst1) (n2, inst2) subst
    >>= \(b, _, subst) -> return (b, subst)
  where
    typename1 = lookupNode n1 gr
    typename2 = lookupNode n2 gr

    subtype'' :: Assumptions -> InstType -> InstType -> Substitution -> IO (Bool, Assumptions, Substitution)
    subtype'' assum (n1, inst1) (n2, inst2) subst =
      case (lab gr n1, lab gr n2) of
        (Just ErrorTag, Just _) -> return (True, assum, subst)
        (Just _, Just ErrorTag) -> return (True, assum, subst)
        (Just (NameDefTag s1 args), Just _) ->
          case lsuc n1 gr of
            [(n, DefEdge)] ->
              if assumption (n, inst1) (n2, inst2) gr assum then return (True, assum, subst)
              else subtype'' (Set.insert ((n, inst1), (n2, inst2)) assum) (n, inst1) (n2, inst2) subst
        (Just _, Just (NameDefTag s2 args)) ->
          case lsuc n2 gr of
            [(n, DefEdge)] ->
              if assumption (n1, inst1) (n, inst2) gr assum then return (True, assum, subst)
              else subtype'' (Set.insert ((n1, inst1), (n, inst2)) assum) (n1, inst1) (n, inst2) subst
        (Just _, Just (NameTag s2)) ->
          case Map.lookup s2 map2 of
            Just n ->
              if assumption (n1, inst1) (n, inst2) gr assum then return (True, assum, subst)
              else subtype'' (Set.insert ((n1, inst1), (n, inst2)) assum) (n1, inst1) (n, inst2) subst
            Nothing ->
              case lsuc n2 gr of
                [] -> return (assumption (n1, inst1) (n2, inst2) gr assum, assum, subst)
                sucs@((n, _):_) ->
                  if assumption (n1, inst1) (n, inst2') gr assum then return (True, assum, subst)
                  else subtype'' (Set.insert ((n1, inst1),(n, inst2')) assum) (n1, inst1) (n, inst2') subst
                  where inst2' = Map.fromList $ List.map (\(_, InstEdge s n) -> (s, n)) sucs
        (Just (NameTag s1), Just _) ->
          case Map.lookup s1 map1 of
            Just n ->
              if assumption (n, inst1) (n2, inst2) gr assum then return (True, assum, subst)
              else subtype'' (Set.insert ((n, inst1), (n2, inst2)) assum) (n, inst1) (n2, inst2) subst
            Nothing ->
              case lsuc n1 gr of
                [] -> return (assumption (n1, inst1) (n2, inst2) gr assum, assum, subst)
                sucs@((n, _):_) ->
                  if assumption (n, inst1') (n2, inst2) gr assum then return (True, assum, subst)
                  else subtype'' (Set.insert ((n, inst1'), (n2, inst2)) assum) (n, inst1') (n2, inst2) subst
                  where inst1' = Map.fromList $ List.map (\(_, InstEdge s n) -> (s, n)) sucs
        (Just ArrayTag, Just ArrayTag) ->
          case (lsuc n1 gr, lsuc n2 gr) of
            ([(n1, _)], [(n2, _)]) ->
              subtype'' assum (n1, inst1) (n2, inst2) subst
        (Just SetTag, Just SetTag) ->
          case (lsuc n1 gr, lsuc n2 gr) of
            ([(n1, _)], [(n2, _)]) ->
              subtype'' assum (n1, inst1) (n2, inst2) subst
        (Just UnionTag, Just UnionTag) ->
          let [(a, _), (b, _)] = lsuc n1 gr
              [(c, _), (d, _)] = lsuc n2 gr
          in do (b11, a1, subst1) <- subtype'' assum (a, inst1) (c, inst2) subst
                (b12, a2, subst2) <- subtype'' a1 (a, inst1) (d, inst2) subst1
                (b21, a3, subst3) <- subtype'' a2 (b, inst1) (c, inst2) subst2
                (b22, a4, subst4) <- subtype'' a3 (b, inst1) (d, inst2) subst3
                return ((b11 || b12) && (b21 || b22), a4, subst4)
        (Just _, Just UnionTag) ->
          let [(a, _), (b, _)] = lsuc n2 gr
          in do (b1, a1, subst1) <- subtype'' assum (n1, inst1) (a, inst2) subst
                (b2, a2, subst2) <- subtype'' a1 (n1, inst1) (b, inst2) subst1
                return (b1 || b2, a2, subst2)
        (Just UnionTag, Just _) ->
          let [(a, _), (b, _)] = lsuc n1 gr
          in do (b1, a1, subst1) <- subtype'' assum (a, inst1) (n2, inst2) subst
                (b2, a2, subst2) <- subtype'' a1 (b, inst1) (n2, inst2) subst1
                return (b1 && b2, a2, subst2)
        (Just AllOfTag, Just _) -> foldM f (True, assum, subst) nodes
          where (nodes, _) = List.unzip $ lsuc n1 gr
                f (b, assum, subst) node =
                  if b then subtype'' assum (node, inst1) (n2, inst2) subst
                  else return (False, assum, subst)
        (Just _, Just AllOfTag) -> foldM f (True, assum, subst) nodes
          where (nodes, _) = List.unzip $ lsuc n2 gr
                f (b, assum, subst) node =
                  if b then subtype'' assum (n1, inst1) (node, inst2) subst
                  else return (False, assum, subst)
        (Just (TypeVarTag u), Just _) ->
          do (_, subst') <- unify (TypeVar u) (graph2type map2 (n2, inst2) gr) subst gr
             return (True, assum, subst')
        (Just _, Just (TypeVarTag u)) ->
          do (_, subst') <- unify (graph2type map1 (n1, inst1) gr) (TypeVar u) subst gr
             return (True, assum, subst')
        (Just TupleTag, Just TupleTag)
          | List.length sucs1 == List.length sucs2 ->
            foldM f (True, assum, subst) (List.zip sucs1 sucs2)
          | otherwise -> return (False, assum, subst)
          where sucs1 = List.map fst $ List.sort $ lsuc n1 gr
                sucs2 = List.map fst $ List.sort $ lsuc n2 gr
                f (b, assum, subst) (n1, n2) =
                  if b then subtype'' assum (n1, inst1) (n2, inst2) subst
                  else return (False, assum, subst)
        (Just ArrowTag, Just ArrowTag) ->
          let [(dom1, _), (cod1, _)] = List.sort $ lsuc n1 gr
              [(dom2, _), (cod2, _)] = List.sort $ lsuc n2 gr
          in do (b1, a1, subst1) <- subtype'' assum (dom1, inst1) (dom2, inst2) subst
                (b2, a2, subst2) <- subtype'' a1 (cod2, inst2) (cod1, inst1) subst1
                return (b1 && b2, a2, subst2)
        (Just RecordTag, Just RecordTag) ->
          foldlWithKeyM g (True, assum, subst) fields1
          where fields1 = Map.fromList $ List.map f $ lsuc n1 gr
                fields2 = Map.fromList $ List.map f $ lsuc n2 gr
                f (n, RecordEdge s) = (s, n)
                g (b, assum, subst) s n =
                  if b then
                    case Map.lookup s fields2 of
                      Just n' -> subtype'' assum (n, inst1) (n', inst2) subst
                      Nothing -> return (False, assum, subst)
                  else return (False, assum, subst)
        (Just _, Just _) -> return (False, assum, subst)