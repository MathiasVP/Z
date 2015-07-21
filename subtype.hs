module Subtype where
import qualified Data.Graph.Inductive as G
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Unique as U
import Control.Monad
import Data.Ord
import Ast
import Unification

data TypeTag
  = NameTag String
  | NameDefTag String [String]
  | ArrayTag
  | SetTag
  | TupleTag
  | UnionTag
  | ArrowTag
  | RecordTag
  | TypeVarTag Unique
  | AllOfTag
  | ErrorTag
  deriving Show

data GraphEdge
  = NumEdge Int
  | DefEdge
  | RecordEdge String
  | InstEdge Int G.Node
  deriving (Show, Ord, Eq)
             
type TypeGraph = (Map.Map String G.Node, Map.Map G.Node String, G.Gr TypeTag GraphEdge, Map.Map String (Map.Map String Int))
type InstType = (G.Node, Map.Map Int G.Node)
type Assumptions = Set.Set (InstType, InstType)

empty = (Map.fromList [("Int", 0)],
         Map.fromList [(0, "Int")],
         G.mkGraph [(0, NameTag "Int")] [],
         Map.empty)

{- Initial assumptions:
     Int <: Int
-}
assumptions :: Assumptions
assumptions = Set.fromList [((0, Map.empty), (0, Map.empty))]

lookupType :: String -> TypeGraph -> Maybe G.Node
lookupType name (map, _, _, _) = Map.lookup name map

lookupNode :: G.Node -> TypeGraph -> Maybe String
lookupNode node (_, map', _, _) = Map.lookup node map'

lookupFormal :: Maybe String -> String -> TypeGraph -> Maybe Int
lookupFormal (Just tyname) argname (_, _, _, tmap) =
  join $ liftM (Map.lookup argname) (Map.lookup tyname tmap)
lookupFormal _ _ _ = Nothing

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

graph2type :: InstType -> TypeGraph -> Type
graph2type (n, inst) gr =
  graph2type' (n, inst)
  where
    typename = lookupNode n gr
    
    graph2type' (n, inst) =
      case lab gr n of
        Just (NameTag name) ->
          case lookupFormal typename name gr of
            Just argnum ->
              case Map.lookup argnum inst of
                Just n -> graph2type' (n, inst)
                Nothing -> Name name inst'
                  where inst' = List.map f $ lsuc n gr --TODO: Sort b InstEdge
                        f (_, InstEdge _ n) = graph2type' (n, inst)
            Nothing -> Name name inst'
                  where inst' = List.map f $ lsuc n gr
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

translateDecl :: String -> Type -> [String] -> TypeGraph -> (TypeGraph, G.Node)
translateDecl name ty args gr =
  case (lookupType name gr) of
    Just n  -> (gr, n)
    Nothing -> (insertEdge root n DefEdge gr'''', root)
      where (gr', root) = newNode (NameDefTag name args) gr
            gr'' = insertName name args root gr'
            (gr''', mapt) = List.foldr f (gr'', Map.empty) args
            f name (gr, mapt) = (gr', Map.insert name node mapt)
              where (gr', node) = newNode (NameTag name) gr
            (gr'''', n) = type2graph ty mapt gr'''

assumption :: InstType -> InstType -> Assumptions -> Bool
assumption t1 t2 assum
  | t1 == t2  = True
  | otherwise = Set.member (t1, t2) assum

subtype :: Assumptions -> InstType -> InstType -> Substitution -> TypeGraph -> (Bool, Assumptions, Substitution)
subtype assum (n1, inst1) (n2, inst2) subst gr =
  subtype' assum (n1, inst1) (n2, inst2) subst
  where
    typename1 = lookupNode n1 gr
    typename2 = lookupNode n2 gr
  
    subtype' :: Assumptions -> InstType -> InstType -> Substitution -> (Bool, Assumptions, Substitution)
    subtype' assum (n1, inst1) (n2, inst2) subst =
      case (lab gr n1, lab gr n2) of
        (Just ErrorTag, Just _) -> (True, assum, subst)
        (Just _, Just ErrorTag) -> (True, assum, subst)
        (Just (NameDefTag s1 args), Just _) ->
          case lsuc n1 gr of
            [(n, DefEdge)] ->
              if assumption (n, inst1) (n2, inst2) assum then (True, assum, subst)
              else subtype' (Set.insert ((n, inst1), (n2, inst2)) assum) (n, inst1) (n2, inst2) subst
        (Just _, Just (NameDefTag s2 args)) ->
          case lsuc n2 gr of
            [(n, DefEdge)] ->
              if assumption (n1, inst1) (n, inst2) assum then (True, assum, subst)
              else subtype' (Set.insert ((n1, inst1), (n, inst2)) assum) (n1, inst1) (n, inst2) subst
        (Just _, Just (NameTag s2)) ->
          case join $ liftM (flip Map.lookup inst2) (lookupFormal typename2 s2 gr) of
            Just n ->
              if assumption (n1, inst1) (n, inst2) assum then (True, assum, subst)
              else subtype' (Set.insert ((n1, inst1), (n, inst2)) assum) (n1, inst1) (n, inst2) subst
            Nothing ->
              case lsuc n2 gr of
                [] -> (assumption (n1, inst1) (n2, inst2) assum, assum, subst)
                sucs@((n, _):_) ->
                  if assumption (n1, inst1) (n, inst2') assum then (True, assum, subst)
                  else subtype' (Set.insert ((n1, inst1),(n, inst2')) assum) (n1, inst1) (n, inst2') subst
                  where inst2' = Map.fromList $ List.map (\(_, InstEdge s n) -> (s, n)) sucs
        (Just (NameTag s1), Just _) ->
          case join $ liftM (flip Map.lookup inst1) (lookupFormal typename1 s1 gr) of
            Just n ->
              if assumption (n, inst1) (n2, inst2) assum then (True, assum, subst)
              else subtype' (Set.insert ((n, inst1), (n2, inst2)) assum) (n, inst1) (n2, inst2) subst
            Nothing ->
              case lsuc n1 gr of
                [] -> (assumption (n1, inst1) (n2, inst2) assum, assum, subst)
                sucs@((n, _):_) ->
                  if assumption (n, inst1') (n2, inst2) assum then (True, assum, subst)
                  else subtype' (Set.insert ((n, inst1'), (n2, inst2)) assum) (n, inst1') (n2, inst2) subst
                  where inst1' = Map.fromList $ List.map (\(_, InstEdge s n) -> (s, n)) sucs
        (Just ArrayTag, Just ArrayTag) ->
          case (lsuc n1 gr, lsuc n2 gr) of
            ([(n1, _)], [(n2, _)]) ->
              subtype' assum (n1, inst1) (n2, inst2) subst
        (Just SetTag, Just SetTag) ->
          case (lsuc n1 gr, lsuc n2 gr) of
            ([(n1, _)], [(n2, _)]) ->
              subtype' assum (n1, inst1) (n2, inst2) subst
        (Just UnionTag, Just UnionTag) -> ((b11 || b12) && (b21 || b22), a4, subst4)
          where [(a, _), (b, _)] = lsuc n1 gr
                [(c, _), (d, _)] = lsuc n2 gr
                (b11, a1, subst1) = subtype' assum (a, inst1) (c, inst2) subst
                (b12, a2, subst2) = subtype' a1 (a, inst1) (d, inst2) subst1
                (b21, a3, subst3) = subtype' a2 (b, inst1) (c, inst2) subst2
                (b22, a4, subst4) = subtype' a3 (b, inst1) (d, inst2) subst3
        (Just _, Just UnionTag) -> (b1 || b2, a2, subst2)
          where [(a, _), (b, _)] = lsuc n2 gr
                (b1, a1, subst1) = subtype' assum (n1, inst1) (a, inst2) subst
                (b2, a2, subst2) = subtype' a1 (n1, inst1) (b, inst2) subst1
        (Just UnionTag, Just _) -> (b1 && b2, a2, subst2)
          where [(a, _), (b, _)] = lsuc n1 gr
                (b1, a1, subst1) = subtype' assum (a, inst1) (n2, inst2) subst
                (b2, a2, subst2) = subtype' a1 (b, inst1) (n2, inst2) subst1
        (Just AllOfTag, Just _) -> List.foldl' f (True, assum, subst) nodes
          where (nodes, _) = List.unzip $ lsuc n1 gr
                f (b, assum, subst) node =
                  if b then subtype' assum (node, inst1) (n2, inst2) subst
                  else (False, assum, subst)
        (Just _, Just AllOfTag) -> List.foldl' f (True, assum, subst) nodes
          where (nodes, _) = List.unzip $ lsuc n2 gr
                f (b, assum, subst) node =
                  if b then subtype' assum (n1, inst1) (node, inst2) subst
                  else (False, assum, subst)
        (Just (TypeVarTag u), Just _) ->
          case unify' (TypeVar u) (graph2type (n2, inst2) gr) subst of
            Just (_, subst') -> (True, assum, subst')
            Nothing -> (False, assum, subst)
        (Just _, Just (TypeVarTag u)) ->
          case unify' (graph2type (n1, inst1) gr) (TypeVar u) subst of
            Just (_, subst') -> (True, assum, subst')
            Nothing -> (False, assum, subst)
        (Just TupleTag, Just TupleTag)
          | List.length sucs1 == List.length sucs2 ->
            List.foldl' f (True, assum, subst) (List.zip sucs1 sucs2)
          | otherwise -> (False, assum, subst)
          where sucs1 = List.map fst $ List.sort $ lsuc n1 gr
                sucs2 = List.map fst $ List.sort $ lsuc n2 gr
                f (b, assum, subst) (n1, n2) =
                  if b then subtype' assum (n1, inst1) (n2, inst2) subst
                  else (False, assum, subst)
        (Just ArrowTag, Just ArrowTag) -> (b1 && b2, a2, subst2)
          where [(dom1, _), (cod1, _)] = List.sort $ lsuc n1 gr
                [(dom2, _), (cod2, _)] = List.sort $ lsuc n2 gr
                (b1, a1, subst1) = subtype' assum (dom1, inst1) (dom2, inst2) subst
                (b2, a2, subst2) = subtype' a1 (cod2, inst2) (cod1, inst1) subst1
        (Just RecordTag, Just RecordTag) ->
          Map.foldlWithKey g (True, assum, subst) fields1
          where fields1 = Map.fromList $ List.map f $ lsuc n1 gr
                fields2 = Map.fromList $ List.map f $ lsuc n2 gr
                f (n, RecordEdge s) = (s, n)
                g (b, assum, subst) s n =
                  if b then
                    case Map.lookup s fields2 of
                      Just n' -> subtype' assum (n, inst1) (n', inst2) subst
                      Nothing -> (False, assum, subst)
                  else (False, assum, subst)
        (Just _, Just _) -> (False, assum, subst)

main :: IO ()
main = do
  let ty1 = Union (Tuple []) (Tuple [Name "T" [], Name "List" [Name "T" []]])
  let ty2 = Tuple [Name "U" [], Name "List" [Name "U" []]]
  let ty3 = Union (Tuple []) (Name "Int" [])
  let (gr1, n1) = translateDecl "List" ty1 ["T"] empty
  let (gr2, n2) = translateDecl "NeList" ty2 ["U"] gr1
  let (gr3, n3) = translateDecl "MaybeInt" ty3 [] gr2
  let (b, _, _) = subtype assumptions (n2, Map.fromList [(0, n3)]) (n1, Map.fromList [(0, n3)]) Map.empty gr3
  print b