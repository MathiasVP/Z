import qualified Data.Graph.Inductive as G
import qualified Data.Graph.Inductive.Dot as Dot
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Ord
import Debug.Trace as Debug

data Type
  = Name String [(String, Type)]
  | Tuple [Type]
  | Union Type Type
  | Arrow Type Type
  | Record [(String, Type)]
  deriving (Show, Ord, Eq)

data TypeTag
  = NameTag String
  | NameDefTag String [String]
  | TupleTag
  | UnionTag
  | ArrowTag
  | RecordTag
  deriving Show

data GraphEdge
  = NumEdge Int
  | DefEdge
  | RecordEdge String
  | InstEdge String G.Node
  deriving (Show, Ord, Eq)
             
type TypeGraph = (Map.Map String G.Node, G.Gr TypeTag GraphEdge)

empty = (Map.fromList [("Int", 0)],
         G.mkGraph [(0, NameTag "Int")] [])

lookupType :: String -> TypeGraph -> Maybe G.Node
lookupType name (map, _) = Map.lookup name map

newNode :: TypeTag -> TypeGraph -> (TypeGraph, G.Node)
newNode tag (map, gr) = ((map, G.insNode (node, tag) gr), node)
  where [node] = G.newNodes 1 gr
  
insertName :: String -> G.Node -> TypeGraph -> TypeGraph
insertName name node (map, gr) =
  (Map.insert name node map, gr)
        
insertEdge :: G.Node -> G.Node -> GraphEdge -> TypeGraph -> TypeGraph
insertEdge from to label (map, gr) = (map, G.insEdge (from, to, label) gr)

insertNode :: G.Node -> TypeTag -> TypeGraph -> TypeGraph
insertNode node tag (map, gr) = (map, G.insNode (node, tag) gr)

lab :: TypeGraph -> G.Node -> Maybe TypeTag
lab (map, gr) node = G.lab gr node

lsuc :: G.Node -> TypeGraph -> [(G.Node, GraphEdge)]
lsuc node (_, gr) = G.lsuc gr node

type2graph :: Type -> Map.Map String G.Node -> TypeGraph -> (TypeGraph, G.Node)
type2graph (Name name args) mapt gr =
  case Map.lookup name mapt of
    Just targetnode ->
      (gr, targetnode)
    Nothing ->
      case lookupType name gr of
        Just targetnode -> (gr'', node)
          where (gr', node) = newNode (NameTag name) gr
                gr'' = List.foldl' f gr' args
                f gr (name, ty) = insertEdge node targetnode (InstEdge name node') gr'
                  where (gr', node') = type2graph ty mapt gr
type2graph (Tuple tys) mapt gr =
  (List.foldl' f gr' (List.zip [0..] tys), node)
  where (gr', node) = newNode TupleTag gr
        f gr (n, ty) = insertEdge node node' (NumEdge n) gr'
          where (gr', node') = type2graph ty mapt gr
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

translateDecl :: String -> Type -> [String] -> TypeGraph -> (TypeGraph, G.Node)
translateDecl name ty args gr =
  case (lookupType name gr) of
    Just n  -> (gr, n)
    Nothing -> (insertEdge root n DefEdge gr'''', root)
      where (gr', root) = newNode (NameDefTag name args) gr
            gr'' = insertName name root gr'
            (gr''', mapt) = List.foldr f (gr'', Map.empty) args
            f name (gr, mapt) = (gr', Map.insert name node mapt)
              where (gr', node) = newNode (NameTag name) gr
            (gr'''', n) = type2graph ty mapt gr'''
            
type InstType = (G.Node, Map.Map String G.Node)
type Visited = Set.Set (InstType, InstType)

subtype :: Visited -> InstType -> InstType -> TypeGraph -> (Bool, Visited)
subtype visited (n1, inst1) (n2, inst2) gr =
  case (Debug.trace ("n1: " ++ show n1 ++ show (Map.toList inst1)) (lab gr n1), Debug.trace ("n2: " ++ show n2 ++ show (Map.toList inst2) ++ "\n") (lab gr n2)) of
    (Just (NameDefTag s1 args), Just _) ->
      case lsuc n1 gr of
        [(n, DefEdge)]
          | Map.size inst1 == List.length args ->
            if Set.member ((n, inst1), (n2, inst2)) visited then (True, visited)
            else subtype (Set.insert ((n, inst1), (n2, inst2)) visited) (n, inst1) (n2, inst2) gr
    (Just _, Just (NameDefTag s2 args)) ->
      case lsuc n2 gr of
        [(n, DefEdge)]
          | Map.size inst2 == List.length args ->
            if Set.member ((n1, inst1), (n, inst2)) visited then (True, visited)
            else subtype (Set.insert ((n1, inst1), (n, inst2)) visited) (n1, inst1) (n, inst2) gr 
    (Just _, Just (NameTag s2)) ->
      case Map.lookup s2 inst2 of
        Just n ->
          if Set.member ((n1, inst1), (n, Map.empty)) visited then (True, visited)
          else subtype (Set.insert ((n1, inst1),(n, Map.empty)) visited) (n1, inst1) (n, Map.empty) gr
        Nothing ->
          case lsuc n2 gr of
            [] -> (Set.member ((n1, inst1), (n2, inst2)) visited, visited)
            sucs@((n, _):_) ->
              if Set.member ((n1, inst1),(n, inst2')) visited then (True, visited)
              else subtype (Set.insert ((n1, inst1),(n, inst2')) visited) (n1, inst1) (n, inst2') gr
              where inst2' = Map.fromList $ List.map (\(_, InstEdge s n) -> (s, n)) sucs
    (Just (NameTag s1), Just _) ->
      case Map.lookup s1 inst1 of
        Just n ->
          if Set.member ((n, inst1),(n2, Map.empty)) visited then (True, visited)
          else subtype (Set.insert ((n, inst1), (n2, Map.empty)) visited) (n, inst1) (n2, Map.empty) gr
        Nothing ->
          case lsuc n1 gr of
            [] -> (Set.member ((n1, inst1), (n2, inst2)) visited, visited)
            sucs@((n, _):_) ->
              if Set.member ((n, inst1'),(n2, inst2)) visited then (True, visited)
              else subtype (Set.insert ((n, inst1'),(n2, inst2)) visited) (n, inst1') (n2, inst2) gr
              where inst1' = Map.fromList $ List.map (\(_, InstEdge s n) -> (s, n)) sucs
    (Just UnionTag, Just UnionTag) ->
      ((b11 || b12) && (b21 || b22), v4)
      where [(a, _), (b, _)] = lsuc n1 gr
            [(c, _), (d, _)] = lsuc n2 gr
            (b11, v1) = subtype visited (a, inst1) (c, inst2) gr
            (b12, v2) = subtype v1 (a, inst1) (d, inst2) gr
            (b21, v3) = subtype v2 (b, inst1) (c, inst2) gr
            (b22, v4) = subtype v3 (b, inst1) (d, inst2) gr
    (Just _, Just UnionTag) -> (b1 || b2, v2)
      where [(a, _), (b, _)] = lsuc n2 gr
            (b1, v1) = subtype visited (n1, inst1) (a, inst2) gr
            (b2, v2) = subtype v1 (n1, inst1) (b, inst2) gr
    (Just UnionTag, Just _) ->
      (b1 && b2, v2)
      where [(a, _), (b, _)] = lsuc n1 gr
            (b1, v1) = subtype visited (a, inst1) (n2, inst2) gr
            (b2, v2) = subtype v1 (b, inst1) (n2, inst2) gr
    (Just TupleTag, Just TupleTag)
      | List.length sucs1 == List.length sucs2 ->
        List.foldl' f (True, visited) (List.zip sucs1 sucs2)
      | otherwise -> (False, visited)
      where sucs1 = List.map fst $ List.sort $ lsuc n1 gr
            sucs2 = List.map fst $ List.sort $ lsuc n2 gr
            f (b, visited) (n1, n2) =
                if b then (b', visited')
                else (False, visited)
                where (b', visited') = subtype visited (n1, inst1) (n2, inst2) gr
    (Just ArrowTag, Just ArrowTag) -> (b1 && b2, v2)
      where [(dom1, _), (cod1, _)] = List.sort $ lsuc n1 gr
            [(dom2, _), (cod2, _)] = List.sort $ lsuc n2 gr
            (b1, v1) = subtype visited (dom1, inst1) (dom2, inst2) gr
            (b2, v2) = subtype v1 (cod2, inst2) (cod1, inst1) gr
    (Just _, Just _) -> (False, visited)

main :: IO ()
main = do
  let ty1 = Union (Tuple []) (Tuple [Tuple [Name "T" [], Name "T" []], Name "List" [("T", Name "T" [])]])
  let ty2 = Tuple [Tuple [Name "T" [], Name "T" []], Name "List" [("T", Name "T" [])]]
  let ty3 = Union (Name "Int" []) (Tuple [Name "Int" [], Name "Int" []])
  let (gr1, _) = translateDecl "List" ty1 ["T"] empty
  let (gr2, _) = translateDecl "NEList" ty2 ["T"] gr1
  let (gr3, _) = translateDecl "TwoInts" ty3 [] gr2
  putStrLn $ Dot.showDot $ Dot.fglToDot (snd gr3)
  print $ fst $ subtype Set.empty (8, Map.fromList [("T", 0)]) (1, Map.fromList [("T", 13)]) gr3