import qualified Data.Graph.Inductive as G
import qualified Data.Graph.Inductive.Dot as Dot
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Unique as U
import Control.Monad
import Data.Ord

data Type
  = Name String [(String, Type)]
  | Array Type
  | Set Type
  | Tuple [Type]
  | Union Type Type
  | Arrow Type Type
  | Record [(String, Type)]
  | TypeVar Unique
  | AllOf [Type]
  | Error
  deriving (Show, Ord, Eq)
  
instance Show Unique where
  show u = "Unique " ++ show (hashUnique u)

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
  | InstEdge String G.Node
  deriving (Show, Ord, Eq)
             
type TypeGraph = (Map.Map String G.Node, G.Gr TypeTag GraphEdge)
type Substitution = Map.Map U.Unique Type
type Env = Map.Map String Type
type InstType = (G.Node, Map.Map String G.Node)
type Visited = Set.Set (InstType, InstType)

unify' :: Type -> Type -> Substitution -> Maybe (Type, Substitution)
unify' = undefined

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

foldlWithKeyM :: Monad m => (a -> k -> b -> m a) -> a -> Map.Map k b -> m a
foldlWithKeyM f acc = Map.foldlWithKey f' (return acc) 
    where
        f' ma k b = ma >>= \a -> f a k b

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
  case lab gr n of
    Just (NameTag name) ->
      case Map.lookup name inst of
        Just n -> graph2type (n, inst) gr
        Nothing -> Name name inst'
          where inst' = List.map f $ lsuc n gr
                f (_, InstEdge s n) = (s, graph2type (n, inst) gr)
    Just (NameDefTag name args)
      | Map.size inst == List.length args ->
        graph2type (n', inst) gr
      where [(n', DefEdge)] = lsuc n gr
    Just ArrayTag -> Array (graph2type (n', inst) gr)
      where [(n', _)] = lsuc n gr
    Just SetTag -> Set (graph2type (n', inst) gr)
      where [(n', _)] = lsuc n gr
    Just TupleTag -> Tuple $ List.map (\n -> graph2type (n, inst) gr) nodes
      where (nodes, _) = List.unzip $ lsuc n gr
    Just UnionTag -> Union t1 t2
      where [(n1, _), (n2, _)] = lsuc n gr
            t1 = graph2type (n1, inst) gr
            t2 = graph2type (n2, inst) gr
    Just ArrowTag -> Arrow t1 t2
      where [(n1, _), (n2, _)] = lsuc n gr
            t1 = graph2type (n1, inst) gr
            t2 = graph2type (n2, inst) gr
    Just RecordTag -> Record fields
      where fields = List.map (\(n, RecordEdge s) ->
                                (s, graph2type (n, inst) gr)) $ lsuc n gr
    Just (TypeVarTag u) -> TypeVar u
    Just AllOfTag -> AllOf tys
      where tys = List.map (\(n, _) -> graph2type (n, inst) gr) $ lsuc n gr
    Just ErrorTag -> Error

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

subtype :: Visited -> InstType -> InstType -> Substitution -> TypeGraph -> (Bool, Visited, Substitution)
subtype visited (n1, inst1) (n2, inst2) subst gr =
  case (lab gr n1, lab gr n2) of
    (Just ErrorTag, Just _) -> (True, visited, subst)
    (Just _, Just ErrorTag) -> (True, visited, subst)
    (Just (NameDefTag s1 args), Just _) ->
      case lsuc n1 gr of
        [(n, DefEdge)]
          | Map.size inst1 == List.length args ->
            if Set.member ((n, inst1), (n2, inst2)) visited then (True, visited, subst)
            else subtype (Set.insert ((n, inst1), (n2, inst2)) visited) (n, inst1) (n2, inst2) subst gr
    (Just _, Just (NameDefTag s2 args)) ->
      case lsuc n2 gr of
        [(n, DefEdge)]
          | Map.size inst2 == List.length args ->
            if Set.member ((n1, inst1), (n, inst2)) visited then (True, visited, subst)
            else subtype (Set.insert ((n1, inst1), (n, inst2)) visited) (n1, inst1) (n, inst2) subst gr 
    (Just _, Just (NameTag s2)) ->
      case Map.lookup s2 inst2 of
        Just n ->
          if Set.member ((n1, inst1), (n, Map.empty)) visited then (True, visited, subst)
          else subtype (Set.insert ((n1, inst1),(n, Map.empty)) visited) (n1, inst1) (n, Map.empty) subst gr
        Nothing ->
          case lsuc n2 gr of
            [] -> (Set.member ((n1, inst1), (n2, inst2)) visited, visited, subst)
            sucs@((n, _):_) ->
              if Set.member ((n1, inst1),(n, inst2')) visited then (True, visited, subst)
              else subtype (Set.insert ((n1, inst1),(n, inst2')) visited) (n1, inst1) (n, inst2') subst gr
              where inst2' = Map.fromList $ List.map (\(_, InstEdge s n) -> (s, n)) sucs
    (Just (NameTag s1), Just _) ->
      case Map.lookup s1 inst1 of
        Just n ->
          if Set.member ((n, inst1),(n2, Map.empty)) visited then (True, visited, subst)
          else subtype (Set.insert ((n, inst1), (n2, Map.empty)) visited) (n, inst1) (n2, Map.empty) subst gr
        Nothing ->
          case lsuc n1 gr of
            [] -> (Set.member ((n1, inst1), (n2, inst2)) visited, visited, subst)
            sucs@((n, _):_) ->
              if Set.member ((n, inst1'),(n2, inst2)) visited then (True, visited, subst)
              else subtype (Set.insert ((n, inst1'),(n2, inst2)) visited) (n, inst1') (n2, inst2) subst gr
              where inst1' = Map.fromList $ List.map (\(_, InstEdge s n) -> (s, n)) sucs
    (Just ArrayTag, Just ArrayTag) ->
      case (lsuc n1 gr, lsuc n2 gr) of
        ([(n1, _)], [(n2, _)]) ->
          subtype visited (n1, inst1) (n2, inst2) subst gr
    (Just SetTag, Just SetTag) ->
      case (lsuc n1 gr, lsuc n2 gr) of
        ([(n1, _)], [(n2, _)]) ->
          subtype visited (n1, inst1) (n2, inst2) subst gr
    (Just UnionTag, Just UnionTag) -> ((b11 || b12) && (b21 || b22), v4, subst4)
      where [(a, _), (b, _)] = lsuc n1 gr
            [(c, _), (d, _)] = lsuc n2 gr
            (b11, v1, subst1) = subtype visited (a, inst1) (c, inst2) subst gr
            (b12, v2, subst2) = subtype v1 (a, inst1) (d, inst2) subst1 gr
            (b21, v3, subst3) = subtype v2 (b, inst1) (c, inst2) subst2 gr
            (b22, v4, subst4) = subtype v3 (b, inst1) (d, inst2) subst3 gr
    (Just _, Just UnionTag) -> (b1 || b2, v2, subst2)
      where [(a, _), (b, _)] = lsuc n2 gr
            (b1, v1, subst1) = subtype visited (n1, inst1) (a, inst2) subst gr
            (b2, v2, subst2) = subtype v1 (n1, inst1) (b, inst2) subst1 gr
    (Just UnionTag, Just _) -> (b1 && b2, v2, subst2)
      where [(a, _), (b, _)] = lsuc n1 gr
            (b1, v1, subst1) = subtype visited (a, inst1) (n2, inst2) subst gr
            (b2, v2, subst2) = subtype v1 (b, inst1) (n2, inst2) subst1 gr
    (Just AllOfTag, Just _) -> List.foldl' f (True, visited, subst) nodes
      where (nodes, _) = List.unzip $ lsuc n1 gr
            f (b, visited, subst) node =
              if b then subtype visited (node, inst1) (n2, inst2) subst gr
              else (False, visited, subst)
    (Just _, Just AllOfTag) -> List.foldl' f (True, visited, subst) nodes
      where (nodes, _) = List.unzip $ lsuc n2 gr
            f (b, visited, subst) node =
              if b then subtype visited (n1, inst1) (node, inst2) subst gr
              else (False, visited, subst)
    (Just (TypeVarTag u), Just _) ->
      case unify' (TypeVar u) (graph2type (n2, inst2) gr) subst of
        Just (_, subst') -> (True, visited, subst')
        Nothing -> (False, visited, subst)
    (Just _, Just (TypeVarTag u)) ->
      case unify' (graph2type (n1, inst1) gr) (TypeVar u) subst of
        Just (_, subst') -> (True, visited, subst')
        Nothing -> (False, visited, subst)
    (Just TupleTag, Just TupleTag)
      | List.length sucs1 == List.length sucs2 ->
        List.foldl' f (True, visited, subst) (List.zip sucs1 sucs2)
      | otherwise -> (False, visited, subst)
      where sucs1 = List.map fst $ List.sort $ lsuc n1 gr
            sucs2 = List.map fst $ List.sort $ lsuc n2 gr
            f (b, visited, subst) (n1, n2) =
              if b then subtype visited (n1, inst1) (n2, inst2) subst gr
              else (False, visited, subst)
    (Just ArrowTag, Just ArrowTag) -> (b1 && b2, v2, subst2)
      where [(dom1, _), (cod1, _)] = List.sort $ lsuc n1 gr
            [(dom2, _), (cod2, _)] = List.sort $ lsuc n2 gr
            (b1, v1, subst1) = subtype visited (dom1, inst1) (dom2, inst2) subst gr
            (b2, v2, subst2) = subtype v1 (cod2, inst2) (cod1, inst1) subst1 gr
    (Just RecordTag, Just RecordTag) ->
      Map.foldlWithKey g (True, visited, subst) fields1
      where fields1 = Map.fromList $ List.map f $ lsuc n1 gr
            fields2 = Map.fromList $ List.map f $ lsuc n2 gr
            f (n, RecordEdge s) = (s, n)
            g (b, visited, subst) s n =
              if b then
                case Map.lookup s fields2 of
                  Just n' -> subtype visited (n, inst1) (n', inst2) subst gr
                  Nothing -> (False, visited, subst)
              else (False, visited, subst)
    (Just _, Just _) -> (False, visited, subst)

main :: IO ()
main = do
  let ty1 = Union (Tuple []) (Tuple [Name "T" [], Name "List" [("T", Name "T" [])]])
  let ty2 = Tuple [Name "T" [], Name "List" [("T", Name "T" [])]]
  let (gr1, n1) = translateDecl "List" ty1 ["T"] empty
  let (gr2, n2) = translateDecl "NeList" ty2 ["T"] gr1
  --print $ graph2type (n1, Map.fromList [("T", 0)]) gr2
  --putStrLn $ Dot.showDot $ Dot.fglToDot (snd gr2)
  let (b, _, _) = subtype Set.empty (7, Map.fromList [("T", 0)]) (1, Map.fromList [("T", 0)]) Map.empty gr2
  print $ b