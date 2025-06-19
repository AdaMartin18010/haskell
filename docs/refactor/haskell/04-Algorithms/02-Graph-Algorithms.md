# 4.2 Graph Algorithms

## 4.2.1 Mathematical Foundation

### 4.2.1.1 Graph Definition

A **graph** $G$ is an ordered pair $(V, E)$ where:

- $V$ is a set of vertices (nodes)
- $E \subseteq V \times V$ is a set of edges (arcs)

Types of graphs:

- **Directed graph (digraph):** $E \subseteq V \times V$
- **Undirected graph:** $E \subseteq \{\{u, v\} \mid u, v \in V\}$
- **Weighted graph:** $w: E \to \mathbb{R}$ assigns weights to edges

### 4.2.1.2 Graph Representations

- **Adjacency list:** $\forall v \in V, \text{adj}(v) = \{u \mid (v, u) \in E\}$
- **Adjacency matrix:** $A_{ij} = 1$ if $(v_i, v_j) \in E$, else $0$

```haskell
-- Adjacency list representation
type Vertex = Int
type Graph = Map Vertex [Vertex]

-- Weighted graph
type Weight = Int
type WGraph = Map Vertex [(Vertex, Weight)]
```

## 4.2.2 Traversal Algorithms

### 4.2.2.1 Depth-First Search (DFS)

DFS explores as far as possible along each branch before backtracking.

```haskell
import qualified Data.Set as Set
import qualified Data.Map as Map

dfs :: Graph -> Vertex -> [Vertex]
dfs graph start = dfs' Set.empty start
  where
    dfs' visited v
      | Set.member v visited = []
      | otherwise = v : concatMap (dfs' (Set.insert v visited)) (Map.findWithDefault [] v graph)
```

### 4.2.2.2 Breadth-First Search (BFS)

BFS explores all neighbors at the present depth before moving to the next level.

```haskell
import qualified Data.Sequence as Seq
import qualified Data.Foldable as Foldable

bfs :: Graph -> Vertex -> [Vertex]
bfs graph start = bfs' Set.empty (Seq.singleton start)
  where
    bfs' _ Seq.Empty = []
    bfs' visited (v Seq.:<| queue)
      | Set.member v visited = bfs' visited queue
      | otherwise = v : bfs' (Set.insert v visited) (queue Seq.>< Seq.fromList (Map.findWithDefault [] v graph))
```

## 4.2.3 Shortest Path Algorithms

### 4.2.3.1 Dijkstra's Algorithm

Finds the shortest path from a source to all vertices in a weighted graph with non-negative weights.

```haskell
import qualified Data.PSQueue as PQ
import Data.Maybe (fromMaybe)

dijkstra :: WGraph -> Vertex -> Map Vertex Weight
dijkstra graph source = dijkstra' (PQ.singleton source 0) Map.empty
  where
    dijkstra' queue dist
      | PQ.null queue = dist
      | otherwise =
          let Just (v PQ.:-> d, queue') = PQ.minView queue
              neighbors = Map.findWithDefault [] v graph
              (queue'', dist') = foldl (relax v d) (queue', dist) neighbors
          in dijkstra' queue'' dist'
    relax v d (q, m) (u, w) =
      let alt = d + w
          old = Map.lookup u m
      in if maybe True (alt <) old
         then (PQ.insert u alt q, Map.insert u alt m)
         else (q, m)
```

### 4.2.3.2 Bellman-Ford Algorithm

Handles graphs with negative weights and detects negative cycles.

```haskell
bellmanFord :: Int -> [(Vertex, Vertex, Weight)] -> Vertex -> Maybe (Map Vertex Weight)
bellmanFord nEdges edges source =
  let dist0 = Map.fromList [(v, if v == source then 0 else maxBound) | v <- [0..nEdges-1]]
      relax dist (u, v, w) =
        let du = fromMaybe maxBound (Map.lookup u dist)
            dv = fromMaybe maxBound (Map.lookup v dist)
        in if du /= maxBound && du + w < dv
           then Map.insert v (du + w) dist
           else dist
      distN = iterate (\d -> foldl relax d edges) dist0 !! nEdges
      hasNegCycle = any (\(u, v, w) -> let du = fromMaybe maxBound (Map.lookup u distN)
                                            dv = fromMaybe maxBound (Map.lookup v distN)
                                        in du /= maxBound && du + w < dv) edges
  in if hasNegCycle then Nothing else Just distN
```

## 4.2.4 Minimum Spanning Tree Algorithms

### 4.2.4.1 Kruskal's Algorithm

Finds a minimum spanning tree (MST) for a connected weighted undirected graph.

```haskell
import Data.List (sortOn)
import qualified Data.Map as Map
import qualified Data.Set as Set

type Edge = (Vertex, Vertex, Weight)

kruskal :: [Edge] -> [Edge]
kruskal edges = kruskal' (sortOn thd edges) Map.empty []
  where
    thd (_,_,w) = w
    find parent v = if Map.findWithDefault v v parent == v then v else find parent (Map.findWithDefault v v parent)
    union parent u v = Map.insert (find parent u) (find parent v) parent
    kruskal' [] _ mst = mst
    kruskal' ((u,v,w):es) parent mst
      | find parent u /= find parent v = kruskal' es (union parent u v) ((u,v,w):mst)
      | otherwise = kruskal' es parent mst
```

### 4.2.4.2 Prim's Algorithm

Builds the MST by growing a single tree.

```haskell
import qualified Data.PSQueue as PQ
import qualified Data.Set as Set

prim :: WGraph -> Vertex -> [(Vertex, Vertex, Weight)]
prim graph start = prim' Set.empty (PQ.singleton start 0) []
  where
    prim' visited queue mst
      | PQ.null queue = mst
      | otherwise =
          let Just (v PQ.:-> w, queue') = PQ.minView queue
              visited' = Set.insert v visited
              edges = [(v, u, w') | (u, w') <- Map.findWithDefault [] v graph, not (Set.member u visited')]
              queue'' = foldl (\q (u,_,w') -> PQ.insert u w' q) queue' edges
              mst' = if w /= 0 then (v, v, w):mst else mst
          in prim' visited' queue'' mst'
```

## 4.2.5 Topological Sorting

### 4.2.5.1 Kahn's Algorithm

Finds a topological ordering of a directed acyclic graph (DAG).

```haskell
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Sequence as Seq

topologicalSort :: Graph -> [Vertex]
topologicalSort graph = kahn (Map.keysSet graph) (Map.map length graph) Seq.empty []
  where
    kahn nodes inDeg queue result
      | Set.null nodes = Foldable.toList result
      | otherwise =
          let (zeroIn, rest) = Set.partition (\v -> Map.findWithDefault 0 v inDeg == 0) nodes
              queue' = queue Seq.>< Seq.fromList (Set.toList zeroIn)
              inDeg' = foldl (\m v -> foldl (\m' u -> Map.adjust (subtract 1) u m') m (Map.findWithDefault [] v graph)) inDeg (Set.toList zeroIn)
          in if Seq.null queue' then []
             else let (v Seq.:<| q) = queue'
                  in kahn (Set.delete v rest) inDeg' q (result Seq.|> v)
```

## 4.2.6 Complexity Analysis

| Algorithm         | Time Complexity | Space Complexity |
|-------------------|----------------|------------------|
| DFS/BFS           | $O(V+E)$        | $O(V)$           |
| Dijkstra          | $O((V+E)\log V)$| $O(V)$           |
| Bellman-Ford      | $O(VE)$         | $O(V)$           |
| Kruskal           | $O(E\log E)$    | $O(V)$           |
| Prim              | $O((V+E)\log V)$| $O(V)$           |
| Topological Sort  | $O(V+E)$        | $O(V)$           |

## 4.2.7 References

- [4.1 Sorting Algorithms](01-Sorting-Algorithms.md)
- [3.3 Advanced Data Structures](../03-Data-Structures/03-Advanced-Data-Structures.md)
- [3.5 Functional Data Structures](../03-Data-Structures/05-Functional-Data-Structures.md)

---

**Next:** [4.3 Dynamic Programming](03-Dynamic-Programming.md)
