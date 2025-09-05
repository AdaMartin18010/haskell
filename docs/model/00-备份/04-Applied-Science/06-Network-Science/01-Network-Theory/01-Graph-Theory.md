# 图论基础

## 1. 图的基本概念

### 1.1 图的定义

**定义 1.1**（图）：图 $G = (V, E)$ 是一个有序对，其中：

- $V$ 是顶点（节点）的有限集合
- $E$ 是边的集合，每个边是 $V$ 中两个顶点的无序对

**定义 1.2**（有向图）：有向图 $G = (V, E)$ 是一个有序对，其中：

- $V$ 是顶点的有限集合
- $E$ 是弧的集合，每个弧是 $V$ 中两个顶点的有序对

```haskell
-- 图的基本数据类型
data Graph a = Graph
  { vertices :: Set a
  , edges :: Set (a, a)
  } deriving (Show, Eq)

data DirectedGraph a = DirectedGraph
  { vertices :: Set a
  , arcs :: Set (a, a)
  } deriving (Show, Eq)

-- 加权图
data WeightedGraph a w = WeightedGraph
  { vertices :: Set a
  , weightedEdges :: Set (a, a, w)
  } deriving (Show, Eq)

-- 图的类型类
class GraphType g where
  getVertices :: g a -> Set a
  getEdges :: g a -> Set (a, a)
  isEmpty :: g a -> Bool
  order :: g a -> Int
  size :: g a -> Int

-- 实例化
instance GraphType Graph where
  getVertices = vertices
  getEdges = edges
  isEmpty g = Set.null (vertices g)
  order g = Set.size (vertices g)
  size g = Set.size (edges g)
```

### 1.2 图的基本性质

#### 1.2.1 度

**定义 1.3**（度）：顶点 $v$ 的度 $deg(v)$ 是与 $v$ 相邻的边的数量。

```haskell
-- 计算顶点的度
degree :: (Ord a, GraphType g) => g a -> a -> Int
degree graph v =
  let edges = getEdges graph
      adjacentEdges = Set.filter (\(u, w) -> u == v || w == v) edges
  in Set.size adjacentEdges

-- 计算所有顶点的度
degreeSequence :: (Ord a, GraphType g) => g a -> [Int]
degreeSequence graph =
  let vertices = Set.toList (getVertices graph)
  in map (degree graph) vertices

-- 度分布
degreeDistribution :: (Ord a, GraphType g) => g a -> Map Int Int
degreeDistribution graph =
  let degrees = degreeSequence graph
  in Map.fromListWith (+) [(d, 1) | d <- degrees]
```

#### 1.2.2 路径和连通性

**定义 1.4**（路径）：路径是顶点序列 $v_0, v_1, \ldots, v_k$，其中 $(v_i, v_{i+1}) \in E$ 对所有 $i = 0, 1, \ldots, k-1$。

```haskell
-- 路径表示
type Path a = [a]

-- 检查路径是否有效
isValidPath :: (Ord a, GraphType g) => g a -> Path a -> Bool
isValidPath graph path =
  case path of
    [] -> True
    [_] -> True
    (u:v:rest) ->
      let edge = if u < v then (u, v) else (v, u)
      in edge `Set.member` getEdges graph && isValidPath graph (v:rest)

-- 路径长度
pathLength :: Path a -> Int
pathLength path = max 0 (length path - 1)

-- 简单路径（无重复顶点）
isSimplePath :: Path a -> Bool
isSimplePath path = length path == length (nub path)
```

#### 1.2.3 连通性

**定义 1.5**（连通图）：图 $G$ 是连通的，如果对于任意两个顶点 $u, v$，存在从 $u$ 到 $v$ 的路径。

```haskell
-- 检查图的连通性
isConnected :: (Ord a, GraphType g) => g a -> Bool
isConnected graph =
  let vertices = Set.toList (getVertices graph)
      components = connectedComponents graph
  in length components == 1

-- 连通分量
connectedComponents :: (Ord a, GraphType g) => g a -> [[a]]
connectedComponents graph =
  let vertices = Set.toList (getVertices graph)
      visited = Set.empty
  in dfsComponents graph vertices visited

-- 深度优先搜索找连通分量
dfsComponents :: (Ord a, GraphType g) => g a -> [a] -> Set a -> [[a]]
dfsComponents graph [] visited = []
dfsComponents graph (v:vs) visited
  | v `Set.member` visited = dfsComponents graph vs visited
  | otherwise =
      let component = dfs graph v Set.empty
          newVisited = Set.union visited (Set.fromList component)
      in component : dfsComponents graph vs newVisited

-- 深度优先搜索
dfs :: (Ord a, GraphType g) => g a -> a -> Set a -> [a]
dfs graph v visited
  | v `Set.member` visited = []
  | otherwise =
      let newVisited = Set.insert v visited
          neighbors = getNeighbors graph v
          neighborResults = concatMap (\n -> dfs graph n newVisited) neighbors
      in v : neighborResults

-- 获取邻居
getNeighbors :: (Ord a, GraphType g) => g a -> a -> [a]
getNeighbors graph v =
  let edges = getEdges graph
      adjacentEdges = Set.filter (\(u, w) -> u == v || w == v) edges
  in [if u == v then w else u | (u, w) <- Set.toList adjacentEdges]
```

## 2. 图的表示

### 2.1 邻接矩阵

**定义 2.1**（邻接矩阵）：图 $G = (V, E)$ 的邻接矩阵 $A$ 是一个 $n \times n$ 矩阵，其中 $A_{ij} = 1$ 如果 $(i, j) \in E$，否则 $A_{ij} = 0$。

```haskell
-- 邻接矩阵表示
type AdjacencyMatrix = Array (Int, Int) Bool

-- 从图创建邻接矩阵
toAdjacencyMatrix :: (Ord a, Enum a, Bounded a) => Graph a -> AdjacencyMatrix
toAdjacencyMatrix graph =
  let vertices = Set.toList (getVertices graph)
      edges = getEdges graph
      n = length vertices
      vertexMap = Map.fromList (zip vertices [0..])
      
      -- 初始化矩阵
      initialMatrix = array ((0,0), (n-1,n-1)) 
                          [((i,j), False) | i <- [0..n-1], j <- [0..n-1]]
      
      -- 填充边
      fillEdges = foldl (\matrix (u, v) ->
        let i = vertexMap Map.! u
            j = vertexMap Map.! v
        in matrix // [((i,j), True), ((j,i), True)]) initialMatrix
  in fillEdges

-- 从邻接矩阵创建图
fromAdjacencyMatrix :: AdjacencyMatrix -> Graph Int
fromAdjacencyMatrix matrix =
  let bounds = bounds matrix
      ((minI, minJ), (maxI, maxJ)) = bounds
      vertices = Set.fromList [minI..maxI]
      edges = Set.fromList [(i, j) | i <- [minI..maxI], j <- [i..maxJ], matrix ! (i, j)]
  in Graph vertices edges
```

### 2.2 邻接表

**定义 2.2**（邻接表）：邻接表是图的另一种表示方法，为每个顶点维护一个邻居列表。

```haskell
-- 邻接表表示
type AdjacencyList a = Map a [a]

-- 从图创建邻接表
toAdjacencyList :: (Ord a, GraphType g) => g a -> AdjacencyList a
toAdjacencyList graph =
  let vertices = Set.toList (getVertices graph)
      edges = getEdges graph
      
      -- 为每个顶点创建邻居列表
      neighborsForVertex v = 
        [if u == v then w else u | (u, w) <- Set.toList edges, u == v || w == v]
      
      adjacencyLists = [(v, neighborsForVertex v) | v <- vertices]
  in Map.fromList adjacencyLists

-- 从邻接表创建图
fromAdjacencyList :: (Ord a) => AdjacencyList a -> Graph a
fromAdjacencyList adjList =
  let vertices = Set.fromList (Map.keys adjList)
      edges = Set.fromList [(v, w) | (v, neighbors) <- Map.toList adjList, w <- neighbors]
  in Graph vertices edges
```

### 2.3 边列表

```haskell
-- 边列表表示
type EdgeList a = [(a, a)]

-- 从图创建边列表
toEdgeList :: Graph a -> EdgeList a
toEdgeList graph = Set.toList (edges graph)

-- 从边列表创建图
fromEdgeList :: (Ord a) => EdgeList a -> Graph a
fromEdgeList edgeList =
  let vertices = Set.fromList (concat [[u, v] | (u, v) <- edgeList])
      edges = Set.fromList edgeList
  in Graph vertices edges
```

## 3. 图算法

### 3.1 最短路径算法

#### 3.1.1 Dijkstra算法

**定理 3.1**（Dijkstra算法）：Dijkstra算法可以在 $O(|V|^2)$ 时间内找到从源点到所有其他顶点的最短路径。

```haskell
-- Dijkstra算法
dijkstra :: (Ord a, Num w, Ord w) => WeightedGraph a w -> a -> Map a (w, Maybe a)
dijkstra graph source =
  let vertices = Set.toList (getVertices graph)
      edges = getWeightedEdges graph
      
      -- 初始化距离和前驱
      initialDistances = Map.fromList [(v, (maxBound, Nothing)) | v <- vertices]
      initialDistances' = Map.insert source (0, Nothing) initialDistances
      
      -- 主循环
      dijkstraLoop distances unvisited =
        if Set.null unvisited then distances
        else
          let -- 找到未访问顶点中距离最小的
              (current, _) = minimumBy (comparing (fst . (distances Map.!))) (Set.toList unvisited)
              newUnvisited = Set.delete current unvisited
              
              -- 更新邻居距离
              neighbors = getWeightedNeighbors graph current
              newDistances = foldl (\dist (neighbor, weight) ->
                let currentDist = fst (dist Map.! current)
                    neighborDist = fst (dist Map.! neighbor)
                    newDist = currentDist + weight
                in if newDist < neighborDist 
                   then Map.insert neighbor (newDist, Just current) dist
                   else dist) distances neighbors
          in dijkstraLoop newDistances newUnvisited
      
      unvisited = Set.fromList vertices
  in dijkstraLoop initialDistances' unvisited

-- 获取加权邻居
getWeightedNeighbors :: (Ord a, Num w) => WeightedGraph a w -> a -> [(a, w)]
getWeightedNeighbors graph v =
  let edges = getWeightedEdges graph
      adjacentEdges = Set.filter (\(u, w, weight) -> u == v || w == v) edges
  in [(if u == v then w else u, weight) | (u, w, weight) <- Set.toList adjacentEdges]
```

#### 3.1.2 Floyd-Warshall算法

**定理 3.2**（Floyd-Warshall算法）：Floyd-Warshall算法可以在 $O(|V|^3)$ 时间内找到所有顶点对之间的最短路径。

```haskell
-- Floyd-Warshall算法
floydWarshall :: (Ord a, Num w, Ord w) => WeightedGraph a w -> Array (a, a) (w, Maybe a)
floydWarshall graph =
  let vertices = Set.toList (getVertices graph)
      edges = getWeightedEdges graph
      
      -- 初始化距离矩阵
      initialDistances = array ((v1, v2) | v1 <- vertices, v2 <- vertices)
                              [((v1, v2), if v1 == v2 then (0, Nothing)
                                         else case findEdge v1 v2 edges of
                                                Just weight -> (weight, Just v1)
                                                Nothing -> (maxBound, Nothing))
                               | v1 <- vertices, v2 <- vertices]
      
      -- 主循环
      floydLoop distances k =
        if k > length vertices then distances
        else
          let vk = vertices !! (k - 1)
              newDistances = array (bounds distances)
                                  [((i, j), 
                                    let dist_ij = fst (distances ! (i, j))
                                        dist_ik = fst (distances ! (i, vk))
                                        dist_kj = fst (distances ! (vk, j))
                                        newDist = dist_ik + dist_kj
                                    in if newDist < dist_ij && dist_ik /= maxBound && dist_kj /= maxBound
                                       then (newDist, Just vk)
                                       else distances ! (i, j))
                                   | (i, j) <- range (bounds distances)]
          in floydLoop newDistances (k + 1)
      
  in floydLoop initialDistances 1

-- 查找边
findEdge :: (Ord a, Num w) => a -> a -> Set (a, a, w) -> Maybe w
findEdge u v edges =
  let edge = Set.lookupMin (Set.filter (\(x, y, _) -> (x == u && y == v) || (x == v && y == u)) edges)
  in case edge of
       Just (_, _, weight) -> Just weight
       Nothing -> Nothing
```

### 3.2 最小生成树算法

#### 3.2.1 Kruskal算法

**定理 3.3**（Kruskal算法）：Kruskal算法可以在 $O(|E| \log |E|)$ 时间内找到图的最小生成树。

```haskell
-- Kruskal算法
kruskal :: (Ord a, Num w, Ord w) => WeightedGraph a w -> WeightedGraph a w
kruskal graph =
  let edges = Set.toList (getWeightedEdges graph)
      sortedEdges = sortBy (comparing (\(_, _, w) -> w)) edges
      vertices = getVertices graph
      
      -- 并查集
      initialForest = Map.fromList [(v, v) | v <- Set.toList vertices]
      
      -- 查找根
      findRoot forest v =
        let parent = forest Map.! v
        in if parent == v then v else findRoot forest parent
      
      -- 合并集合
      union forest u v =
        let rootU = findRoot forest u
            rootV = findRoot forest v
        in Map.insert rootU rootV forest
      
      -- 主循环
      kruskalLoop forest [] = []
      kruskalLoop forest ((u, v, w):es) =
        let rootU = findRoot forest u
            rootV = findRoot forest v
        in if rootU == rootV
           then kruskalLoop forest es
           else (u, v, w) : kruskalLoop (union forest u v) es
      
      mstEdges = kruskalLoop initialForest sortedEdges
  in WeightedGraph vertices (Set.fromList mstEdges)
```

#### 3.2.2 Prim算法

**定理 3.4**（Prim算法）：Prim算法可以在 $O(|V|^2)$ 时间内找到图的最小生成树。

```haskell
-- Prim算法
prim :: (Ord a, Num w, Ord w) => WeightedGraph a w -> WeightedGraph a w
prim graph =
  let vertices = Set.toList (getVertices graph)
      edges = getWeightedEdges graph
      
      -- 初始化
      startVertex = head vertices
      initialTree = Set.singleton startVertex
      initialEdges = Set.empty
      
      -- 找到连接树和剩余顶点的最小边
      findMinEdge tree remaining =
        let crossEdges = Set.filter (\(u, v, _) -> 
          (u `Set.member` tree && v `Set.notMember` tree) ||
          (v `Set.member` tree && u `Set.notMember` tree)) edges
        in if Set.null crossEdges then Nothing
           else Just (Set.findMin crossEdges)
      
      -- 主循环
      primLoop tree remaining mstEdges =
        if Set.null remaining then mstEdges
        else
          case findMinEdge tree remaining of
            Nothing -> mstEdges
            Just (u, v, w) ->
              let newTree = Set.insert (if u `Set.member` tree then v else u) tree
                  newRemaining = Set.delete (if u `Set.member` tree then v else u) remaining
                  newMstEdges = Set.insert (u, v, w) mstEdges
              in primLoop newTree newRemaining newMstEdges
      
      remainingVertices = Set.fromList (tail vertices)
      mstEdges = primLoop initialTree remainingVertices initialEdges
  in WeightedGraph (getVertices graph) mstEdges
```

### 3.3 拓扑排序

**定义 3.1**（拓扑排序）：有向无环图的拓扑排序是顶点的一个线性排序，使得对于每条边 $(u, v)$，$u$ 在排序中出现在 $v$ 之前。

```haskell
-- 拓扑排序
topologicalSort :: (Ord a) => DirectedGraph a -> Maybe [a]
topologicalSort graph =
  let vertices = Set.toList (getVertices graph)
      arcs = getArcs graph
      
      -- 计算入度
      inDegree v = length [u | (u, w) <- Set.toList arcs, w == v]
      inDegrees = Map.fromList [(v, inDegree v) | v <- vertices]
      
      -- 找到入度为0的顶点
      findZeroInDegree degrees = 
        [v | (v, deg) <- Map.toList degrees, deg == 0]
      
      -- 更新入度
      updateInDegrees degrees [] = degrees
      updateInDegrees degrees (v:vs) =
        let neighbors = [w | (u, w) <- Set.toList arcs, u == v]
            newDegrees = foldl (\deg w -> Map.adjust (\d -> d - 1) w deg) degrees neighbors
        in updateInDegrees newDegrees vs
      
      -- 主循环
      topoSortLoop degrees result =
        let zeroInDegree = findZeroInDegree degrees
        in if null zeroInDegree
           then if Map.null degrees then Just (reverse result) else Nothing
           else
             let v = head zeroInDegree
                 newDegrees = Map.delete v degrees
                 updatedDegrees = updateInDegrees newDegrees [v]
             in topoSortLoop updatedDegrees (v:result)
      
  in topoSortLoop inDegrees []
```

## 4. 图的数学性质

### 4.1 欧拉图和哈密顿图

#### 4.1.1 欧拉路径和欧拉回路

**定理 4.1**（欧拉定理）：连通图 $G$ 有欧拉回路的充要条件是所有顶点的度都是偶数。

```haskell
-- 检查欧拉回路
hasEulerCircuit :: (Ord a, GraphType g) => g a -> Bool
hasEulerCircuit graph =
  isConnected graph && all (even . degree graph) (Set.toList (getVertices graph))

-- 检查欧拉路径
hasEulerPath :: (Ord a, GraphType g) => g a -> Bool
hasEulerPath graph =
  isConnected graph && 
  let oddDegrees = filter (odd . degree graph) (Set.toList (getVertices graph))
  in length oddDegrees == 0 || length oddDegrees == 2

-- 找到欧拉回路
findEulerCircuit :: (Ord a, GraphType g) => g a -> Maybe [a]
findEulerCircuit graph
  | not (hasEulerCircuit graph) = Nothing
  | otherwise = Just (eulerCircuitLoop graph (head (Set.toList (getVertices graph))) [])

-- 欧拉回路算法
eulerCircuitLoop :: (Ord a, GraphType g) => g a -> a -> [a] -> [a]
eulerCircuitLoop graph current path =
  let neighbors = getNeighbors graph current
      availableEdges = filter (\n -> hasEdge graph current n) neighbors
  in if null availableEdges
     then current:path
     else
       let next = head availableEdges
           newGraph = removeEdge graph current next
       in eulerCircuitLoop newGraph next (current:path)

-- 移除边
removeEdge :: (Ord a, GraphType g) => g a -> a -> a -> g a
removeEdge graph u v =
  let edges = getEdges graph
      newEdges = Set.delete (if u < v then (u, v) else (v, u)) edges
  in -- 这里需要根据具体的图类型实现
     undefined
```

#### 4.1.2 哈密顿路径和哈密顿回路

**定义 4.1**（哈密顿回路）：哈密顿回路是经过图中每个顶点恰好一次的回路。

```haskell
-- 检查哈密顿回路
hasHamiltonianCircuit :: (Ord a, GraphType g) => g a -> Bool
hasHamiltonianCircuit graph =
  let vertices = Set.toList (getVertices graph)
      n = length vertices
  in n >= 3 && hamiltonianCircuitExists graph vertices

-- 哈密顿回路存在性检查（简化版本）
hamiltonianCircuitExists :: (Ord a, GraphType g) => g a -> [a] -> Bool
hamiltonianCircuitExists graph vertices =
  let allPermutations = permutations vertices
      validCircuits = filter (\perm -> isValidHamiltonianCircuit graph perm) allPermutations
  in not (null validCircuits)

-- 检查是否为有效的哈密顿回路
isValidHamiltonianCircuit :: (Ord a, GraphType g) => g a -> [a] -> Bool
isValidHamiltonianCircuit graph path =
  let n = length path
      edges = [(path !! i, path !! ((i + 1) `mod` n)) | i <- [0..n-1]]
  in all (\(u, v) -> hasEdge graph u v) edges

-- 检查边是否存在
hasEdge :: (Ord a, GraphType g) => g a -> a -> a -> Bool
hasEdge graph u v =
  let edge = if u < v then (u, v) else (v, u)
  in edge `Set.member` getEdges graph
```

### 4.2 匹配和覆盖

#### 4.2.1 最大匹配

**定义 4.2**（匹配）：匹配是图中边的一个子集，其中任意两条边都不共享顶点。

```haskell
-- 最大匹配
maximumMatching :: (Ord a, GraphType g) => g a -> Set (a, a)
maximumMatching graph =
  let edges = Set.toList (getEdges graph)
      allMatchings = generateAllMatchings edges
      validMatchings = filter (isValidMatching graph) allMatchings
  in if null validMatchings then Set.empty
     else Set.fromList (maximumBy (comparing length) validMatchings)

-- 生成所有可能的匹配
generateAllMatchings :: [(a, a)] -> [[(a, a)]]
generateAllMatchings [] = [[]]
generateAllMatchings (e:es) =
  let withoutEdge = generateAllMatchings es
      withEdge = map (e:) (generateAllMatchings (filter (not . sharesVertex e) es))
  in withoutEdge ++ withEdge

-- 检查两条边是否共享顶点
sharesVertex :: (Eq a) => (a, a) -> (a, a) -> Bool
sharesVertex (u1, v1) (u2, v2) = u1 == u2 || u1 == v2 || v1 == u2 || v1 == v2

-- 检查是否为有效匹配
isValidMatching :: (Ord a, GraphType g) => g a -> [(a, a)] -> Bool
isValidMatching graph edges =
  let vertices = concat [[u, v] | (u, v) <- edges]
  in length vertices == length (nub vertices)
```

#### 4.2.2 最小顶点覆盖

**定义 4.3**（顶点覆盖）：顶点覆盖是顶点的一个子集，使得图中的每条边至少有一个端点在该子集中。

```haskell
-- 最小顶点覆盖（近似算法）
minimumVertexCover :: (Ord a, GraphType g) => g a -> Set a
minimumVertexCover graph =
  let edges = Set.toList (getEdges graph)
      cover = Set.empty
  in vertexCoverGreedy edges cover

-- 贪心顶点覆盖算法
vertexCoverGreedy :: (Ord a) => [(a, a)] -> Set a -> Set a
vertexCoverGreedy [] cover = cover
vertexCoverGreedy ((u, v):es) cover =
  if u `Set.member` cover || v `Set.member` cover
  then vertexCoverGreedy es cover
  else vertexCoverGreedy es (Set.insert u cover)
```

## 5. 图的着色

### 5.1 顶点着色

**定义 5.1**（顶点着色）：顶点着色是为图的每个顶点分配一个颜色，使得相邻顶点具有不同颜色。

```haskell
-- 顶点着色
vertexColoring :: (Ord a, GraphType g) => g a -> Map a Int
vertexColoring graph =
  let vertices = Set.toList (getVertices graph)
      initialColoring = Map.empty
  in greedyColoring graph vertices initialColoring

-- 贪心着色算法
greedyColoring :: (Ord a, GraphType g) => g a -> [a] -> Map a Int -> Map a Int
greedyColoring graph [] coloring = coloring
greedyColoring graph (v:vs) coloring =
  let neighbors = getNeighbors graph v
      usedColors = Set.fromList [coloring Map.! u | u <- neighbors, u `Map.member` coloring]
      availableColor = findAvailableColor usedColors
      newColoring = Map.insert v availableColor coloring
  in greedyColoring graph vs newColoring

-- 找到可用的颜色
findAvailableColor :: Set Int -> Int
findAvailableColor usedColors =
  let allColors = [0..]
      availableColor = head [c | c <- allColors, c `Set.notMember` usedColors]
  in availableColor

-- 检查着色是否有效
isValidColoring :: (Ord a, GraphType g) => g a -> Map a Int -> Bool
isValidColoring graph coloring =
  let edges = getEdges graph
      invalidEdges = filter (\(u, v) -> 
        coloring Map.! u == coloring Map.! v) (Set.toList edges)
  in null invalidEdges
```

### 5.2 边着色

**定义 5.2**（边着色）：边着色是为图的每条边分配一个颜色，使得共享顶点的边具有不同颜色。

```haskell
-- 边着色
edgeColoring :: (Ord a, GraphType g) => g a -> Map (a, a) Int
edgeColoring graph =
  let edges = Set.toList (getEdges graph)
      initialColoring = Map.empty
  in greedyEdgeColoring graph edges initialColoring

-- 贪心边着色算法
greedyEdgeColoring :: (Ord a, GraphType g) => g a -> [(a, a)] -> Map (a, a) Int -> Map (a, a) Int
greedyEdgeColoring graph [] coloring = coloring
greedyEdgeColoring graph (e@(u, v):es) coloring =
  let incidentEdges = getIncidentEdges graph u ++ getIncidentEdges graph v
      usedColors = Set.fromList [coloring Map.! edge | edge <- incidentEdges, edge `Map.member` coloring]
      availableColor = findAvailableColor usedColors
      newColoring = Map.insert e availableColor coloring
  in greedyEdgeColoring graph es newColoring

-- 获取与顶点相关的边
getIncidentEdges :: (Ord a, GraphType g) => g a -> a -> [(a, a)]
getIncidentEdges graph v =
  let edges = getEdges graph
  in [(u, w) | (u, w) <- Set.toList edges, u == v || w == v]
```

## 6. 图的分解

### 6.1 连通分量分解

```haskell
-- 强连通分量（有向图）
stronglyConnectedComponents :: (Ord a) => DirectedGraph a -> [[a]]
stronglyConnectedComponents graph =
  let vertices = Set.toList (getVertices graph)
      -- 第一次DFS
      (finishTimes, _) = dfsWithFinishTimes graph vertices Map.empty 1
      -- 按完成时间排序
      sortedVertices = sortBy (flip compare) [v | (v, _) <- Map.toList finishTimes]
      -- 转置图
      transposedGraph = transposeGraph graph
      -- 第二次DFS
      components = dfsComponentsTransposed transposedGraph sortedVertices Set.empty []
  in components

-- DFS with finish times
dfsWithFinishTimes :: (Ord a) => DirectedGraph a -> [a] -> Map a Int -> Int -> (Map a Int, Int)
dfsWithFinishTimes graph [] finishTimes time = (finishTimes, time)
dfsWithFinishTimes graph (v:vs) finishTimes time
  | v `Map.member` finishTimes = dfsWithFinishTimes graph vs finishTimes time
  | otherwise =
      let (newFinishTimes, newTime) = dfsVisit graph v finishTimes time
      in dfsWithFinishTimes graph vs newFinishTimes newTime

-- DFS visit
dfsVisit :: (Ord a) => DirectedGraph a -> a -> Map a Int -> Int -> (Map a Int, Int)
dfsVisit graph v finishTimes time =
  let neighbors = getDirectedNeighbors graph v
      (newFinishTimes, newTime) = foldl (\acc neighbor ->
        if neighbor `Map.member` (fst acc)
        then acc
        else dfsVisit graph neighbor (fst acc) (snd acc)) (finishTimes, time + 1) neighbors
      finalTime = newTime + 1
  in (Map.insert v finalTime newFinishTimes, finalTime)

-- 转置图
transposeGraph :: (Ord a) => DirectedGraph a -> DirectedGraph a
transposeGraph graph =
  let arcs = getArcs graph
      transposedArcs = Set.map (\(u, v) -> (v, u)) arcs
  in DirectedGraph (getVertices graph) transposedArcs
```

### 6.2 双连通分量

```haskell
-- 双连通分量
biconnectedComponents :: (Ord a, GraphType g) => g a -> [[a]]
biconnectedComponents graph =
  let vertices = Set.toList (getVertices graph)
      components = tarjanBCC graph vertices Map.empty Map.empty 1 []
  in components

-- Tarjan算法找双连通分量
tarjanBCC :: (Ord a, GraphType g) => g a -> [a] -> Map a Int -> Map a Int -> Int -> [[a]] -> [[a]]
tarjanBCC graph [] _ _ _ components = components
tarjanBCC graph (v:vs) discovery low stack components
  | v `Map.member` discovery = tarjanBCC graph vs discovery low stack components
  | otherwise =
      let (newDiscovery, newLow, newStack, newComponents) = 
            tarjanBCCVisit graph v v discovery low stack components
      in tarjanBCC graph vs newDiscovery newLow newStack newComponents

-- Tarjan BCC visit
tarjanBCCVisit :: (Ord a, GraphType g) => g a -> a -> a -> Map a Int -> Map a Int -> [a] -> [[a]] -> (Map a Int, Map a Int, [a], [[a]])
tarjanBCCVisit graph v parent discovery low stack components =
  let newDiscovery = Map.insert v (Map.size discovery + 1) discovery
      newLow = Map.insert v (newDiscovery Map.! v) low
      newStack = v:stack
      neighbors = getNeighbors graph v
      
      (finalDiscovery, finalLow, finalStack, finalComponents) = 
        foldl (\acc neighbor ->
          if neighbor == parent
          then acc
          else if neighbor `Map.member` (fst acc)
               then let currentLow = min (snd acc Map.! v) (fst acc Map.! neighbor)
                    in (fst acc, Map.insert v currentLow (snd acc), fst (fst (fst acc)), snd (fst (fst acc)))
               else let (d, l, s, c) = tarjanBCCVisit graph neighbor v (fst acc) (snd acc) (fst (fst (fst acc))) (snd (fst (fst acc)))
                        currentLow = min (l Map.! v) (l Map.! neighbor)
                        newLow = Map.insert v currentLow l
                    in (d, newLow, s, c)) (newDiscovery, newLow, newStack, components) neighbors
      
      -- 检查是否为割点
      isArticulationPoint = any (\neighbor -> 
        neighbor /= parent && (finalLow Map.! neighbor) >= (finalDiscovery Map.! v)) neighbors
      
      -- 如果v是割点，提取双连通分量
      (finalStack', finalComponents') = if isArticulationPoint
        then extractBCC v finalStack finalComponents
        else (finalStack, finalComponents)
  in (finalDiscovery, finalLow, finalStack', finalComponents')

-- 提取双连通分量
extractBCC :: (Ord a) => a -> [a] -> [[a]] -> ([a], [[a]])
extractBCC v stack components =
  let (component, remainingStack) = span (/= v) stack
      newComponent = v:component
      newStack = tail remainingStack
  in (newStack, newComponent:components)
```

## 7. 总结

图论为网络科学提供了坚实的数学基础。通过Haskell的函数式编程特性，我们可以优雅地实现各种图算法和数据结构。

关键要点：

1. 图的基本概念和表示方法
2. 经典图算法（最短路径、最小生成树、拓扑排序）
3. 图的数学性质（欧拉图、哈密顿图、匹配、着色）
4. 图的分解算法（连通分量、双连通分量）
5. 函数式编程在图论中的应用
