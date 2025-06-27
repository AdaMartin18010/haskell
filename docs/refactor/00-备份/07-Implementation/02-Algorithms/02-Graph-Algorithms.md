# 图算法 - 形式化理论与Haskell实现

## 📋 概述

图算法是计算机科学中的核心算法类别，用于解决图结构上的各种问题。本文档从形式化理论的角度分析各种图算法，并提供完整的Haskell实现。

## 🎯 形式化定义

### 图的基本概念

#### 图的数学定义

一个图 $G = (V, E)$ 由以下组成：

- **顶点集** $V$：非空有限集合
- **边集** $E$：$V \times V$ 的子集

#### 图的类型

1. **无向图**：$E \subseteq \{\{u, v\} : u, v \in V, u \neq v\}$
2. **有向图**：$E \subseteq \{(u, v) : u, v \in V, u \neq v\}$
3. **加权图**：$E \subseteq \{(u, v, w) : u, v \in V, w \in \mathbb{R}\}$

#### 图的性质

- **连通性**：任意两个顶点间存在路径
- **完全性**：任意两个顶点间都有边
- **平面性**：可以在平面上绘制且边不相交

## 🔧 Haskell实现

### 基础类型定义

```haskell
{-# LANGUAGE TypeFamilies, FlexibleContexts, MultiParamTypeClasses #-}

import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Data.List (find, delete)

-- 图的基本类型
data Graph v e = Graph
    { vertices :: Set v
    , edges :: Set e
    , edgeInfo :: Map e (v, v)
    }

-- 有向图
type DirectedGraph v = Graph v (v, v)

-- 无向图
type UndirectedGraph v = Graph v (v, v)

-- 加权图
type WeightedGraph v w = Graph v (v, v, w)

-- 图的邻接表表示
type AdjacencyList v = Map v [v]

-- 加权图的邻接表表示
type WeightedAdjacencyList v w = Map v [(v, w)]

-- 路径
type Path v = [v]

-- 算法结果类型
data AlgorithmResult a = AlgorithmResult
    { result :: a
    , steps :: Int
    , time :: Double
    , memory :: Int
    }

-- 图算法类型类
class GraphAlgorithm alg where
    type Input alg :: *
    type Output alg :: *
    execute :: alg -> Input alg -> Output alg
    algorithmName :: alg -> String
    complexity :: alg -> String
```

### 1. 深度优先搜索 (DFS)

#### 形式化定义

深度优先搜索是一种图遍历算法，沿着图的边尽可能深入地访问顶点。

**算法描述**：

1. 从起始顶点开始
2. 访问当前顶点
3. 递归访问所有未访问的邻居
4. 回溯到上一个顶点

#### Haskell实现

```haskell
-- 深度优先搜索
dfs :: Ord v => Graph v e -> v -> [v]
dfs graph start = dfs' graph start Set.empty []

dfs' :: Ord v => Graph v e -> v -> Set v -> [v] -> [v]
dfs' graph current visited result
  | current `Set.member` visited = result
  | otherwise = 
      let newVisited = Set.insert current visited
          newResult = result ++ [current]
          neighbors = getNeighbors graph current
          unvisitedNeighbors = filter (`Set.notMember` newVisited) neighbors
      in foldl (\acc neighbor -> dfs' graph neighbor newVisited acc) 
               newResult unvisitedNeighbors

-- 获取顶点的邻居
getNeighbors :: Ord v => Graph v e -> v -> [v]
getNeighbors graph v = 
    let allEdges = Set.toList $ edges graph
        edgeMap = edgeInfo graph
        connectedEdges = filter (\e -> 
            case Map.lookup e edgeMap of
                Just (u, w) -> u == v || w == v
                Nothing -> False) allEdges
    in [if u == v then w else u | e <- connectedEdges, 
        let (u, w) = fromMaybe (v, v) $ Map.lookup e edgeMap]

-- 带统计的DFS
dfsWithStats :: Ord v => Graph v e -> v -> AlgorithmResult [v]
dfsWithStats graph start = AlgorithmResult
    { result = result
    , steps = steps
    , time = 0.0
    , memory = memory
    }
  where
    (result, steps, memory) = dfsStats graph start Set.empty [] 0 0

dfsStats :: Ord v => Graph v e -> v -> Set v -> [v] -> Int -> Int -> ([v], Int, Int)
dfsStats graph current visited result steps memory
  | current `Set.member` visited = (result, steps, memory)
  | otherwise = 
      let newVisited = Set.insert current visited
          newResult = result ++ [current]
          newSteps = steps + 1
          newMemory = memory + 1
          neighbors = getNeighbors graph current
          unvisitedNeighbors = filter (`Set.notMember` newVisited) neighbors
      in foldl (\(acc, s, m) neighbor -> 
                   let (r, s', m') = dfsStats graph neighbor newVisited acc s m
                   in (r, s', m')) 
               (newResult, newSteps, newMemory) unvisitedNeighbors

-- 复杂度分析
dfsComplexity :: String
dfsComplexity = 
    "时间复杂度: O(V + E)\n" ++
    "空间复杂度: O(V)\n" ++
    "遍历方式: 深度优先\n" ++
    "应用: 拓扑排序、连通分量、强连通分量"
```

#### 性能分析

**时间复杂度**：$O(V + E)$
**空间复杂度**：$O(V)$（递归栈深度）

### 2. 广度优先搜索 (BFS)

#### 形式化定义

广度优先搜索是一种图遍历算法，先访问所有邻居，再访问邻居的邻居。

**算法描述**：

1. 从起始顶点开始，加入队列
2. 从队列取出顶点并访问
3. 将所有未访问的邻居加入队列
4. 重复步骤2-3直到队列为空

#### Haskell实现

```haskell
-- 广度优先搜索
bfs :: Ord v => Graph v e -> v -> [v]
bfs graph start = bfs' graph [start] Set.empty []

bfs' :: Ord v => Graph v e -> [v] -> Set v -> [v] -> [v]
bfs' graph [] visited result = result
bfs' graph (current:queue) visited result
  | current `Set.member` visited = bfs' graph queue visited result
  | otherwise = 
      let newVisited = Set.insert current visited
          newResult = result ++ [current]
          neighbors = getNeighbors graph current
          unvisitedNeighbors = filter (`Set.notMember` newVisited) neighbors
          newQueue = queue ++ unvisitedNeighbors
      in bfs' graph newQueue newVisited newResult

-- 带统计的BFS
bfsWithStats :: Ord v => Graph v e -> v -> AlgorithmResult [v]
bfsWithStats graph start = AlgorithmResult
    { result = result
    , steps = steps
    , time = 0.0
    , memory = memory
    }
  where
    (result, steps, memory) = bfsStats graph [start] Set.empty [] 0 0

bfsStats :: Ord v => Graph v e -> [v] -> Set v -> [v] -> Int -> Int -> ([v], Int, Int)
bfsStats graph [] visited result steps memory = (result, steps, memory)
bfsStats graph (current:queue) visited result steps memory
  | current `Set.member` visited = bfsStats graph queue visited result steps memory
  | otherwise = 
      let newVisited = Set.insert current visited
          newResult = result ++ [current]
          newSteps = steps + 1
          newMemory = memory + length queue
          neighbors = getNeighbors graph current
          unvisitedNeighbors = filter (`Set.notMember` newVisited) neighbors
          newQueue = queue ++ unvisitedNeighbors
      in bfsStats graph newQueue newVisited newResult newSteps newMemory

-- 复杂度分析
bfsComplexity :: String
bfsComplexity = 
    "时间复杂度: O(V + E)\n" ++
    "空间复杂度: O(V)\n" ++
    "遍历方式: 广度优先\n" ++
    "应用: 最短路径、连通性检测、层次遍历"
```

#### 性能分析

**时间复杂度**：$O(V + E)$
**空间复杂度**：$O(V)$（队列大小）

### 3. Dijkstra最短路径算法

#### 形式化定义

Dijkstra算法用于找到图中从一个顶点到所有其他顶点的最短路径。

**算法描述**：

1. 初始化距离数组，起始顶点距离为0，其他为无穷大
2. 选择距离最小的未访问顶点
3. 更新通过该顶点到达其他顶点的距离
4. 重复步骤2-3直到所有顶点都被访问

#### Haskell实现

```haskell
-- Dijkstra最短路径算法
dijkstra :: (Ord v, Num w, Ord w) => WeightedGraph v w -> v -> Map v (w, Maybe v)
dijkstra graph start = 
    let initialDistances = Map.insert start (0, Nothing) $ 
                          Map.fromList [(v, (maxBound, Nothing)) | v <- Set.toList $ vertices graph]
        initialUnvisited = Set.fromList $ Map.keys initialDistances
    in dijkstra' graph initialDistances initialUnvisited

dijkstra' :: (Ord v, Num w, Ord w) => 
            WeightedGraph v w -> Map v (w, Maybe v) -> Set v -> Map v (w, Maybe v)
dijkstra' graph distances unvisited
  | Set.null unvisited = distances
  | otherwise = 
      let current = findMinDistance distances unvisited
          newUnvisited = Set.delete current unvisited
          newDistances = updateDistances graph current distances
      in dijkstra' graph newDistances newUnvisited

-- 找到距离最小的未访问顶点
findMinDistance :: (Ord v, Ord w) => Map v (w, Maybe v) -> Set v -> v
findMinDistance distances unvisited = 
    let candidates = [(v, dist) | v <- Set.toList unvisited, 
                    let (dist, _) = fromMaybe (maxBound, Nothing) $ Map.lookup v distances]
    in fst $ minimumBy (\(_, d1) (_, d2) -> compare d1 d2) candidates

-- 更新距离
updateDistances :: (Ord v, Num w, Ord w) => 
                  WeightedGraph v w -> v -> Map v (w, Maybe v) -> Map v (w, Maybe v)
updateDistances graph current distances = 
    let currentDist = fst $ fromMaybe (maxBound, Nothing) $ Map.lookup current distances
        neighbors = getWeightedNeighbors graph current
    in foldl (\acc (neighbor, weight) -> 
                let newDist = currentDist + weight
                    oldDist = fst $ fromMaybe (maxBound, Nothing) $ Map.lookup neighbor acc
                in if newDist < oldDist 
                   then Map.insert neighbor (newDist, Just current) acc
                   else acc) distances neighbors

-- 获取加权邻居
getWeightedNeighbors :: (Ord v, Num w) => WeightedGraph v w -> v -> [(v, w)]
getWeightedNeighbors graph v = 
    let allEdges = Set.toList $ edges graph
        edgeMap = edgeInfo graph
        connectedEdges = filter (\e -> 
            case Map.lookup e edgeMap of
                Just (u, w, weight) -> u == v
                Nothing -> False) allEdges
    in [(w, weight) | e <- connectedEdges, 
        let (u, w, weight) = fromMaybe (v, v, 0) $ Map.lookup e edgeMap]

-- 带统计的Dijkstra
dijkstraWithStats :: (Ord v, Num w, Ord w) => 
                    WeightedGraph v w -> v -> AlgorithmResult (Map v (w, Maybe v))
dijkstraWithStats graph start = AlgorithmResult
    { result = result
    , steps = steps
    , time = 0.0
    , memory = memory
    }
  where
    (result, steps, memory) = dijkstraStats graph start

dijkstraStats :: (Ord v, Num w, Ord w) => 
                WeightedGraph v w -> v -> (Map v (w, Maybe v), Int, Int)
dijkstraStats graph start = 
    let initialDistances = Map.insert start (0, Nothing) $ 
                          Map.fromList [(v, (maxBound, Nothing)) | v <- Set.toList $ vertices graph]
        initialUnvisited = Set.fromList $ Map.keys initialDistances
    in dijkstraStats' graph initialDistances initialUnvisited 0 0

dijkstraStats' :: (Ord v, Num w, Ord w) => 
                 WeightedGraph v w -> Map v (w, Maybe v) -> Set v -> Int -> Int -> 
                 (Map v (w, Maybe v), Int, Int)
dijkstraStats' graph distances unvisited steps memory
  | Set.null unvisited = (distances, steps, memory)
  | otherwise = 
      let current = findMinDistance distances unvisited
          newUnvisited = Set.delete current unvisited
          newDistances = updateDistances graph current distances
          newSteps = steps + 1
          newMemory = memory + Map.size distances
      in dijkstraStats' graph newDistances newUnvisited newSteps newMemory

-- 复杂度分析
dijkstraComplexity :: String
dijkstraComplexity = 
    "时间复杂度: O(V² + E) 或 O((V + E) log V) 使用优先队列\n" ++
    "空间复杂度: O(V)\n" ++
    "应用: 最短路径、路由算法、网络优化\n" ++
    "限制: 不能处理负权边"
```

#### 性能分析

**时间复杂度**：

- 朴素实现：$O(V^2 + E)$
- 使用优先队列：$O((V + E) \log V)$

**空间复杂度**：$O(V)$

### 4. 最小生成树算法 (Kruskal)

#### 形式化定义

最小生成树是连接图中所有顶点的最小权重树。

**算法描述**：

1. 将所有边按权重排序
2. 初始化并查集
3. 依次选择最小权重的边
4. 如果边不会形成环，则加入生成树

#### Haskell实现

```haskell
-- 并查集数据结构
data UnionFind v = UnionFind
    { parent :: Map v v
    , rank :: Map v Int
    }

-- 创建并查集
makeUnionFind :: Ord v => [v] -> UnionFind v
makeUnionFind vertices = UnionFind
    { parent = Map.fromList [(v, v) | v <- vertices]
    , rank = Map.fromList [(v, 0) | v <- vertices]
    }

-- 查找根节点
find :: Ord v => UnionFind v -> v -> v
find uf v = 
    let p = fromMaybe v $ Map.lookup v (parent uf)
    in if p == v then v else find uf p

-- 合并两个集合
union :: Ord v => UnionFind v -> v -> v -> UnionFind v
union uf v1 v2 = 
    let root1 = find uf v1
        root2 = find uf v2
        rank1 = fromMaybe 0 $ Map.lookup root1 (rank uf)
        rank2 = fromMaybe 0 $ Map.lookup root2 (rank uf)
    in if root1 == root2 
       then uf
       else if rank1 < rank2
            then UnionFind (Map.insert root1 root2 (parent uf)) (rank uf)
            else if rank1 > rank2
                 then UnionFind (Map.insert root2 root1 (parent uf)) (rank uf)
                 else UnionFind (Map.insert root2 root1 (parent uf)) 
                               (Map.insert root1 (rank1 + 1) (rank uf))

-- Kruskal算法
kruskal :: (Ord v, Ord w, Num w) => WeightedGraph v w -> [(v, v, w)]
kruskal graph = 
    let allEdges = sortBy (\(_, _, w1) (_, _, w2) -> compare w1 w2) $ 
                   Set.toList $ edges graph
        vertices = Set.toList $ vertices graph
        uf = makeUnionFind vertices
    in kruskal' allEdges uf []

kruskal' :: (Ord v, Ord w, Num w) => 
           [(v, v, w)] -> UnionFind v -> [(v, v, w)] -> [(v, v, w)]
kruskal' [] uf mst = mst
kruskal' ((v1, v2, w):edges) uf mst = 
    let root1 = find uf v1
        root2 = find uf v2
    in if root1 == root2
       then kruskal' edges uf mst
       else let newUf = union uf v1 v2
            in kruskal' edges newUf ((v1, v2, w):mst)

-- 带统计的Kruskal
kruskalWithStats :: (Ord v, Ord w, Num w) => 
                   WeightedGraph v w -> AlgorithmResult [(v, v, w)]
kruskalWithStats graph = AlgorithmResult
    { result = result
    , steps = steps
    , time = 0.0
    , memory = memory
    }
  where
    (result, steps, memory) = kruskalStats graph

kruskalStats :: (Ord v, Ord w, Num w) => 
               WeightedGraph v w -> ([(v, v, w)], Int, Int)
kruskalStats graph = 
    let allEdges = sortBy (\(_, _, w1) (_, _, w2) -> compare w1 w2) $ 
                   Set.toList $ edges graph
        vertices = Set.toList $ vertices graph
        uf = makeUnionFind vertices
    in kruskalStats' allEdges uf [] 0 0

kruskalStats' :: (Ord v, Ord w, Num w) => 
                [(v, v, w)] -> UnionFind v -> [(v, v, w)] -> Int -> Int -> 
                ([(v, v, w)], Int, Int)
kruskalStats' [] uf mst steps memory = (mst, steps, memory)
kruskalStats' ((v1, v2, w):edges) uf mst steps memory = 
    let root1 = find uf v1
        root2 = find uf v2
        newSteps = steps + 1
        newMemory = memory + length mst
    in if root1 == root2
       then kruskalStats' edges uf mst newSteps newMemory
       else let newUf = union uf v1 v2
            in kruskalStats' edges newUf ((v1, v2, w):mst) newSteps newMemory

-- 复杂度分析
kruskalComplexity :: String
kruskalComplexity = 
    "时间复杂度: O(E log E) 或 O(E log V)\n" ++
    "空间复杂度: O(V)\n" ++
    "应用: 网络设计、聚类分析、图像分割\n" ++
    "特点: 贪心算法，全局最优解"
```

#### 性能分析

**时间复杂度**：$O(E \log E)$ 或 $O(E \log V)$
**空间复杂度**：$O(V)$

### 5. 拓扑排序

#### 形式化定义

拓扑排序是对有向无环图(DAG)的顶点进行线性排序，使得对于每条边 $(u, v)$，$u$ 在排序中位于 $v$ 之前。

**算法描述**：

1. 计算每个顶点的入度
2. 将入度为0的顶点加入队列
3. 从队列取出顶点并加入结果
4. 减少其邻居的入度，如果入度变为0则加入队列
5. 重复步骤3-4直到队列为空

#### Haskell实现

```haskell
-- 拓扑排序
topologicalSort :: Ord v => DirectedGraph v -> Maybe [v]
topologicalSort graph = 
    let inDegrees = calculateInDegrees graph
        initialQueue = [v | (v, degree) <- Map.toList inDegrees, degree == 0]
    in if length initialQueue == Map.size inDegrees
       then Just $ topologicalSort' graph inDegrees initialQueue []
       else Nothing  -- 存在环

topologicalSort' :: Ord v => DirectedGraph v -> Map v Int -> [v] -> [v] -> [v]
topologicalSort' graph inDegrees [] result = result
topologicalSort' graph inDegrees (current:queue) result = 
    let neighbors = getOutNeighbors graph current
        newInDegrees = foldl (\acc neighbor -> 
                                Map.insertWith (+) neighbor (-1) acc) 
                             inDegrees neighbors
        newQueue = queue ++ [v | (v, degree) <- Map.toList newInDegrees, 
                                degree == 0, v `notElem` (current:queue)]
    in topologicalSort' graph newInDegrees newQueue (result ++ [current])

-- 计算入度
calculateInDegrees :: Ord v => DirectedGraph v -> Map v Int
calculateInDegrees graph = 
    let allEdges = Set.toList $ edges graph
        edgeMap = edgeInfo graph
        inEdges = [v | e <- allEdges, 
                     let (u, v) = fromMaybe (undefined, undefined) $ Map.lookup e edgeMap]
    in Map.fromListWith (+) [(v, 1) | v <- inEdges]

-- 获取出边邻居
getOutNeighbors :: Ord v => DirectedGraph v -> v -> [v]
getOutNeighbors graph v = 
    let allEdges = Set.toList $ edges graph
        edgeMap = edgeInfo graph
        outEdges = filter (\e -> 
            case Map.lookup e edgeMap of
                Just (u, w) -> u == v
                Nothing -> False) allEdges
    in [w | e <- outEdges, 
           let (u, w) = fromMaybe (v, v) $ Map.lookup e edgeMap]

-- 复杂度分析
topologicalSortComplexity :: String
topologicalSortComplexity = 
    "时间复杂度: O(V + E)\n" ++
    "空间复杂度: O(V)\n" ++
    "应用: 任务调度、依赖解析、编译优化\n" ++
    "限制: 只能用于有向无环图"
```

#### 性能分析

**时间复杂度**：$O(V + E)$
**空间复杂度**：$O(V)$

## 📊 算法比较

### 性能对比表

| 算法 | 时间复杂度 | 空间复杂度 | 应用场景 | 特点 |
|------|------------|------------|----------|------|
| DFS | O(V + E) | O(V) | 连通性检测、拓扑排序 | 递归实现，深度优先 |
| BFS | O(V + E) | O(V) | 最短路径、层次遍历 | 队列实现，广度优先 |
| Dijkstra | O(V² + E) | O(V) | 单源最短路径 | 贪心算法，无负权 |
| Kruskal | O(E log E) | O(V) | 最小生成树 | 并查集，贪心算法 |
| 拓扑排序 | O(V + E) | O(V) | 任务调度、依赖解析 | 入度计算，队列 |

### 选择指南

```haskell
-- 算法选择函数
chooseGraphAlgorithm :: String -> String
chooseGraphAlgorithm "connectivity" = "DFS或BFS"
chooseGraphAlgorithm "shortest_path" = "Dijkstra"
chooseGraphAlgorithm "minimum_spanning_tree" = "Kruskal"
chooseGraphAlgorithm "topological_sort" = "拓扑排序"
chooseGraphAlgorithm "cycle_detection" = "DFS"
chooseGraphAlgorithm _ = "根据具体需求选择"

-- 智能算法选择
smartGraphAlgorithm :: String -> String -> String
smartGraphAlgorithm "traversal" "depth" = "DFS"
smartGraphAlgorithm "traversal" "breadth" = "BFS"
smartGraphAlgorithm "path" "unweighted" = "BFS"
smartGraphAlgorithm "path" "weighted" = "Dijkstra"
smartGraphAlgorithm "tree" "minimum" = "Kruskal"
smartGraphAlgorithm "sort" "dependency" = "拓扑排序"
smartGraphAlgorithm _ _ = "需要更多信息"
```

## 🔬 形式化验证

### 正确性证明

#### Dijkstra算法正确性

**定理**：Dijkstra算法能够找到从起始顶点到所有其他顶点的最短路径。

**证明**：

1. **基础情况**：起始顶点到自身的距离为0
2. **归纳假设**：假设已找到到前k个顶点的最短路径
3. **归纳步骤**：选择距离最小的未访问顶点，其距离必为最短路径

#### Kruskal算法正确性

**定理**：Kruskal算法能够找到图的最小生成树。

**证明**：

1. **贪心选择性质**：每次选择最小权重的边
2. **最优子结构**：剩余图的最小生成树与已选边构成整体最优解
3. **安全性**：不会形成环的边可以安全加入

### 复杂度证明

#### DFS复杂度

**定理**：DFS的时间复杂度为 $O(V + E)$。

**证明**：

- 每个顶点最多访问一次：$O(V)$
- 每条边最多遍历两次：$O(E)$
- 总时间复杂度：$O(V + E)$

## 🎯 实际应用

### 性能测试

```haskell
-- 性能测试函数
testGraphAlgorithmPerformance :: WeightedGraph Int Int -> IO ()
testGraphAlgorithmPerformance graph = do
    putStrLn "图算法性能测试"
    putStrLn "================"
    
    let testAlgorithm name algFunc = do
            start <- getCurrentTime
            let result = algFunc graph
            end <- getCurrentTime
            let duration = diffUTCTime end start
            putStrLn $ name ++ ": " ++ show duration
    
    testAlgorithm "Dijkstra" (\g -> dijkstra g 1)
    testAlgorithm "Kruskal" kruskal

-- 生成测试图
generateTestGraph :: Int -> Int -> IO (WeightedGraph Int Int)
generateTestGraph vertices edges = do
    gen <- newStdGen
    let vertexList = [1..vertices]
        edgeList = take edges $ randomRs ((1, 1, 1), (vertices, vertices, 100)) gen
    return $ Graph (Set.fromList vertexList) 
                   (Set.fromList edgeList)
                   (Map.fromList $ zip edgeList edgeList)
```

### 实际应用场景

1. **网络路由**：Dijkstra算法用于路由表计算
2. **社交网络**：BFS用于朋友推荐和影响力分析
3. **编译器优化**：拓扑排序用于依赖解析
4. **电路设计**：最小生成树用于电路布局
5. **游戏开发**：图算法用于AI路径规划和地图生成

## 📚 扩展阅读

### 高级图算法

1. **Floyd-Warshall**：全源最短路径
2. **Bellman-Ford**：处理负权边的最短路径
3. **Prim算法**：最小生成树的另一种实现
4. **强连通分量**：Tarjan算法
5. **最大流**：Ford-Fulkerson算法

### 并行图算法

```haskell
-- 并行BFS
parallelBfs :: Ord v => Graph v e -> v -> [v]
parallelBfs graph start = 
    let initialLevel = [start]
        visited = Set.singleton start
    in parallelBfs' graph [initialLevel] visited

parallelBfs' :: Ord v => Graph v e -> [[v]] -> Set v -> [v]
parallelBfs' graph [] visited = []
parallelBfs' graph (level:levels) visited = 
    let newNeighbors = concatMap (getNeighbors graph) level
        unvisitedNeighbors = filter (`Set.notMember` visited) newNeighbors
        newVisited = foldl Set.insert visited unvisitedNeighbors
        nextLevel = unvisitedNeighbors
    in level ++ parallelBfs' graph (levels ++ [nextLevel]) newVisited
```

## 🔗 相关链接

- [基础数据结构](../01-Haskell-Basics/01-Language-Features.md)
- [高级数据结构](../03-Data-Structures/01-Advanced-Data-Structures.md)
- [形式化证明](../04-Formal-Proofs/01-Theorem-Proving.md)
- [性能优化](../05-Performance-Optimization/01-Memory-Optimization.md)

---

*本文档提供了图算法的完整形式化理论和Haskell实现，包括性能分析和实际应用指导。*
