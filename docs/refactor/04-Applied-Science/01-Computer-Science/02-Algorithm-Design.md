# 算法设计

## 概述

算法设计是计算机科学的核心领域，研究如何设计高效、正确的算法来解决各种计算问题。本文档从形式化角度探讨算法设计的核心概念和技术。

## 1. 算法分析

### 1.1 时间复杂度

时间复杂度分析是算法设计的基础。

```haskell
-- 时间复杂度
data TimeComplexity = TimeComplexity
  { complexityFunction :: Int -> Int
  , complexityClass :: ComplexityClass
  , asymptoticNotation :: AsymptoticNotation
  }

-- 复杂性类
data ComplexityClass = 
  Constant | Logarithmic | Linear | Linearithmic | Quadratic | Cubic | Exponential | Factorial

-- 渐近记号
data AsymptoticNotation = 
  BigO | BigOmega | BigTheta | LittleO | LittleOmega

-- 大O记号分析
bigOAnalysis :: (Int -> Int) -> (Int -> Int) -> Bool
bigOAnalysis f g = 
  let c = 1000  -- 常数因子
      n0 = 100  -- 起始点
  in all (\n -> n >= n0 -> f n <= c * g n) [n0..n0+1000]

-- 算法复杂度分析
analyzeAlgorithmComplexity :: String -> (Int -> Int) -> TimeComplexity
analyzeAlgorithmComplexity name function = 
  let complexityClass = determineComplexityClass function
      asymptoticNotation = BigO
  in TimeComplexity {
    complexityFunction = function,
    complexityClass = complexityClass,
    asymptoticNotation = asymptoticNotation
  }

-- 确定复杂性类
determineComplexityClass :: (Int -> Int) -> ComplexityClass
determineComplexityClass f = 
  if bigOAnalysis f (\n -> 1) then Constant
  else if bigOAnalysis f (\n -> floor (log (fromIntegral n))) then Logarithmic
  else if bigOAnalysis f (\n -> n) then Linear
  else if bigOAnalysis f (\n -> n * floor (log (fromIntegral n))) then Linearithmic
  else if bigOAnalysis f (\n -> n^2) then Quadratic
  else if bigOAnalysis f (\n -> n^3) then Cubic
  else if bigOAnalysis f (\n -> 2^n) then Exponential
  else Factorial

-- 递归关系分析
data RecurrenceRelation = RecurrenceRelation
  { baseCase :: Int -> Int
  , recursiveCase :: Int -> Int -> Int
  , solution :: Int -> Int
  }

-- 主定理
masterTheorem :: Int -> Int -> Int -> Int -> String
masterTheorem a b f n = 
  let c = logBase (fromIntegral b) (fromIntegral a)
      fComplexity = analyzeFunctionComplexity f n
  in case compare fComplexity c of
       LT -> "Case 1: T(n) = Θ(n^" ++ show c ++ ")"
       EQ -> "Case 2: T(n) = Θ(n^" ++ show c ++ " * log n)"
       GT -> "Case 3: T(n) = Θ(f(n))"

-- 分析函数复杂性
analyzeFunctionComplexity :: (Int -> Int) -> Int -> Double
analyzeFunctionComplexity f n = 
  logBase (fromIntegral n) (fromIntegral (f n))
```

### 1.2 空间复杂度

空间复杂度分析算法所需的存储空间。

```haskell
-- 空间复杂度
data SpaceComplexity = SpaceComplexity
  { spaceFunction :: Int -> Int
  , spaceClass :: ComplexityClass
  , memoryUsage :: MemoryUsage
  }

-- 内存使用
data MemoryUsage = MemoryUsage
  { stackSpace :: Int
  , heapSpace :: Int
  , auxiliarySpace :: Int
  }

-- 空间复杂度分析
analyzeSpaceComplexity :: String -> (Int -> Int) -> SpaceComplexity
analyzeSpaceComplexity name function = 
  let spaceClass = determineSpaceComplexityClass function
      memoryUsage = MemoryUsage {
        stackSpace = function 10,
        heapSpace = function 10,
        auxiliarySpace = function 10
      }
  in SpaceComplexity {
    spaceFunction = function,
    spaceClass = spaceClass,
    memoryUsage = memoryUsage
  }

-- 确定空间复杂性类
determineSpaceComplexityClass :: (Int -> Int) -> ComplexityClass
determineSpaceComplexityClass f = 
  if bigOAnalysis f (\n -> 1) then Constant
  else if bigOAnalysis f (\n -> floor (log (fromIntegral n))) then Logarithmic
  else if bigOAnalysis f (\n -> n) then Linear
  else if bigOAnalysis f (\n -> n^2) then Quadratic
  else Cubic
```

## 2. 分治算法

### 2.1 基本概念

分治算法将问题分解为更小的子问题。

```haskell
-- 分治算法
data DivideAndConquer = DivideAndConquer
  { divideFunction :: [Int] -> [[Int]]
  , conquerFunction :: [Int] -> Int
  , combineFunction :: [Int] -> Int
  }

-- 分治策略
data DivideStrategy = 
  BinaryDivide | TernaryDivide | RecursiveDivide | IterativeDivide

-- 合并排序
mergeSort :: [Int] -> [Int]
mergeSort [] = []
mergeSort [x] = [x]
mergeSort xs = 
  let (left, right) = splitAt (length xs `div` 2) xs
      sortedLeft = mergeSort left
      sortedRight = mergeSort right
  in merge sortedLeft sortedRight

-- 合并两个有序列表
merge :: [Int] -> [Int] -> [Int]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys) = 
  if x <= y
  then x : merge xs (y:ys)
  else y : merge (x:xs) ys

-- 快速排序
quickSort :: [Int] -> [Int]
quickSort [] = []
quickSort (x:xs) = 
  let smaller = filter (<= x) xs
      larger = filter (> x) xs
  in quickSort smaller ++ [x] ++ quickSort larger

-- 分治算法分析
analyzeDivideAndConquer :: DivideAndConquer -> Int -> TimeComplexity
analyzeDivideAndConquer algorithm n = 
  let divideTime = analyzeDivideTime (divideFunction algorithm) n
      conquerTime = analyzeConquerTime (conquerFunction algorithm) n
      combineTime = analyzeCombineTime (combineFunction algorithm) n
      totalTime = divideTime + conquerTime + combineTime
  in TimeComplexity {
    complexityFunction = \n -> totalTime,
    complexityClass = determineComplexityClass (\n -> totalTime),
    asymptoticNotation = BigO
  }

-- 分析分治时间
analyzeDivideTime :: ([Int] -> [[Int]]) -> Int -> Int
analyzeDivideTime divideFunction n = 
  let testInput = [1..n]
      startTime = 0  -- 简化实现
      divided = divideFunction testInput
      endTime = 1
  in endTime - startTime

-- 分析征服时间
analyzeConquerTime :: ([Int] -> Int) -> Int -> Int
analyzeConquerTime conquerFunction n = 
  let testInput = [1..n]
      startTime = 0
      result = conquerFunction testInput
      endTime = 1
  in endTime - startTime

-- 分析合并时间
analyzeCombineTime :: ([Int] -> Int) -> Int -> Int
analyzeCombineTime combineFunction n = 
  let testInput = [1..n]
      startTime = 0
      result = combineFunction testInput
      endTime = 1
  in endTime - startTime
```

### 2.2 高级分治

高级分治算法解决复杂问题。

```haskell
-- 最近点对问题
data ClosestPair = ClosestPair
  { points :: [(Double, Double)]
  , closestDistance :: Double
  , closestPair :: ((Double, Double), (Double, Double))
  }

-- 最近点对算法
closestPairAlgorithm :: [(Double, Double)] -> ClosestPair
closestPairAlgorithm points = 
  let sortedByX = sortBy (comparing fst) points
      sortedByY = sortBy (comparing snd) points
      result = closestPairRecursive sortedByX sortedByY
  in ClosestPair {
    points = points,
    closestDistance = fst result,
    closestPair = snd result
  }

-- 最近点对递归
closestPairRecursive :: [(Double, Double)] -> [(Double, Double)] -> (Double, ((Double, Double), (Double, Double)))
closestPairRecursive pointsX pointsY = 
  let n = length pointsX
  in if n <= 3
     then bruteForceClosestPair pointsX
     else 
       let mid = n `div` 2
           (leftX, rightX) = splitAt mid pointsX
           leftY = filter (\p -> fst p <= fst (pointsX !! mid)) pointsY
           rightY = filter (\p -> fst p > fst (pointsX !! mid)) pointsY
           (leftDist, leftPair) = closestPairRecursive leftX leftY
           (rightDist, rightPair) = closestPairRecursive rightX rightY
           minDist = min leftDist rightDist
           stripPoints = filter (\p -> abs (fst p - fst (pointsX !! mid)) < minDist) pointsY
           (stripDist, stripPair) = closestPairInStrip stripPoints minDist
       in if stripDist < minDist
          then (stripDist, stripPair)
          else if leftDist < rightDist
               then (leftDist, leftPair)
               else (rightDist, rightPair)

-- 暴力最近点对
bruteForceClosestPair :: [(Double, Double)] -> (Double, ((Double, Double), (Double, Double)))
bruteForceClosestPair points = 
  let pairs = [(p1, p2) | p1 <- points, p2 <- points, p1 /= p2]
      distances = [(distance p1 p2, (p1, p2)) | (p1, p2) <- pairs]
  in minimum distances

-- 计算距离
distance :: (Double, Double) -> (Double, Double) -> Double
distance (x1, y1) (x2, y2) = sqrt ((x1 - x2)^2 + (y1 - y2)^2)

-- 条带中的最近点对
closestPairInStrip :: [(Double, Double)] -> Double -> (Double, ((Double, Double), (Double, Double)))
closestPairInStrip strip minDist = 
  let n = length strip
      minDistance = minDist
      minPair = ((0, 0), (0, 0))
  in foldl (\acc i -> 
             foldl (\acc' j -> 
                     if j - i <= 7
                     then 
                       let dist = distance (strip !! i) (strip !! j)
                       in if dist < fst acc'
                          then (dist, ((strip !! i), (strip !! j)))
                          else acc'
                     else acc') 
                   acc [i+1..min (i+7) (n-1)]) 
           (minDistance, minPair) [0..n-2]
```

## 3. 动态规划

### 3.1 基本概念

动态规划通过存储子问题的解来避免重复计算。

```haskell
-- 动态规划
data DynamicProgramming = DynamicProgramming
  { subproblems :: [(String, Int)]
  , recurrenceRelation :: String -> Int
  , memoization :: [(String, Int)]
  }

-- 动态规划策略
data DPStrategy = 
  TopDown | BottomUp | Memoization | Tabulation

-- 斐波那契数列
fibonacciDP :: Int -> Int
fibonacciDP n = 
  let memo = replicate (n + 1) (-1)
      fibHelper i = 
        if i <= 1
        then i
        else if memo !! i /= -1
             then memo !! i
             else 
               let result = fibHelper (i - 1) + fibHelper (i - 2)
               in memo !! i = result
  in fibHelper n

-- 最长公共子序列
longestCommonSubsequence :: String -> String -> Int
longestCommonSubsequence s1 s2 = 
  let m = length s1
      n = length s2
      dp = replicate (m + 1) (replicate (n + 1) 0)
      lcsHelper i j = 
        if i == 0 || j == 0
        then 0
        else if s1 !! (i - 1) == s2 !! (j - 1)
             then 1 + lcsHelper (i - 1) (j - 1)
             else max (lcsHelper (i - 1) j) (lcsHelper i (j - 1))
  in lcsHelper m n

-- 背包问题
data KnapsackProblem = KnapsackProblem
  { weights :: [Int]
  , values :: [Int]
  , capacity :: Int
  , maxValue :: Int
  }

-- 0-1背包问题
knapsack01 :: [Int] -> [Int] -> Int -> Int
knapsack01 weights values capacity = 
  let n = length weights
      dp = replicate (n + 1) (replicate (capacity + 1) 0)
      knapsackHelper i w = 
        if i == 0 || w == 0
        then 0
        else if weights !! (i - 1) <= w
             then max (values !! (i - 1) + knapsackHelper (i - 1) (w - weights !! (i - 1)))
                      (knapsackHelper (i - 1) w)
             else knapsackHelper (i - 1) w
  in knapsackHelper n capacity

-- 动态规划分析
analyzeDynamicProgramming :: DynamicProgramming -> Int -> TimeComplexity
analyzeDynamicProgramming dp n = 
  let subproblemCount = length (subproblems dp)
      timePerSubproblem = 1  -- 简化假设
      totalTime = subproblemCount * timePerSubproblem
  in TimeComplexity {
    complexityFunction = \n -> totalTime,
    complexityClass = determineComplexityClass (\n -> totalTime),
    asymptoticNotation = BigO
  }
```

### 3.2 高级动态规划

高级动态规划解决复杂优化问题。

```haskell
-- 编辑距离
editDistance :: String -> String -> Int
editDistance s1 s2 = 
  let m = length s1
      n = length s2
      dp = replicate (m + 1) (replicate (n + 1) 0)
      editDistanceHelper i j = 
        if i == 0
        then j
        else if j == 0
             then i
             else if s1 !! (i - 1) == s2 !! (j - 1)
                  then editDistanceHelper (i - 1) (j - 1)
                  else 1 + minimum [editDistanceHelper (i - 1) j,      -- 删除
                                   editDistanceHelper i (j - 1),       -- 插入
                                   editDistanceHelper (i - 1) (j - 1)] -- 替换
  in editDistanceHelper m n

-- 矩阵链乘法
matrixChainMultiplication :: [Int] -> Int
matrixChainMultiplication dimensions = 
  let n = length dimensions - 1
      dp = replicate n (replicate n 0)
      matrixChainHelper i j = 
        if i == j
        then 0
        else 
          let costs = [matrixChainHelper i k + matrixChainHelper (k + 1) j + 
                       dimensions !! i * dimensions !! (k + 1) * dimensions !! (j + 1) | 
                       k <- [i..j-1]]
          in minimum costs
  in matrixChainHelper 0 (n - 1)

-- 最长递增子序列
longestIncreasingSubsequence :: [Int] -> Int
longestIncreasingSubsequence nums = 
  let n = length nums
      dp = replicate n 1
      lisHelper i = 
        if i == 0
        then 1
        else 
          let maxLen = maximum [if nums !! j < nums !! i 
                               then dp !! j + 1 
                               else 1 | j <- [0..i-1]]
          in maxLen
  in maximum [lisHelper i | i <- [0..n-1]]
```

## 4. 贪心算法

### 4.1 基本概念

贪心算法通过局部最优选择来构建全局解。

```haskell
-- 贪心算法
data GreedyAlgorithm = GreedyAlgorithm
  { selectionFunction :: [Int] -> Int
  , feasibilityFunction :: [Int] -> Bool
  , solutionFunction :: [Int] -> [Int]
  }

-- 贪心策略
data GreedyStrategy = 
  LargestFirst | SmallestFirst | RatioBased | CustomOrder

-- 活动选择问题
data ActivitySelection = ActivitySelection
  { activities :: [(Int, Int)]
  , selectedActivities :: [(Int, Int)]
  , maxActivities :: Int
  }

-- 活动选择算法
activitySelection :: [(Int, Int)] -> ActivitySelection
activitySelection activities = 
  let sortedActivities = sortBy (comparing snd) activities
      selected = greedyActivitySelection sortedActivities
  in ActivitySelection {
    activities = activities,
    selectedActivities = selected,
    maxActivities = length selected
  }

-- 贪心活动选择
greedyActivitySelection :: [(Int, Int)] -> [(Int, Int)]
greedyActivitySelection [] = []
greedyActivitySelection (activity:activities) = 
  let selected = [activity]
      compatible = filter (\act -> fst act >= snd activity) activities
  in selected ++ greedyActivitySelection compatible

-- 霍夫曼编码
data HuffmanNode = 
  Leaf Char Int
  | Internal HuffmanNode HuffmanNode Int

-- 构建霍夫曼树
buildHuffmanTree :: [(Char, Int)] -> HuffmanNode
buildHuffmanTree frequencies = 
  let nodes = map (\(char, freq) -> Leaf char freq) frequencies
      tree = buildHuffmanTreeHelper nodes
  in tree

-- 霍夫曼树构建辅助函数
buildHuffmanTreeHelper :: [HuffmanNode] -> HuffmanNode
buildHuffmanTreeHelper [node] = node
buildHuffmanTreeHelper nodes = 
  let sortedNodes = sortBy (comparing getFrequency) nodes
      (node1, node2) = (head sortedNodes, head (tail sortedNodes))
      remaining = drop 2 sortedNodes
      internalNode = Internal node1 node2 (getFrequency node1 + getFrequency node2)
  in buildHuffmanTreeHelper (internalNode : remaining)

-- 获取频率
getFrequency :: HuffmanNode -> Int
getFrequency (Leaf _ freq) = freq
getFrequency (Internal _ _ freq) = freq

-- 贪心算法分析
analyzeGreedyAlgorithm :: GreedyAlgorithm -> Int -> TimeComplexity
analyzeGreedyAlgorithm greedy n = 
  let selectionTime = analyzeSelectionTime (selectionFunction greedy) n
      feasibilityTime = analyzeFeasibilityTime (feasibilityFunction greedy) n
      solutionTime = analyzeSolutionTime (solutionFunction greedy) n
      totalTime = selectionTime + feasibilityTime + solutionTime
  in TimeComplexity {
    complexityFunction = \n -> totalTime,
    complexityClass = determineComplexityClass (\n -> totalTime),
    asymptoticNotation = BigO
  }

-- 分析选择时间
analyzeSelectionTime :: ([Int] -> Int) -> Int -> Int
analyzeSelectionTime selectionFunction n = 
  let testInput = [1..n]
      startTime = 0
      result = selectionFunction testInput
      endTime = 1
  in endTime - startTime

-- 分析可行性时间
analyzeFeasibilityTime :: ([Int] -> Bool) -> Int -> Int
analyzeFeasibilityTime feasibilityFunction n = 
  let testInput = [1..n]
      startTime = 0
      result = feasibilityFunction testInput
      endTime = 1
  in endTime - startTime

-- 分析解时间
analyzeSolutionTime :: ([Int] -> [Int]) -> Int -> Int
analyzeSolutionTime solutionFunction n = 
  let testInput = [1..n]
      startTime = 0
      result = solutionFunction testInput
      endTime = 1
  in endTime - startTime
```

## 5. 图算法

### 5.1 基本图算法

图算法处理图结构数据。

```haskell
-- 图
data Graph = Graph
  { vertices :: [Int]
  , edges :: [(Int, Int)]
  , adjacencyList :: [(Int, [Int])]
  }

-- 构建图
buildGraph :: [Int] -> [(Int, Int)] -> Graph
buildGraph vertices edges = 
  let adjacencyList = [(v, [u | (u, w) <- edges, v == u || v == w]) | v <- vertices]
  in Graph {
    vertices = vertices,
    edges = edges,
    adjacencyList = adjacencyList
  }

-- 深度优先搜索
depthFirstSearch :: Graph -> Int -> [Int]
depthFirstSearch graph start = 
  let visited = replicate (length (vertices graph)) False
      dfsHelper v = 
        if visited !! v
        then []
        else 
          let newVisited = updateList visited v True
              neighbors = getNeighbors graph v
              neighborResults = concatMap dfsHelper neighbors
          in v : neighborResults
  in dfsHelper start

-- 广度优先搜索
breadthFirstSearch :: Graph -> Int -> [Int]
breadthFirstSearch graph start = 
  let visited = replicate (length (vertices graph)) False
      bfsHelper queue visited = 
        if null queue
        then []
        else 
          let (v, rest) = (head queue, tail queue)
          in if visited !! v
             then bfsHelper rest visited
             else 
               let newVisited = updateList visited v True
                   neighbors = getNeighbors graph v
                   newQueue = rest ++ neighbors
               in v : bfsHelper newQueue newVisited
  in bfsHelper [start] visited

-- 获取邻居
getNeighbors :: Graph -> Int -> [Int]
getNeighbors graph vertex = 
  case lookup vertex (adjacencyList graph) of
    Just neighbors -> neighbors
    Nothing -> []

-- 最短路径算法
data ShortestPath = ShortestPath
  { distances :: [Int]
  , predecessors :: [Int]
  , path :: [Int]
  }

-- Dijkstra算法
dijkstra :: Graph -> Int -> ShortestPath
dijkstra graph start = 
  let n = length (vertices graph)
      distances = replicate n maxBound
      predecessors = replicate n (-1)
      initialDistances = updateList distances start 0
      result = dijkstraHelper graph initialDistances predecessors [start]
  in ShortestPath {
    distances = fst result,
    predecessors = snd result,
    path = extractPath (snd result) start (n - 1)
  }

-- Dijkstra辅助函数
dijkstraHelper :: Graph -> [Int] -> [Int] -> [Int] -> ([Int], [Int])
dijkstraHelper graph distances predecessors visited = 
  if length visited == length (vertices graph)
  then (distances, predecessors)
  else 
    let unvisited = filter (`notElem` visited) (vertices graph)
        nextVertex = minimumBy (comparing (distances !!)) unvisited
        neighbors = getNeighbors graph nextVertex
        (newDistances, newPredecessors) = updateDistances graph distances predecessors nextVertex neighbors
    in dijkstraHelper graph newDistances newPredecessors (nextVertex : visited)

-- 更新距离
updateDistances :: Graph -> [Int] -> [Int] -> Int -> [Int] -> ([Int], [Int])
updateDistances graph distances predecessors vertex neighbors = 
  foldl (\(dist, pred) neighbor -> 
           let newDist = distances !! vertex + 1  -- 假设所有边权重为1
           in if newDist < dist !! neighbor
              then (updateList dist neighbor newDist, updateList pred neighbor vertex)
              else (dist, pred)) 
        (distances, predecessors) neighbors

-- 提取路径
extractPath :: [Int] -> Int -> Int -> [Int]
extractPath predecessors start end = 
  if end == start
  then [start]
  else if predecessors !! end == -1
       then []
       else extractPath predecessors start (predecessors !! end) ++ [end]
```

### 5.2 高级图算法

高级图算法解决复杂图问题。

```haskell
-- 最小生成树
data MinimumSpanningTree = MinimumSpanningTree
  { treeEdges :: [(Int, Int)]
  { totalWeight :: Int
  }

-- Kruskal算法
kruskal :: Graph -> MinimumSpanningTree
kruskal graph = 
  let edges = sortBy (comparing (\(u, v) -> u + v)) (edges graph)
      n = length (vertices graph)
      parent = [0..n-1]
      rank = replicate n 0
      result = kruskalHelper edges parent rank []
  in MinimumSpanningTree {
    treeEdges = result,
    totalWeight = sum (map (\(u, v) -> u + v) result)
  }

-- Kruskal辅助函数
kruskalHelper :: [(Int, Int)] -> [Int] -> [Int] -> [(Int, Int)] -> [(Int, Int)]
kruskalHelper [] _ _ mst = mst
kruskalHelper ((u, v):edges) parent rank mst = 
  let rootU = find parent u
      rootV = find parent v
  in if rootU == rootV
     then kruskalHelper edges parent rank mst
     else 
       let newParent = union parent rank rootU rootV
           newMst = (u, v):mst
       in kruskalHelper edges newParent rank newMst

-- 查找根
find :: [Int] -> Int -> Int
find parent x = 
  if parent !! x == x
  then x
  else find parent (parent !! x)

-- 并集
union :: [Int] -> [Int] -> Int -> Int -> [Int]
union parent rank x y = 
  let rootX = find parent x
      rootY = find parent y
  in if rootX == rootY
     then parent
     else 
       let rankX = rank !! rootX
           rankY = rank !! rootY
       in if rankX < rankY
          then updateList parent rootX rootY
          else if rankX > rankY
               then updateList parent rootY rootX
               else let newParent = updateList parent rootY rootX
                        newRank = updateList rank rootX (rankX + 1)
                    in newParent

-- 强连通分量
data StronglyConnectedComponent = StronglyConnectedComponent
  { components :: [[Int]]
  , componentCount :: Int
  }

-- Kosaraju算法
kosaraju :: Graph -> StronglyConnectedComponent
kosaraju graph = 
  let vertices = vertices graph
      visited = replicate (length vertices) False
      order = []
      -- 第一次DFS
      (order, _) = foldl (\(ord, vis) v -> 
                           if not (vis !! v)
                           then let (newOrd, newVis) = dfsFirst graph v vis
                                in (newOrd ++ ord, newVis)
                           else (ord, vis)) 
                         (order, visited) vertices
      -- 第二次DFS
      transposedGraph = transposeGraph graph
      visited2 = replicate (length vertices) False
      components = kosarajuSecond transposedGraph order visited2 []
  in StronglyConnectedComponent {
    components = components,
    componentCount = length components
  }

-- 第一次DFS
dfsFirst :: Graph -> Int -> [Bool] -> ([Int], [Bool])
dfsFirst graph vertex visited = 
  if visited !! vertex
  then ([], visited)
  else 
    let newVisited = updateList visited vertex True
        neighbors = getNeighbors graph vertex
        (order, finalVisited) = foldl (\(ord, vis) neighbor -> 
                                        let (newOrd, newVis) = dfsFirst graph neighbor vis
                                        in (newOrd ++ ord, newVis)) 
                                      ([], newVisited) neighbors
    in (vertex : order, finalVisited)

-- 转置图
transposeGraph :: Graph -> Graph
transposeGraph graph = 
  let transposedEdges = map (\(u, v) -> (v, u)) (edges graph)
  in buildGraph (vertices graph) transposedEdges

-- Kosaraju第二次DFS
kosarajuSecond :: Graph -> [Int] -> [Bool] -> [[Int]] -> [[Int]]
kosarajuSecond graph order visited components = 
  case order of
    [] -> components
    (vertex:rest) -> 
      if visited !! vertex
      then kosarajuSecond graph rest visited components
      else 
        let newVisited = updateList visited vertex True
            component = dfsSecond graph vertex newVisited []
            newComponents = component : components
        in kosarajuSecond graph rest newVisited newComponents

-- 第二次DFS
dfsSecond :: Graph -> Int -> [Bool] -> [Int] -> [Int]
dfsSecond graph vertex visited component = 
  if visited !! vertex
  then component
  else 
    let newVisited = updateList visited vertex True
        neighbors = getNeighbors graph vertex
        newComponent = vertex : component
        finalComponent = foldl (\comp neighbor -> 
                                 dfsSecond graph neighbor newVisited comp) 
                               newComponent neighbors
    in finalComponent
```

## 总结

算法设计为解决各种计算问题提供了系统的方法。通过形式化方法，我们可以：

1. **精确分析**：用数学工具精确分析算法性能
2. **算法设计**：设计高效、正确的算法
3. **问题解决**：为实际问题提供算法解决方案
4. **理论发展**：为计算机科学提供理论基础

算法设计的研究将继续推动我们对计算问题的理解，并为实际应用提供高效的解决方案。 