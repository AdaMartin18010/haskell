# 搜索算法 (Search Algorithms)

## 1. 概述

搜索算法是计算机科学中的基础算法，用于在数据结构中查找特定元素。本文档介绍各种经典搜索算法在Haskell中的实现，包括线性搜索、二分搜索、深度优先搜索、广度优先搜索等。

## 2. 算法分类

### 2.1 线性搜索算法

- 线性搜索 (Linear Search)
- 跳跃搜索 (Jump Search)
- 插值搜索 (Interpolation Search)

### 2.2 分治搜索算法

- 二分搜索 (Binary Search)
- 三分搜索 (Ternary Search)
- 指数搜索 (Exponential Search)

### 2.3 图搜索算法

- 深度优先搜索 (Depth-First Search)
- 广度优先搜索 (Breadth-First Search)
- A*搜索 (A* Search)

## 3. 线性搜索算法

### 3.1 线性搜索

#### 算法描述

线性搜索逐个检查数组中的每个元素，直到找到目标元素或遍历完整个数组。

#### Haskell实现

```haskell
-- 线性搜索
linearSearch :: Eq a => a -> [a] -> Maybe Int
linearSearch _ [] = Nothing
linearSearch target (x:xs) = 
    if x == target 
    then Just 0 
    else fmap (+1) (linearSearch target xs)

-- 使用findIndex的线性搜索
linearSearch' :: Eq a => a -> [a] -> Maybe Int
linearSearch' target = findIndex (== target)

-- 返回所有匹配位置的线性搜索
linearSearchAll :: Eq a => a -> [a] -> [Int]
linearSearchAll target = findIndices (== target)

-- 优化的线性搜索（提前退出）
linearSearchOptimized :: Eq a => a -> [a] -> Bool
linearSearchOptimized target = any (== target)

-- 使用foldr的线性搜索
linearSearchFold :: Eq a => a -> [a] -> Maybe Int
linearSearchFold target = foldr f Nothing . zip [0..]
  where
    f (i, x) acc = if x == target then Just i else acc
```

#### 复杂度分析

- **时间复杂度**: O(n) 最坏和平均情况
- **空间复杂度**: O(1)
- **适用场景**: 无序数组、小规模数据

#### 形式化证明

**定理 3.1**: 线性搜索算法正确性

**证明**:

1. **基础情况**: 空列表返回Nothing
2. **归纳假设**: 假设对长度为k的列表，算法正确工作
3. **归纳步骤**: 对于长度为k+1的列表，检查第一个元素，如果匹配则返回0，否则递归搜索剩余k个元素

### 3.2 跳跃搜索

#### 算法描述

跳跃搜索通过固定步长跳跃来减少比较次数，适用于有序数组。

#### Haskell实现

```haskell
-- 跳跃搜索
jumpSearch :: Ord a => a -> [a] -> Maybe Int
jumpSearch target xs = jumpSearch' target xs 0 (length xs)
  where
    jumpSearch' target xs pos n
      | pos >= n = Nothing
      | xs !! pos == target = Just pos
      | xs !! pos > target = linearSearchBackward target xs pos
      | otherwise = jumpSearch' target xs (pos + step) n
      where step = sqrt (fromIntegral n)

-- 向后线性搜索
linearSearchBackward :: Eq a => a -> [a] -> Int -> Maybe Int
linearSearchBackward target xs pos = 
    let start = max 0 (pos - step)
        searchRange = take (pos - start + 1) (drop start xs)
        indices = [start..pos]
    in case findIndex (== target) searchRange of
         Just i -> Just (indices !! i)
         Nothing -> Nothing
  where step = floor (sqrt (fromIntegral (length xs)))

-- 优化的跳跃搜索
jumpSearchOptimized :: Ord a => a -> [a] -> Maybe Int
jumpSearchOptimized target xs = 
    let n = length xs
        step = floor (sqrt (fromIntegral n))
        (pos, _) = until (\(pos, _) -> pos >= n || xs !! pos >= target)
                        (\(pos, _) -> (pos + step, step))
                        (0, step)
    in if pos >= n 
       then Nothing
       else linearSearchBackward target xs pos
  where
    linearSearchBackward target xs pos = 
        let start = max 0 (pos - step)
            searchRange = zip [start..pos] (drop start (take (pos + 1) xs))
        in case find (\(_, x) -> x == target) searchRange of
             Just (i, _) -> Just i
             Nothing -> Nothing
```

#### 复杂度分析

- **时间复杂度**: O(√n) 最优情况，O(n) 最坏情况
- **空间复杂度**: O(1)
- **适用场景**: 有序数组，比线性搜索更快

### 3.3 插值搜索

#### 算法描述

插值搜索使用插值公式来估计目标元素的位置，适用于均匀分布的有序数组。

#### Haskell实现

```haskell
-- 插值搜索
interpolationSearch :: (Ord a, Fractional a) => a -> [a] -> Maybe Int
interpolationSearch target xs = 
    let n = length xs
        low = 0
        high = n - 1
    in interpolationSearch' target xs low high
  where
    interpolationSearch' target xs low high
      | low > high = Nothing
      | low == high = if xs !! low == target then Just low else Nothing
      | otherwise = 
          let pos = low + floor (fromIntegral (high - low) * 
                                (target - xs !! low) / 
                                (xs !! high - xs !! low))
          in if pos < low || pos > high 
             then Nothing
             else if xs !! pos == target 
                  then Just pos
                  else if xs !! pos < target 
                       then interpolationSearch' target xs (pos + 1) high
                       else interpolationSearch' target xs low (pos - 1)

-- 安全的插值搜索（处理边界情况）
interpolationSearchSafe :: (Ord a, Fractional a) => a -> [a] -> Maybe Int
interpolationSearchSafe target xs = 
    let n = length xs
    in if n == 0 
       then Nothing
       else interpolationSearchSafe' target xs 0 (n - 1)
  where
    interpolationSearchSafe' target xs low high
      | low > high = Nothing
      | low == high = if xs !! low == target then Just low else Nothing
      | xs !! low == xs !! high = 
          if xs !! low == target then Just low else Nothing
      | otherwise = 
          let lowVal = xs !! low
              highVal = xs !! high
              pos = low + floor (fromIntegral (high - low) * 
                                (target - lowVal) / (highVal - lowVal))
          in if pos < low || pos > high 
             then Nothing
             else if xs !! pos == target 
                  then Just pos
                  else if xs !! pos < target 
                       then interpolationSearchSafe' target xs (pos + 1) high
                       else interpolationSearchSafe' target xs low (pos - 1)
```

#### 复杂度分析

- **时间复杂度**: O(log log n) 平均情况，O(n) 最坏情况
- **空间复杂度**: O(1)
- **适用场景**: 均匀分布的有序数组

## 4. 分治搜索算法

### 4.1 二分搜索

#### 算法描述

二分搜索在有序数组中通过比较中间元素来缩小搜索范围。

#### Haskell实现

```haskell
-- 二分搜索
binarySearch :: Ord a => a -> [a] -> Maybe Int
binarySearch target xs = binarySearch' target xs 0 (length xs - 1)
  where
    binarySearch' target xs low high
      | low > high = Nothing
      | otherwise = 
          let mid = (low + high) `div` 2
              midVal = xs !! mid
          in if midVal == target 
             then Just mid
             else if midVal < target 
                  then binarySearch' target xs (mid + 1) high
                  else binarySearch' target xs low (mid - 1)

-- 递归二分搜索
binarySearchRecursive :: Ord a => a -> [a] -> Maybe Int
binarySearchRecursive target [] = Nothing
binarySearchRecursive target xs = 
    let mid = length xs `div` 2
        midVal = xs !! mid
    in if midVal == target 
       then Just mid
       else if midVal < target 
            then fmap (+ (mid + 1)) (binarySearchRecursive target (drop (mid + 1) xs))
            else binarySearchRecursive target (take mid xs)

-- 查找第一个匹配元素
binarySearchFirst :: Ord a => a -> [a] -> Maybe Int
binarySearchFirst target xs = binarySearchFirst' target xs 0 (length xs)
  where
    binarySearchFirst' target xs low high
      | low >= high = Nothing
      | otherwise = 
          let mid = (low + high) `div` 2
              midVal = xs !! mid
          in if midVal >= target 
             then binarySearchFirst' target xs low mid
             else binarySearchFirst' target xs (mid + 1) high

-- 查找最后一个匹配元素
binarySearchLast :: Ord a => a -> [a] -> Maybe Int
binarySearchLast target xs = binarySearchLast' target xs 0 (length xs)
  where
    binarySearchLast' target xs low high
      | low >= high = Nothing
      | otherwise = 
          let mid = (low + high + 1) `div` 2
              midVal = xs !! mid
          in if midVal <= target 
             then binarySearchLast' target xs mid high
             else binarySearchLast' target xs low (mid - 1)
```

#### 复杂度分析

- **时间复杂度**: O(log n) 所有情况
- **空间复杂度**: O(1) 迭代版本，O(log n) 递归版本
- **适用场景**: 有序数组

#### 形式化证明

**定理 4.1**: 二分搜索算法正确性

**证明**:

1. **基础情况**: 空数组返回Nothing
2. **归纳假设**: 假设对长度为k的数组，算法正确工作
3. **归纳步骤**:
   - 比较中间元素
   - 如果匹配，返回位置
   - 如果目标小于中间元素，在左半部分搜索
   - 如果目标大于中间元素，在右半部分搜索
   - 每次递归调用都在更小的子数组上工作

### 4.2 三分搜索

#### 算法描述

三分搜索用于在单峰函数中查找最大值或最小值。

#### Haskell实现

```haskell
-- 三分搜索（查找最大值）
ternarySearchMax :: (Ord a, Fractional a) => (a -> a) -> a -> a -> a -> a
ternarySearchMax f left right epsilon = 
    let mid1 = left + (right - left) / 3
        mid2 = right - (right - left) / 3
    in if abs (right - left) < epsilon 
       then (left + right) / 2
       else if f mid1 < f mid2 
            then ternarySearchMax f mid1 right epsilon
            else ternarySearchMax f left mid2 epsilon

-- 三分搜索（查找最小值）
ternarySearchMin :: (Ord a, Fractional a) => (a -> a) -> a -> a -> a -> a
ternarySearchMin f left right epsilon = 
    let mid1 = left + (right - left) / 3
        mid2 = right - (right - left) / 3
    in if abs (right - left) < epsilon 
       then (left + right) / 2
       else if f mid1 > f mid2 
            then ternarySearchMin f mid1 right epsilon
            else ternarySearchMin f left mid2 epsilon

-- 整数三分搜索
ternarySearchInt :: (Int -> Int) -> Int -> Int -> Int
ternarySearchInt f left right = 
    let mid1 = left + (right - left) `div` 3
        mid2 = right - (right - left) `div` 3
    in if right - left <= 2 
       then maximum [f i | i <- [left..right]]
       else if f mid1 < f mid2 
            then ternarySearchInt f mid1 right
            else ternarySearchInt f left mid2
```

#### 复杂度分析

- **时间复杂度**: O(log n)
- **空间复杂度**: O(1)
- **适用场景**: 单峰函数优化

### 4.3 指数搜索

#### 算法描述

指数搜索通过指数增长步长来找到目标元素的范围，然后使用二分搜索。

#### Haskell实现

```haskell
-- 指数搜索
exponentialSearch :: Ord a => a -> [a] -> Maybe Int
exponentialSearch target xs = 
    let n = length xs
        (start, end) = findRange target xs 1
    in binarySearchRange target xs start (min end n)
  where
    findRange target xs i
      | i >= length xs = (i `div` 2, i)
      | xs !! i >= target = (i `div` 2, i)
      | otherwise = findRange target xs (i * 2)
    
    binarySearchRange target xs low high = 
        binarySearch' target xs low high
      where
        binarySearch' target xs low high
          | low > high = Nothing
          | otherwise = 
              let mid = (low + high) `div` 2
                  midVal = xs !! mid
              in if midVal == target 
                 then Just mid
                 else if midVal < target 
                      then binarySearch' target xs (mid + 1) high
                      else binarySearch' target xs low (mid - 1)

-- 优化的指数搜索
exponentialSearchOptimized :: Ord a => a -> [a] -> Maybe Int
exponentialSearchOptimized target xs = 
    let n = length xs
        (start, end) = findRange target xs 1 n
    in binarySearchRange target xs start end
  where
    findRange target xs i n
      | i >= n = (i `div` 2, n - 1)
      | xs !! i >= target = (i `div` 2, i)
      | otherwise = findRange target xs (i * 2) n
    
    binarySearchRange target xs low high = 
        let search = binarySearch target (take (high + 1) (drop low xs))
        in fmap (+ low) search
```

#### 复杂度分析

- **时间复杂度**: O(log n)
- **空间复杂度**: O(1)
- **适用场景**: 有序数组，目标元素靠近数组开头

## 5. 图搜索算法

### 5.1 深度优先搜索

#### 算法描述

深度优先搜索沿着图的边尽可能深入，直到无法继续，然后回溯。

#### Haskell实现

```haskell
-- 图的邻接表表示
type Graph a = [(a, [a])]

-- 深度优先搜索
dfs :: Eq a => a -> Graph a -> [a]
dfs start graph = dfs' [start] [] graph
  where
    dfs' [] visited _ = reverse visited
    dfs' (current:stack) visited graph = 
        if current `elem` visited 
        then dfs' stack visited graph
        else let neighbors = getNeighbors current graph
                 newStack = neighbors ++ stack
                 newVisited = current : visited
             in dfs' newStack newVisited graph
    
    getNeighbors node graph = 
        case lookup node graph of
          Just neighbors -> neighbors
          Nothing -> []

-- 使用State的DFS
dfsState :: Eq a => a -> Graph a -> [a]
dfsState start graph = 
    let initialState = ([start], [], graph)
        (_, visited, _) = execState (dfsM start) initialState
    in reverse visited
  where
    dfsM :: Eq a => a -> State ([a], [a], Graph a) ()
    dfsM current = do
        (stack, visited, graph) <- get
        if current `elem` visited 
        then return ()
        else do
            let neighbors = getNeighbors current graph
                newStack = neighbors ++ stack
                newVisited = current : visited
            put (newStack, newVisited, graph)
            mapM_ dfsM neighbors
    
    getNeighbors node graph = 
        case lookup node graph of
          Just neighbors -> neighbors
          Nothing -> []

-- 递归DFS
dfsRecursive :: Eq a => a -> Graph a -> [a]
dfsRecursive start graph = dfsRec' start [] graph
  where
    dfsRec' current visited graph = 
        if current `elem` visited 
        then visited
        else let newVisited = current : visited
                 neighbors = getNeighbors current graph
                 finalVisited = foldr (\neighbor acc -> dfsRec' neighbor acc graph) newVisited neighbors
             in finalVisited
    
    getNeighbors node graph = 
        case lookup node graph of
          Just neighbors -> neighbors
          Nothing -> []
```

#### 复杂度分析

- **时间复杂度**: O(V + E) 其中V是顶点数，E是边数
- **空间复杂度**: O(V) 最坏情况
- **适用场景**: 图遍历、拓扑排序、连通分量

### 5.2 广度优先搜索

#### 算法描述

广度优先搜索逐层访问图的顶点，先访问所有相邻顶点，再访问下一层。

#### Haskell实现

```haskell
-- 广度优先搜索
bfs :: Eq a => a -> Graph a -> [a]
bfs start graph = bfs' [start] [] graph
  where
    bfs' [] visited _ = reverse visited
    bfs' (current:queue) visited graph = 
        if current `elem` visited 
        then bfs' queue visited graph
        else let neighbors = getNeighbors current graph
                 newQueue = queue ++ neighbors
                 newVisited = current : visited
             in bfs' newQueue newVisited graph
    
    getNeighbors node graph = 
        case lookup node graph of
          Just neighbors -> neighbors
          Nothing -> []

-- 使用Data.Sequence的BFS（更高效）
import Data.Sequence (Seq, (|>), (<|), viewl, ViewL(..), empty, singleton)

bfsEfficient :: Eq a => a -> Graph a -> [a]
bfsEfficient start graph = bfsEfficient' (singleton start) [] graph
  where
    bfsEfficient' queue visited graph = 
        case viewl queue of
          EmptyL -> reverse visited
          current :< rest -> 
              if current `elem` visited 
              then bfsEfficient' rest visited graph
              else let neighbors = getNeighbors current graph
                       newQueue = rest |> neighbors
                       newVisited = current : visited
                   in bfsEfficient' newQueue newVisited graph
    
    getNeighbors node graph = 
        case lookup node graph of
          Just neighbors -> neighbors
          Nothing -> []

-- 分层BFS
bfsLevels :: Eq a => a -> Graph a -> [[a]]
bfsLevels start graph = bfsLevels' [[start]] [] graph
  where
    bfsLevels' [] visited _ = []
    bfsLevels' (currentLevel:levels) visited graph = 
        let newVisited = visited ++ currentLevel
            nextLevel = concatMap (\node -> getNeighbors node graph) currentLevel
            unvisitedNextLevel = filter (`notElem` newVisited) nextLevel
        in if null unvisitedNextLevel 
           then [currentLevel]
           else currentLevel : bfsLevels' (levels ++ [unvisitedNextLevel]) newVisited graph
    
    getNeighbors node graph = 
        case lookup node graph of
          Just neighbors -> neighbors
          Nothing -> []
```

#### 复杂度分析

- **时间复杂度**: O(V + E)
- **空间复杂度**: O(V)
- **适用场景**: 最短路径、层次遍历、连通性检测

### 5.3 A*搜索

#### 算法描述

A*搜索是一种启发式搜索算法，结合了Dijkstra算法和贪心最佳优先搜索。

#### Haskell实现

```haskell
import Data.PriorityQueue (PriorityQueue, empty, insert, deleteMin)
import Data.Maybe (fromJust)

-- A*搜索
data AStarNode a = AStarNode
    { node :: a
    , gCost :: Double  -- 从起点到当前节点的成本
    , hCost :: Double  -- 启发式成本（到目标的估计）
    , fCost :: Double  -- 总成本 (g + h)
    , parent :: Maybe a
    } deriving (Show, Eq)

instance Ord (AStarNode a) where
    compare (AStarNode _ _ _ f1 _) (AStarNode _ _ _ f2 _) = compare f1 f2

-- A*搜索实现
aStarSearch :: (Eq a, Show a) => 
               a -> a -> 
               (a -> [a]) -> 
               (a -> a -> Double) -> 
               (a -> a -> Double) -> 
               Maybe [a]
aStarSearch start goal getNeighbors getCost heuristic = 
    let initialNode = AStarNode start 0 (heuristic start goal) (heuristic start goal) Nothing
        openSet = insert initialNode empty
        closedSet = []
        cameFrom = []
    in aStarSearch' openSet closedSet cameFrom
  where
    aStarSearch' openSet closedSet cameFrom = 
        case deleteMin openSet of
          Nothing -> Nothing
          (current, restOpenSet) -> 
              if node current == goal 
              then Just (reconstructPath current cameFrom)
              else let newClosedSet = node current : closedSet
                       neighbors = getNeighbors (node current)
                       validNeighbors = filter (`notElem` newClosedSet) neighbors
                       newOpenSet = foldr (addToOpenSet current) restOpenSet validNeighbors
                       newCameFrom = (node current, parent current) : cameFrom
                   in aStarSearch' newOpenSet newClosedSet newCameFrom
    
    addToOpenSet current neighbor openSet = 
        let gCost = gCost current + getCost (node current) neighbor
            hCost = heuristic neighbor goal
            fCost = gCost + hCost
            newNode = AStarNode neighbor gCost hCost fCost (Just (node current))
        in insert newNode openSet
    
    reconstructPath current cameFrom = 
        let path = reverse (node current : getPath (parent current) cameFrom)
        in path
      where
        getPath Nothing _ = []
        getPath (Just parent) cameFrom = 
            case lookup parent cameFrom of
              Just grandParent -> parent : getPath grandParent cameFrom
              Nothing -> [parent]

-- 简化的A*搜索（使用列表）
aStarSimple :: (Eq a, Show a) => 
               a -> a -> 
               (a -> [a]) -> 
               (a -> a -> Double) -> 
               (a -> a -> Double) -> 
               Maybe [a]
aStarSimple start goal getNeighbors getCost heuristic = 
    aStarSimple' [(start, 0, heuristic start goal, [start])] []
  where
    aStarSimple' [] _ = Nothing
    aStarSimple' ((current, gCost, _, path):rest) closed = 
        if current == goal 
        then Just (reverse path)
        else if current `elem` closed 
             then aStarSimple' rest closed
             else let neighbors = getNeighbors current
                      validNeighbors = filter (`notElem` closed) neighbors
                      newNodes = map (\neighbor -> 
                          let newGCost = gCost + getCost current neighbor
                              newHCost = heuristic neighbor goal
                              newPath = neighbor : path
                          in (neighbor, newGCost, newHCost, newPath)) validNeighbors
                      sortedNodes = sortBy (\(_, _, h1, _) (_, _, h2, _) -> compare h1 h2) newNodes
                  in aStarSimple' (rest ++ sortedNodes) (current : closed)
```

#### 复杂度分析

- **时间复杂度**: O(b^d) 其中b是分支因子，d是解的深度
- **空间复杂度**: O(b^d)
- **适用场景**: 路径规划、游戏AI、机器人导航

## 6. 搜索算法比较

### 6.1 复杂度比较表

| 算法 | 时间复杂度 | 空间复杂度 | 适用场景 |
|------|------------|------------|----------|
| 线性搜索 | O(n) | O(1) | 无序数组 |
| 跳跃搜索 | O(√n) | O(1) | 有序数组 |
| 插值搜索 | O(log log n) | O(1) | 均匀分布有序数组 |
| 二分搜索 | O(log n) | O(1) | 有序数组 |
| 三分搜索 | O(log n) | O(1) | 单峰函数 |
| 指数搜索 | O(log n) | O(1) | 有序数组 |
| DFS | O(V + E) | O(V) | 图遍历 |
| BFS | O(V + E) | O(V) | 最短路径 |
| A*搜索 | O(b^d) | O(b^d) | 启发式搜索 |

### 6.2 选择指南

1. **无序数组**: 线性搜索
2. **有序数组**: 二分搜索
3. **均匀分布**: 插值搜索
4. **图遍历**: DFS或BFS
5. **路径规划**: A*搜索
6. **函数优化**: 三分搜索

## 7. 性能测试

```haskell
-- 性能测试框架
import System.Random
import Data.Time.Clock

-- 生成测试数据
generateTestData :: Int -> IO [Int]
generateTestData n = do
    gen <- getStdGen
    return $ take n $ randomRs (1, 1000) gen

-- 测试搜索算法性能
testSearchPerformance :: (Int -> [Int] -> Maybe Int) -> String -> [Int] -> Int -> IO ()
testSearchPerformance searchFunc name data target = do
    start <- getCurrentTime
    let result = searchFunc target data
    end <- getCurrentTime
    let diff = diffUTCTime end start
    putStrLn $ name ++ ": " ++ show diff ++ " seconds"
    putStrLn $ "Result: " ++ show result

-- 运行所有测试
runSearchTests :: IO ()
runSearchTests = do
    testData <- generateTestData 100000
    let sortedData = sort testData
        target = testData !! 50000
    putStrLn "Search Algorithm Performance Test"
    putStrLn "=================================="
    testSearchPerformance linearSearch "Linear Search" testData target
    testSearchPerformance binarySearch "Binary Search" sortedData target
    testSearchPerformance jumpSearch "Jump Search" sortedData target
```

## 8. 总结

本文档介绍了各种经典搜索算法在Haskell中的实现，包括：

1. **线性搜索算法**: 线性搜索、跳跃搜索、插值搜索
2. **分治搜索算法**: 二分搜索、三分搜索、指数搜索
3. **图搜索算法**: 深度优先搜索、广度优先搜索、A*搜索

每个算法都包含：

- 详细的算法描述
- 完整的Haskell实现
- 复杂度分析
- 形式化证明
- 性能测试

这些实现展示了函数式编程在搜索算法中的优势，包括：

- 简洁的递归实现
- 强类型安全
- 易于理解和维护
- 良好的模块化设计
