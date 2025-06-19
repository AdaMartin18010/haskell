# 计算机科学 (Computer Science)

## 📚 概述

计算机科学是研究计算、信息处理和算法设计的科学。本文档从数学形式化的角度阐述计算机科学的基础概念，并通过Haskell代码实现相关算法和数据结构。

**相关文档：**
- [[001-Programming-Language-Theory]] - 编程语言理论
- [[002-System-Theory]] - 系统理论
- [[003-Category-Theory]] - 范畴论基础

---

## 1. 算法基础

### 1.1 算法定义

**定义 1.1 (算法)**
算法是一个有限的计算步骤序列，用于解决特定问题。

**定义 1.2 (算法正确性)**
算法 $A$ 对于问题 $P$ 是正确的，如果：
$$\forall x \in \text{input}(P), A(x) \in \text{output}(P, x)$$

**定义 1.3 (算法终止性)**
算法 $A$ 是终止的，如果对于所有输入，算法都在有限步内停止。

### 1.2 算法复杂度

**定义 1.4 (时间复杂度)**
算法的时间复杂度 $T(n)$ 是输入大小为 $n$ 时执行的基本操作数。

**定义 1.5 (空间复杂度)**
算法的空间复杂度 $S(n)$ 是输入大小为 $n$ 时使用的额外存储空间。

### 1.3 算法实现

```haskell
-- 算法类型
type Algorithm input output = input -> output

-- 算法分析
data AlgorithmAnalysis = AlgorithmAnalysis
  { timeComplexity :: String
  , spaceComplexity :: String
  , isCorrect :: Bool
  , isTerminating :: Bool
  } deriving (Show)

-- 示例：线性搜索
linearSearch :: Eq a => [a] -> a -> Maybe Int
linearSearch [] _ = Nothing
linearSearch (x:xs) target = 
  if x == target 
    then Just 0 
    else case linearSearch xs target of
           Just i -> Just (i + 1)
           Nothing -> Nothing

-- 线性搜索分析
linearSearchAnalysis :: AlgorithmAnalysis
linearSearchAnalysis = AlgorithmAnalysis
  { timeComplexity = "O(n)"
  , spaceComplexity = "O(1)"
  , isCorrect = True
  , isTerminating = True
  }

-- 二分搜索
binarySearch :: Ord a => [a] -> a -> Maybe Int
binarySearch [] _ = Nothing
binarySearch xs target = binarySearchHelper xs target 0 (length xs - 1)
  where
    binarySearchHelper [] _ _ _ = Nothing
    binarySearchHelper xs target left right
      | left > right = Nothing
      | otherwise = 
          let mid = (left + right) `div` 2
              midValue = xs !! mid
          in if target == midValue
               then Just mid
               else if target < midValue
                    then binarySearchHelper xs target left (mid - 1)
                    else binarySearchHelper xs target (mid + 1) right

-- 二分搜索分析
binarySearchAnalysis :: AlgorithmAnalysis
binarySearchAnalysis = AlgorithmAnalysis
  { timeComplexity = "O(log n)"
  , spaceComplexity = "O(1)"
  , isCorrect = True
  , isTerminating = True
  }
```

---

## 2. 数据结构

### 2.1 抽象数据类型

**定义 2.1 (抽象数据类型)**
抽象数据类型是一个数学模型，定义了一组操作和这些操作的语义。

**定义 2.2 (栈)**
栈是一个后进先出(LIFO)的数据结构，支持以下操作：
- `push(x)`：将元素 $x$ 压入栈顶
- `pop()`：移除并返回栈顶元素
- `top()`：返回栈顶元素
- `isEmpty()`：检查栈是否为空

### 2.2 数据结构实现

```haskell
-- 栈
data Stack a = Stack [a] deriving (Show)

-- 栈操作
emptyStack :: Stack a
emptyStack = Stack []

isEmpty :: Stack a -> Bool
isEmpty (Stack []) = True
isEmpty _ = False

push :: a -> Stack a -> Stack a
push x (Stack xs) = Stack (x:xs)

pop :: Stack a -> Maybe (a, Stack a)
pop (Stack []) = Nothing
pop (Stack (x:xs)) = Just (x, Stack xs)

top :: Stack a -> Maybe a
top (Stack []) = Nothing
top (Stack (x:_)) = Just x

-- 队列
data Queue a = Queue [a] [a] deriving (Show)

-- 队列操作
emptyQueue :: Queue a
emptyQueue = Queue [] []

isEmptyQueue :: Queue a -> Bool
isEmptyQueue (Queue [] []) = True
isEmptyQueue _ = False

enqueue :: a -> Queue a -> Queue a
enqueue x (Queue front back) = Queue front (x:back)

dequeue :: Queue a -> Maybe (a, Queue a)
dequeue (Queue [] []) = Nothing
dequeue (Queue [] back) = dequeue (Queue (reverse back) [])
dequeue (Queue (x:front) back) = Just (x, Queue front back)

-- 二叉树
data BinaryTree a = 
    Empty
  | Node a (BinaryTree a) (BinaryTree a)
  deriving (Show, Eq)

-- 二叉树操作
insert :: Ord a => a -> BinaryTree a -> BinaryTree a
insert x Empty = Node x Empty Empty
insert x (Node y left right) = 
  if x <= y 
    then Node y (insert x left) right
    else Node y left (insert x right)

search :: Ord a => a -> BinaryTree a -> Bool
search _ Empty = False
search x (Node y left right) = 
  if x == y 
    then True
    else if x < y 
         then search x left
         else search x right

-- 遍历
inorder :: BinaryTree a -> [a]
inorder Empty = []
inorder (Node x left right) = inorder left ++ [x] ++ inorder right

preorder :: BinaryTree a -> [a]
preorder Empty = []
preorder (Node x left right) = [x] ++ preorder left ++ preorder right

postorder :: BinaryTree a -> [a]
postorder Empty = []
postorder (Node x left right) = postorder left ++ postorder right ++ [x]
```

---

## 3. 排序算法

### 3.1 排序问题

**定义 3.1 (排序问题)**
给定序列 $A = [a_1, a_2, \ldots, a_n]$，找到排列 $\pi$ 使得 $a_{\pi(1)} \leq a_{\pi(2)} \leq \ldots \leq a_{\pi(n)}$。

**定义 3.2 (稳定排序)**
排序算法是稳定的，如果相等元素的相对顺序在排序后保持不变。

### 3.2 排序算法实现

```haskell
-- 冒泡排序
bubbleSort :: Ord a => [a] -> [a]
bubbleSort [] = []
bubbleSort xs = 
  let (swapped, newXs) = bubblePass xs
  in if swapped 
       then bubbleSort newXs
       else newXs
  where
    bubblePass [] = (False, [])
    bubblePass [x] = (False, [x])
    bubblePass (x:y:xs) = 
      if x > y 
        then let (swapped, rest) = bubblePass (x:xs)
             in (True, y:rest)
        else let (swapped, rest) = bubblePass (y:xs)
             in (swapped, x:rest)

-- 快速排序
quickSort :: Ord a => [a] -> [a]
quickSort [] = []
quickSort (x:xs) = 
  let smaller = [a | a <- xs, a <= x]
      larger = [a | a <- xs, a > x]
  in quickSort smaller ++ [x] ++ quickSort larger

-- 归并排序
mergeSort :: Ord a => [a] -> [a]
mergeSort [] = []
mergeSort [x] = [x]
mergeSort xs = 
  let (left, right) = splitAt (length xs `div` 2) xs
  in merge (mergeSort left) (mergeSort right)

merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys) = 
  if x <= y 
    then x : merge xs (y:ys)
    else y : merge (x:xs) ys

-- 堆排序
heapSort :: Ord a => [a] -> [a]
heapSort xs = 
  let heap = buildHeap xs
  in heapSortHelper heap []
  where
    heapSortHelper Empty result = result
    heapSortHelper heap result = 
      let (value, newHeap) = extractMax heap
      in heapSortHelper newHeap (value:result)

-- 堆数据结构
data Heap a = 
    EmptyHeap
  | HeapNode a (Heap a) (Heap a)
  deriving (Show)

-- 构建堆
buildHeap :: Ord a => [a] -> Heap a
buildHeap = foldr insertHeap EmptyHeap

-- 插入堆
insertHeap :: Ord a => a -> Heap a -> Heap a
insertHeap x EmptyHeap = HeapNode x EmptyHeap EmptyHeap
insertHeap x (HeapNode y left right) = 
  if x > y 
    then HeapNode x (insertHeap y left) right
    else HeapNode y (insertHeap x left) right

-- 提取最大值
extractMax :: Ord a => Heap a -> (a, Heap a)
extractMax (HeapNode x left right) = (x, mergeHeaps left right)

-- 合并堆
mergeHeaps :: Ord a => Heap a -> Heap a -> Heap a
mergeHeaps EmptyHeap h = h
mergeHeaps h EmptyHeap = h
mergeHeaps (HeapNode x left1 right1) (HeapNode y left2 right2) = 
  if x > y 
    then HeapNode x (mergeHeaps left1 right1) (HeapNode y left2 right2)
    else HeapNode y (HeapNode x left1 right1) (mergeHeaps left2 right2)
```

---

## 4. 图算法

### 4.1 图定义

**定义 4.1 (图)**
图 $G = (V, E)$ 是一个二元组，其中：
- $V$ 是顶点集合
- $E \subseteq V \times V$ 是边集合

**定义 4.2 (路径)**
路径是顶点序列 $v_1, v_2, \ldots, v_k$，其中 $(v_i, v_{i+1}) \in E$。

### 4.2 图算法实现

```haskell
-- 图表示
data Graph a = Graph
  { vertices :: [a]
  , edges :: [(a, a)]
  } deriving (Show)

-- 邻接表表示
type AdjacencyList a = Map a [a]

-- 构建邻接表
buildAdjacencyList :: Eq a => Graph a -> AdjacencyList a
buildAdjacencyList graph = 
  let initialMap = Map.fromList [(v, []) | v <- vertices graph]
  in foldr addEdge initialMap (edges graph)
  where
    addEdge (u, v) map = 
      let neighbors = Map.findWithDefault [] u map
      in Map.insert u (v:neighbors) map

-- 深度优先搜索
dfs :: Eq a => AdjacencyList a -> a -> [a]
dfs adjList start = dfsHelper adjList start []
  where
    dfsHelper adjList current visited = 
      if current `elem` visited 
        then visited
        else let neighbors = Map.findWithDefault [] current adjList
                 newVisited = current:visited
             in foldr (dfsHelper adjList) newVisited neighbors

-- 广度优先搜索
bfs :: Eq a => AdjacencyList a -> a -> [a]
bfs adjList start = bfsHelper adjList [start] [start]
  where
    bfsHelper _ [] visited = visited
    bfsHelper adjList (current:queue) visited = 
      let neighbors = Map.findWithDefault [] current adjList
          unvisitedNeighbors = [n | n <- neighbors, n `notElem` visited]
          newQueue = queue ++ unvisitedNeighbors
          newVisited = visited ++ unvisitedNeighbors
      in bfsHelper adjList newQueue newVisited

-- 最短路径：Dijkstra算法
dijkstra :: (Eq a, Ord b, Num b) => AdjacencyList a -> Map (a, a) b -> a -> Map a b
dijkstra adjList weights start = 
  let initialDistances = Map.insert start 0 (Map.fromList [(v, maxBound) | v <- Map.keys adjList])
  in dijkstraHelper adjList weights initialDistances [start]
  where
    dijkstraHelper _ _ distances [] = distances
    dijkstraHelper adjList weights distances (current:queue) = 
      let neighbors = Map.findWithDefault [] current adjList
          currentDist = Map.findWithDefault maxBound current distances
          updatedDistances = foldr (updateDistance current currentDist) distances neighbors
          newQueue = queue ++ [n | n <- neighbors, n `notElem` queue]
      in dijkstraHelper adjList weights updatedDistances newQueue

    updateDistance current currentDist neighbor distances = 
      let weight = Map.findWithDefault maxBound (current, neighbor) weights
          newDist = currentDist + weight
          oldDist = Map.findWithDefault maxBound neighbor distances
      in if newDist < oldDist 
           then Map.insert neighbor newDist distances
           else distances

-- 最小生成树：Kruskal算法
kruskal :: (Eq a, Ord b, Num b) => Graph a -> Map (a, a) b -> [(a, a)]
kruskal graph weights = 
  let sortedEdges = sortBy (comparing snd) [(edge, Map.findWithDefault maxBound edge weights) | edge <- edges graph]
      initialSets = Map.fromList [(v, [v]) | v <- vertices graph]
  in kruskalHelper sortedEdges initialSets []
  where
    kruskalHelper [] _ mst = mst
    kruskalHelper ((u, v):edges) sets mst = 
      let setU = findSet u sets
          setV = findSet v sets
      in if setU == setV
           then kruskalHelper edges sets mst
           else let newSets = unionSets u v sets
                in kruskalHelper edges newSets ((u, v):mst)

    findSet vertex sets = 
      case Map.lookup vertex sets of
        Just set -> if vertex `elem` set then set else findSet (head set) sets
        Nothing -> [vertex]

    unionSets u v sets = 
      let setU = findSet u sets
          setV = findSet v sets
          newSet = setU ++ setV
      in foldr (\vertex -> Map.insert vertex newSet) sets newSet
```

---

## 5. 动态规划

### 5.1 动态规划原理

**定义 5.1 (最优子结构)**
问题具有最优子结构，如果问题的最优解包含其子问题的最优解。

**定义 5.2 (重叠子问题)**
问题具有重叠子问题，如果递归算法重复解决相同的子问题。

### 5.2 动态规划实现

```haskell
-- 斐波那契数列
fibonacci :: Int -> Integer
fibonacci n = fibMemo n (Map.singleton 0 0)
  where
    fibMemo 0 memo = Map.findWithDefault 0 0 memo
    fibMemo 1 memo = Map.findWithDefault 1 1 memo
    fibMemo n memo = 
      case Map.lookup n memo of
        Just value -> value
        Nothing -> 
          let fib1 = fibMemo (n-1) memo
              fib2 = fibMemo (n-2) memo
              newMemo = Map.insert n (fib1 + fib2) memo
          in fibMemo n newMemo

-- 最长公共子序列
longestCommonSubsequence :: Eq a => [a] -> [a] -> [a]
longestCommonSubsequence xs ys = 
  let table = lcsTable xs ys
  in lcsBacktrack table xs ys (length xs) (length ys)
  where
    lcsTable xs ys = 
      let m = length xs
          n = length ys
          table = array ((0,0), (m,n)) [((i,j), 0) | i <- [0..m], j <- [0..n]]
      in foldr (\i table -> 
                foldr (\j table -> 
                      if i == 0 || j == 0 
                        then table
                        else if xs !! (i-1) == ys !! (j-1)
                             then table // [((i,j), 1 + table ! (i-1,j-1))]
                             else table // [((i,j), max (table ! (i-1,j)) (table ! (i,j-1)))]
                ) table [1..n]
               ) table [1..m]

    lcsBacktrack table xs ys i j
      | i == 0 || j == 0 = []
      | xs !! (i-1) == ys !! (j-1) = lcsBacktrack table xs ys (i-1) (j-1) ++ [xs !! (i-1)]
      | table ! (i-1,j) >= table ! (i,j-1) = lcsBacktrack table xs ys (i-1) j
      | otherwise = lcsBacktrack table xs ys i (j-1)

-- 背包问题
knapsack :: [(Int, Int)] -> Int -> Int
knapsack items capacity = 
  let n = length items
      table = array ((0,0), (n,capacity)) [((i,w), 0) | i <- [0..n], w <- [0..capacity]]
  in knapsackHelper items capacity n table
  where
    knapsackHelper items capacity n table = 
      let filledTable = foldr (\i table -> 
                              foldr (\w table -> 
                                    let (value, weight) = items !! (i-1)
                                    in if weight <= w
                                         then let include = value + table ! (i-1, w-weight)
                                                  exclude = table ! (i-1, w)
                                              in table // [((i,w), max include exclude)]
                                         else table // [((i,w), table ! (i-1, w))]
                              ) table [0..capacity]
                             ) table [1..n]
      in filledTable ! (n, capacity)
```

---

## 6. 计算复杂性

### 6.1 复杂度类

**定义 6.1 (P类)**
P类是可以在多项式时间内解决的问题集合。

**定义 6.2 (NP类)**
NP类是可以在多项式时间内验证解的问题集合。

**定义 6.3 (NP完全)**
问题 $L$ 是NP完全的，如果：
1. $L \in \text{NP}$
2. $\forall L' \in \text{NP}, L' \leq_p L$

### 6.2 复杂度分析实现

```haskell
-- 复杂度分析
data ComplexityClass = P | NP | NPComplete | NPHard | PSPACE deriving (Show, Eq)

-- 问题分类
data Problem = Problem
  { name :: String
  , complexity :: ComplexityClass
  , description :: String
  } deriving (Show)

-- 常见问题
commonProblems :: [Problem]
commonProblems = 
  [ Problem "排序" P "对数组进行排序"
  , Problem "搜索" P "在数组中搜索元素"
  , Problem "最短路径" P "找到图中两点间的最短路径"
  , Problem "旅行商问题" NPComplete "找到访问所有城市一次的最短路径"
  , Problem "背包问题" NP "在容量限制下选择物品使价值最大"
  , Problem "图着色" NPComplete "用最少的颜色给图着色"
  ]

-- 多项式时间归约
class PolynomialReducible a where
  reduce :: a -> a -> Bool

-- 示例：3-SAT到独立集的归约
data ThreeSAT = ThreeSAT
  { clauses :: [[String]]
  , variables :: [String]
  } deriving (Show)

data IndependentSet = IndependentSet
  { vertices :: [String]
  , edges :: [(String, String)]
  } deriving (Show)

-- 3-SAT到独立集的归约
reduce3SATToIndependentSet :: ThreeSAT -> IndependentSet
reduce3SATToIndependentSet (ThreeSAT clauses variables) = 
  let vertices = concatMap (\clause -> 
                            [show i ++ "_" ++ literal | (i, literal) <- zip [0..] clause]) clauses
      edges = concatMap (\clause -> 
                         [(show i ++ "_" ++ literal1, show j ++ "_" ++ literal2) | 
                          (i, literal1) <- zip [0..] clause,
                          (j, literal2) <- zip [0..] clause,
                          i /= j]) clauses
  in IndependentSet vertices edges
```

---

## 7. 自动机理论

### 7.1 有限自动机

**定义 7.1 (有限自动机)**
有限自动机是一个五元组 $(Q, \Sigma, \delta, q_0, F)$，其中：
- $Q$ 是状态集合
- $\Sigma$ 是输入字母表
- $\delta : Q \times \Sigma \to Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

### 7.2 自动机实现

```haskell
-- 有限自动机
data FiniteAutomaton = FiniteAutomaton
  { states :: [String]
  , alphabet :: [Char]
  , transitions :: Map (String, Char) String
  , initialState :: String
  , acceptingStates :: [String]
  } deriving (Show)

-- 运行自动机
runAutomaton :: FiniteAutomaton -> String -> Bool
runAutomaton fa input = 
  let finalState = foldl (step fa) (initialState fa) input
  in finalState `elem` acceptingStates fa

step :: FiniteAutomaton -> String -> Char -> String
step fa currentState symbol = 
  Map.findWithDefault currentState (currentState, symbol) (transitions fa)

-- 示例：识别偶数个1的自动机
evenOnesAutomaton :: FiniteAutomaton
evenOnesAutomaton = FiniteAutomaton
  { states = ["even", "odd"]
  , alphabet = ['0', '1']
  , transitions = Map.fromList 
      [ (("even", '0'), "even")
      , (("even", '1'), "odd")
      , (("odd", '0'), "odd")
      , (("odd", '1'), "even")
      ]
  , initialState = "even"
  , acceptingStates = ["even"]
  }

-- 正则表达式
data Regex = 
    Empty
  | Epsilon
  | Char Char
  | Concat Regex Regex
  | Union Regex Regex
  | Star Regex
  deriving (Show)

-- 正则表达式匹配
matchRegex :: Regex -> String -> Bool
matchRegex Empty _ = False
matchRegex Epsilon "" = True
matchRegex Epsilon _ = False
matchRegex (Char c) [x] = c == x
matchRegex (Char _) _ = False
matchRegex (Concat r1 r2) s = 
  any (\i -> matchRegex r1 (take i s) && matchRegex r2 (drop i s)) [0..length s]
matchRegex (Union r1 r2) s = matchRegex r1 s || matchRegex r2 s
matchRegex (Star r) s = 
  s == "" || any (\i -> matchRegex r (take i s) && matchRegex (Star r) (drop i s)) [1..length s]
```

---

## 8. 结论

计算机科学为软件开发提供了坚实的理论基础。通过形式化的定义和Haskell实现，我们可以：

1. **设计算法**：使用各种算法设计技术解决问题
2. **分析复杂度**：评估算法的时间和空间效率
3. **实现数据结构**：构建高效的数据组织方式
4. **解决图问题**：处理网络和关系数据
5. **应用动态规划**：解决具有最优子结构的问题
6. **理解计算复杂性**：分析问题的可解性

计算机科学的应用范围广泛，从算法设计到系统架构，从人工智能到网络安全，都离不开计算机科学的支持。

---

## 参考文献

1. Cormen, T. H., Leiserson, C. E., Rivest, R. L., & Stein, C. (2009). Introduction to algorithms.
2. Sipser, M. (2012). Introduction to the theory of computation.
3. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). Introduction to automata theory, languages, and computation.
4. Kleinberg, J., & Tardos, É. (2005). Algorithm design.
5. Papadimitriou, C. H. (1994). Computational complexity. 