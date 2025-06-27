# Haskell基本数据结构

## 📚 快速导航

### 相关理论

- [函数式编程基础](../01-Basic-Concepts/001-Functional-Programming-Foundation.md)
- [递归和列表](../01-Basic-Concepts/003-Recursion-and-Lists.md)
- [类型系统基础](../04-Type-System/001-Type-System-Foundation.md)

### 实现示例

- [高级数据结构](./002-Advanced-Data-Structures.md)
- [算法实现](../07-Algorithms/001-Sorting-Algorithms.md)
- [性能优化](../09-Performance/001-Performance-Analysis.md)

### 应用领域

- [Web开发](../11-Web-Development/001-Web-Development-Foundation.md)
- [系统编程](../12-System-Programming/001-System-Programming-Foundation.md)
- [科学计算](../09-Scientific-Computing/001-Numerical-Computation.md)

## 🎯 概述

数据结构是计算机科学的基础，在Haskell中，数据结构的设计充分利用了函数式编程的特性。本文档介绍Haskell中的基本数据结构，包括列表、树、图等，以及它们的实现和操作。

## 📖 1. 列表数据结构

### 1.1 列表基础

**定义 1.1 (列表)**
列表是Haskell中最基本的数据结构，表示有序的元素序列。

**数学表示：**
$$[a] = \text{Nil} \mid \text{Cons } a \text{ } [a]$$

**Haskell实现：**

```haskell
-- 列表基本操作
listBasics :: IO ()
listBasics = do
  let -- 列表构造
      emptyList = []
      singleElement = [1]
      multipleElements = [1, 2, 3, 4, 5]
      
      -- 列表操作
      headResult = head multipleElements
      tailResult = tail multipleElements
      lengthResult = length multipleElements
      nullResult = null emptyList
  putStrLn $ "Empty list: " ++ show emptyList
  putStrLn $ "Single element: " ++ show singleElement
  putStrLn $ "Multiple elements: " ++ show multipleElements
  putStrLn $ "Head: " ++ show headResult
  putStrLn $ "Tail: " ++ show tailResult
  putStrLn $ "Length: " ++ show lengthResult
  putStrLn $ "Is null: " ++ show nullResult
```

### 1.2 列表操作

**定义 1.2 (列表操作)**
列表支持丰富的操作，包括映射、过滤、折叠等。

**Haskell实现：**

```haskell
-- 列表操作函数
listOperations :: IO ()
listOperations = do
  let numbers = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
      
      -- 映射操作
      doubled = map (*2) numbers
      squared = map (^2) numbers
      
      -- 过滤操作
      evens = filter even numbers
      odds = filter odd numbers
      greaterThan5 = filter (>5) numbers
      
      -- 折叠操作
      sumResult = foldr (+) 0 numbers
      productResult = foldr (*) 1 numbers
      maxResult = foldr max (head numbers) numbers
      
      -- 列表推导式
      comprehension = [x^2 | x <- numbers, even x, x > 5]
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Doubled: " ++ show doubled
  putStrLn $ "Squared: " ++ show squared
  putStrLn $ "Evens: " ++ show evens
  putStrLn $ "Odds: " ++ show odds
  putStrLn $ "Greater than 5: " ++ show greaterThan5
  putStrLn $ "Sum: " ++ show sumResult
  putStrLn $ "Product: " ++ show productResult
  putStrLn $ "Maximum: " ++ show maxResult
  putStrLn $ "Comprehension: " ++ show comprehension
```

### 1.3 列表实现

**定义 1.3 (列表实现)**
列表的内部实现基于代数数据类型。

**Haskell实现：**

```haskell
-- 自定义列表实现
data CustomList a = 
  CNil | 
  CCons a (CustomList a)
  deriving (Show)

-- 自定义列表操作
customLength :: CustomList a -> Int
customLength CNil = 0
customLength (CCons _ xs) = 1 + customLength xs

customMap :: (a -> b) -> CustomList a -> CustomList b
customMap _ CNil = CNil
customMap f (CCons x xs) = CCons (f x) (customMap f xs)

customFilter :: (a -> Bool) -> CustomList a -> CustomList a
customFilter _ CNil = CNil
customFilter p (CCons x xs)
  | p x = CCons x (customFilter p xs)
  | otherwise = customFilter p xs

-- 自定义列表示例
customListExample :: IO ()
customListExample = do
  let -- 构造自定义列表
      emptyCustom = CNil
      singleCustom = CCons 1 CNil
      multipleCustom = CCons 1 (CCons 2 (CCons 3 CNil))
      
      -- 操作自定义列表
      lengthResult = customLength multipleCustom
      mappedResult = customMap (*2) multipleCustom
      filteredResult = customFilter even multipleCustom
  putStrLn $ "Empty custom list: " ++ show emptyCustom
  putStrLn $ "Single element: " ++ show singleCustom
  putStrLn $ "Multiple elements: " ++ show multipleCustom
  putStrLn $ "Length: " ++ show lengthResult
  putStrLn $ "Mapped: " ++ show mappedResult
  putStrLn $ "Filtered: " ++ show filteredResult
```

## 🔧 2. 栈数据结构

### 2.1 栈基础

**定义 2.1 (栈)**
栈是后进先出（LIFO）的数据结构。

**数学表示：**
$$\text{Stack } a = \text{Empty} \mid \text{Push } a \text{ } (\text{Stack } a)$$

**Haskell实现：**

```haskell
-- 栈数据类型
data Stack a = 
  Empty | 
  Push a (Stack a)
  deriving (Show)

-- 栈操作
isEmpty :: Stack a -> Bool
isEmpty Empty = True
isEmpty _ = False

push :: a -> Stack a -> Stack a
push x s = Push x s

pop :: Stack a -> Maybe (a, Stack a)
pop Empty = Nothing
pop (Push x s) = Just (x, s)

top :: Stack a -> Maybe a
top Empty = Nothing
top (Push x _) = Just x

-- 栈示例
stackExample :: IO ()
stackExample = do
  let -- 构造栈
      emptyStack = Empty
      stack1 = push 1 emptyStack
      stack2 = push 2 stack1
      stack3 = push 3 stack2
      
      -- 栈操作
      topResult = top stack3
      (popped, remaining) = case pop stack3 of
                              Just (x, s) -> (x, s)
                              Nothing -> error "Empty stack"
  putStrLn $ "Stack: " ++ show stack3
  putStrLn $ "Top: " ++ show topResult
  putStrLn $ "Popped: " ++ show popped
  putStrLn $ "Remaining: " ++ show remaining
```

### 2.2 栈应用

**定义 2.2 (栈应用)**
栈在表达式求值、括号匹配等场景中有重要应用。

**Haskell实现：**

```haskell
-- 括号匹配
bracketMatching :: String -> Bool
bracketMatching = go Empty
  where
    go _ [] = isEmpty Empty
    go s (c:cs)
      | c == '(' = go (push c s) cs
      | c == '[' = go (push c s) cs
      | c == '{' = go (push c s) cs
      | c == ')' = case pop s of
                     Just ('(', s') -> go s' cs
                     _ -> False
      | c == ']' = case pop s of
                     Just ('[', s') -> go s' cs
                     _ -> False
      | c == '}' = case pop s of
                     Just ('{', s') -> go s' cs
                     _ -> False
      | otherwise = go s cs

-- 栈应用示例
stackApplicationExample :: IO ()
stackApplicationExample = do
  let testCases = [
        "()",
        "([])",
        "{[()]}",
        "([)]",
        "(((",
        ")))"
      ]
      
      results = map bracketMatching testCases
  putStrLn "Bracket matching results:"
  zipWithM_ (\test result -> 
    putStrLn $ test ++ " -> " ++ show result) testCases results
```

## 💾 3. 队列数据结构

### 3.1 队列基础

**定义 3.1 (队列)**
队列是先进先出（FIFO）的数据结构。

**数学表示：**
$$\text{Queue } a = \text{Empty} \mid \text{Enqueue } a \text{ } (\text{Queue } a)$$

**Haskell实现：**

```haskell
-- 队列数据类型
data Queue a = 
  QEmpty | 
  QEnqueue a (Queue a)
  deriving (Show)

-- 队列操作
qIsEmpty :: Queue a -> Bool
qIsEmpty QEmpty = True
qIsEmpty _ = False

enqueue :: a -> Queue a -> Queue a
enqueue x QEmpty = QEnqueue x QEmpty
enqueue x (QEnqueue y q) = QEnqueue y (enqueue x q)

dequeue :: Queue a -> Maybe (a, Queue a)
dequeue QEmpty = Nothing
dequeue (QEnqueue x q) = Just (x, q)

front :: Queue a -> Maybe a
front QEmpty = Nothing
front (QEnqueue x _) = Just x

-- 队列示例
queueExample :: IO ()
queueExample = do
  let -- 构造队列
      emptyQueue = QEmpty
      queue1 = enqueue 1 emptyQueue
      queue2 = enqueue 2 queue1
      queue3 = enqueue 3 queue2
      
      -- 队列操作
      frontResult = front queue3
      (dequeued, remaining) = case dequeue queue3 of
                                Just (x, q) -> (x, q)
                                Nothing -> error "Empty queue"
  putStrLn $ "Queue: " ++ show queue3
  putStrLn $ "Front: " ++ show frontResult
  putStrLn $ "Dequeued: " ++ show dequeued
  putStrLn $ "Remaining: " ++ show remaining
```

### 3.2 高效队列实现

**定义 3.2 (高效队列)**
使用两个列表实现高效的队列操作。

**Haskell实现：**

```haskell
-- 高效队列实现
data EfficientQueue a = Queue [a] [a]
  deriving (Show)

-- 高效队列操作
eqEmpty :: EfficientQueue a
eqEmpty = Queue [] []

eqIsEmpty :: EfficientQueue a -> Bool
eqIsEmpty (Queue [] []) = True
eqIsEmpty _ = False

eqEnqueue :: a -> EfficientQueue a -> EfficientQueue a
eqEnqueue x (Queue front rear) = Queue front (x:rear)

eqDequeue :: EfficientQueue a -> Maybe (a, EfficientQueue a)
eqDequeue (Queue [] []) = Nothing
eqDequeue (Queue [] rear) = eqDequeue (Queue (reverse rear) [])
eqDequeue (Queue (x:front) rear) = Just (x, Queue front rear)

eqFront :: EfficientQueue a -> Maybe a
eqFront (Queue [] []) = Nothing
eqFront (Queue [] rear) = eqFront (Queue (reverse rear) [])
eqFront (Queue (x:_) _) = Just x

-- 高效队列示例
efficientQueueExample :: IO ()
efficientQueueExample = do
  let -- 构造高效队列
      emptyEQ = eqEmpty
      eq1 = eqEnqueue 1 emptyEQ
      eq2 = eqEnqueue 2 eq1
      eq3 = eqEnqueue 3 eq2
      
      -- 队列操作
      frontResult = eqFront eq3
      (dequeued, remaining) = case eqDequeue eq3 of
                                Just (x, q) -> (x, q)
                                Nothing -> error "Empty queue"
  putStrLn $ "Efficient queue: " ++ show eq3
  putStrLn $ "Front: " ++ show frontResult
  putStrLn $ "Dequeued: " ++ show dequeued
  putStrLn $ "Remaining: " ++ show remaining
```

## 🎭 4. 树数据结构

### 4.1 二叉树

**定义 4.1 (二叉树)**
二叉树是每个节点最多有两个子节点的树结构。

**数学表示：**
$$\text{BinaryTree } a = \text{Empty} \mid \text{Node } a \text{ } (\text{BinaryTree } a) \text{ } (\text{BinaryTree } a)$$

**Haskell实现：**

```haskell
-- 二叉树数据类型
data BinaryTree a = 
  BEmpty | 
  BNode a (BinaryTree a) (BinaryTree a)
  deriving (Show)

-- 二叉树操作
btInsert :: Ord a => a -> BinaryTree a -> BinaryTree a
btInsert x BEmpty = BNode x BEmpty BEmpty
btInsert x (BNode y left right)
  | x < y = BNode y (btInsert x left) right
  | x > y = BNode y left (btInsert x right)
  | otherwise = BNode y left right

btSearch :: Ord a => a -> BinaryTree a -> Bool
btSearch _ BEmpty = False
btSearch x (BNode y left right)
  | x == y = True
  | x < y = btSearch x left
  | otherwise = btSearch x right

btSize :: BinaryTree a -> Int
btSize BEmpty = 0
btSize (BNode _ left right) = 1 + btSize left + btSize right

btHeight :: BinaryTree a -> Int
btHeight BEmpty = 0
btHeight (BNode _ left right) = 1 + max (btHeight left) (btHeight right)

-- 二叉树示例
binaryTreeExample :: IO ()
binaryTreeExample = do
  let -- 构造二叉树
      emptyBT = BEmpty
      bt1 = btInsert 5 emptyBT
      bt2 = btInsert 3 bt1
      bt3 = btInsert 7 bt2
      bt4 = btInsert 1 bt3
      bt5 = btInsert 9 bt4
      
      -- 二叉树操作
      searchResult = btSearch 3 bt5
      sizeResult = btSize bt5
      heightResult = btHeight bt5
  putStrLn $ "Binary tree: " ++ show bt5
  putStrLn $ "Search for 3: " ++ show searchResult
  putStrLn $ "Size: " ++ show sizeResult
  putStrLn $ "Height: " ++ show heightResult
```

### 4.2 树遍历

**定义 4.2 (树遍历)**
树遍历包括前序、中序、后序遍历。

**Haskell实现：**

```haskell
-- 树遍历
preorder :: BinaryTree a -> [a]
preorder BEmpty = []
preorder (BNode x left right) = [x] ++ preorder left ++ preorder right

inorder :: BinaryTree a -> [a]
inorder BEmpty = []
inorder (BNode x left right) = inorder left ++ [x] ++ inorder right

postorder :: BinaryTree a -> [a]
postorder BEmpty = []
postorder (BNode x left right) = postorder left ++ postorder right ++ [x]

-- 层序遍历
levelorder :: BinaryTree a -> [a]
levelorder BEmpty = []
levelorder tree = go [tree]
  where
    go [] = []
    go (BEmpty:rest) = go rest
    go (BNode x left right:rest) = x : go (rest ++ [left, right])

-- 树遍历示例
treeTraversalExample :: IO ()
treeTraversalExample = do
  let -- 构造测试树
      testTree = BNode 1 
                  (BNode 2 
                    (BNode 4 BEmpty BEmpty) 
                    (BNode 5 BEmpty BEmpty))
                  (BNode 3 
                    (BNode 6 BEmpty BEmpty) 
                    (BNode 7 BEmpty BEmpty))
      
      -- 遍历结果
      preorderResult = preorder testTree
      inorderResult = inorder testTree
      postorderResult = postorder testTree
      levelorderResult = levelorder testTree
  putStrLn $ "Test tree: " ++ show testTree
  putStrLn $ "Preorder: " ++ show preorderResult
  putStrLn $ "Inorder: " ++ show inorderResult
  putStrLn $ "Postorder: " ++ show postorderResult
  putStrLn $ "Level order: " ++ show levelorderResult
```

## ⚡ 5. 堆数据结构

### 5.1 最小堆

**定义 5.1 (最小堆)**
最小堆是完全二叉树，其中每个节点的值都小于或等于其子节点的值。

**Haskell实现：**

```haskell
-- 最小堆数据类型
data MinHeap a = 
  MHEmpty | 
  MHNode a (MinHeap a) (MinHeap a)
  deriving (Show)

-- 最小堆操作
mhInsert :: Ord a => a -> MinHeap a -> MinHeap a
mhInsert x MHEmpty = MHNode x MHEmpty MHEmpty
mhInsert x (MHNode y left right)
  | x <= y = MHNode x (mhInsert y right) left
  | otherwise = MHNode y (mhInsert x right) left

mhExtractMin :: Ord a => MinHeap a -> Maybe (a, MinHeap a)
mhExtractMin MHEmpty = Nothing
mhExtractMin (MHNode x left right) = Just (x, mhMerge left right)

mhMerge :: Ord a => MinHeap a -> MinHeap a -> MinHeap a
mhMerge MHEmpty h = h
mhMerge h MHEmpty = h
mhMerge (MHNode x left1 right1) (MHNode y left2 right2)
  | x <= y = MHNode x (mhMerge right1 (MHNode y left2 right2)) left1
  | otherwise = MHNode y (mhMerge (MHNode x left1 right1) right2) left2

-- 最小堆示例
minHeapExample :: IO ()
minHeapExample = do
  let -- 构造最小堆
      emptyMH = MHEmpty
      mh1 = mhInsert 5 emptyMH
      mh2 = mhInsert 3 mh1
      mh3 = mhInsert 7 mh2
      mh4 = mhInsert 1 mh3
      
      -- 堆操作
      extractResult = mhExtractMin mh4
  putStrLn $ "Min heap: " ++ show mh4
  putStrLn $ "Extract min: " ++ show extractResult
```

### 5.2 堆排序

**定义 5.2 (堆排序)**
堆排序使用堆数据结构进行排序。

**Haskell实现：**

```haskell
-- 堆排序
heapSort :: Ord a => [a] -> [a]
heapSort xs = heapSortHelper (buildHeap xs)
  where
    buildHeap = foldr mhInsert MHEmpty
    
    heapSortHelper MHEmpty = []
    heapSortHelper heap = 
      case mhExtractMin heap of
        Just (min, rest) -> min : heapSortHelper rest
        Nothing -> []

-- 堆排序示例
heapSortExample :: IO ()
heapSortExample = do
  let numbers = [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
      sorted = heapSort numbers
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Heap sorted: " ++ show sorted
```

## 🔄 6. 图数据结构

### 6.1 图表示

**定义 6.1 (图)**
图是由顶点和边组成的数学结构。

**数学表示：**
$$G = (V, E) \text{ where } V \text{ is vertices and } E \text{ is edges}$$

**Haskell实现：**

```haskell
-- 图数据类型
type Vertex = Int
type Edge = (Vertex, Vertex)
type Graph = [Edge]

-- 图操作
graphVertices :: Graph -> [Vertex]
graphVertices = nub . concatMap (\(u, v) -> [u, v])

graphEdges :: Graph -> [Edge]
graphEdges = id

graphNeighbors :: Graph -> Vertex -> [Vertex]
graphNeighbors graph v = [u | (u, w) <- graph, w == v] ++ 
                         [w | (u, w) <- graph, u == v]

graphDegree :: Graph -> Vertex -> Int
graphDegree graph v = length (graphNeighbors graph v)

-- 图示例
graphExample :: IO ()
graphExample = do
  let -- 构造图
      emptyGraph = []
      simpleGraph = [(1, 2), (2, 3), (3, 1), (1, 4)]
      
      -- 图操作
      vertices = graphVertices simpleGraph
      edges = graphEdges simpleGraph
      neighbors1 = graphNeighbors simpleGraph 1
      degree1 = graphDegree simpleGraph 1
  putStrLn $ "Graph: " ++ show simpleGraph
  putStrLn $ "Vertices: " ++ show vertices
  putStrLn $ "Edges: " ++ show edges
  putStrLn $ "Neighbors of 1: " ++ show neighbors1
  putStrLn $ "Degree of 1: " ++ show degree1
```

### 6.2 图遍历

**定义 6.2 (图遍历)**
图遍历包括深度优先搜索和广度优先搜索。

**Haskell实现：**

```haskell
-- 深度优先搜索
dfs :: Graph -> Vertex -> [Vertex]
dfs graph start = dfsHelper start []
  where
    dfsHelper current visited
      | current `elem` visited = visited
      | otherwise = 
          let neighbors = graphNeighbors graph current
              newVisited = current : visited
          in foldr (\neighbor acc -> dfsHelper neighbor acc) newVisited neighbors

-- 广度优先搜索
bfs :: Graph -> Vertex -> [Vertex]
bfs graph start = bfsHelper [start] []
  where
    bfsHelper [] visited = reverse visited
    bfsHelper (current:queue) visited
      | current `elem` visited = bfsHelper queue visited
      | otherwise = 
          let neighbors = graphNeighbors graph current
              newVisited = current : visited
              newQueue = queue ++ neighbors
          in bfsHelper newQueue newVisited

-- 图遍历示例
graphTraversalExample :: IO ()
graphTraversalExample = do
  let testGraph = [(1, 2), (1, 3), (2, 4), (2, 5), (3, 6), (3, 7)]
      dfsResult = dfs testGraph 1
      bfsResult = bfs testGraph 1
  putStrLn $ "Test graph: " ++ show testGraph
  putStrLn $ "DFS from 1: " ++ show dfsResult
  putStrLn $ "BFS from 1: " ++ show bfsResult
```

## 🛠️ 7. 哈希表

### 7.1 哈希表实现

**定义 7.1 (哈希表)**
哈希表是基于键值对的数据结构，提供快速的查找、插入和删除操作。

**Haskell实现：**

```haskell
-- 哈希表数据类型
type HashTable k v = [(k, v)]

-- 哈希表操作
htEmpty :: HashTable k v
htEmpty = []

htInsert :: Eq k => k -> v -> HashTable k v -> HashTable k v
htInsert key value table = (key, value) : filter ((/= key) . fst) table

htLookup :: Eq k => k -> HashTable k v -> Maybe v
htLookup key = lookup key

htDelete :: Eq k => k -> HashTable k v -> HashTable k v
htDelete key = filter ((/= key) . fst)

htKeys :: HashTable k v -> [k]
htKeys = map fst

htValues :: HashTable k v -> [v]
htValues = map snd

-- 哈希表示例
hashTableExample :: IO ()
hashTableExample = do
  let -- 构造哈希表
      emptyHT = htEmpty
      ht1 = htInsert "Alice" 25 emptyHT
      ht2 = htInsert "Bob" 30 ht1
      ht3 = htInsert "Charlie" 35 ht2
      
      -- 哈希表操作
      lookupAlice = htLookup "Alice" ht3
      lookupDavid = htLookup "David" ht3
      keys = htKeys ht3
      values = htValues ht3
      ht4 = htDelete "Bob" ht3
  putStrLn $ "Hash table: " ++ show ht3
  putStrLn $ "Lookup Alice: " ++ show lookupAlice
  putStrLn $ "Lookup David: " ++ show lookupDavid
  putStrLn $ "Keys: " ++ show keys
  putStrLn $ "Values: " ++ show values
  putStrLn $ "After deleting Bob: " ++ show ht4
```

### 7.2 哈希表应用

**定义 7.2 (哈希表应用)**
哈希表在缓存、计数等场景中有重要应用。

**Haskell实现：**

```haskell
-- 词频统计
wordFrequency :: String -> HashTable String Int
wordFrequency text = 
  let words = map (map toLower) (words text)
  in foldr (\word table -> 
             htInsert word (1 + maybe 0 id (htLookup word table)) table) 
           htEmpty words

-- 缓存实现
type Cache k v = HashTable k v

cacheLookup :: Eq k => k -> Cache k v -> Maybe v
cacheLookup = htLookup

cacheInsert :: Eq k => k -> v -> Cache k v -> Cache k v
cacheInsert = htInsert

-- 哈希表应用示例
hashTableApplicationExample :: IO ()
hashTableApplicationExample = do
  let -- 词频统计
      text = "hello world hello haskell world"
      frequency = wordFrequency text
      
      -- 缓存
      emptyCache = htEmpty
      cache1 = cacheInsert "key1" "value1" emptyCache
      cache2 = cacheInsert "key2" "value2" cache1
      lookupResult = cacheLookup "key1" cache2
  putStrLn $ "Text: " ++ show text
  putStrLn $ "Word frequency: " ++ show frequency
  putStrLn $ "Cache: " ++ show cache2
  putStrLn $ "Cache lookup: " ++ show lookupResult
```

## 📊 8. 性能分析

### 8.1 时间复杂度

**定义 8.1 (时间复杂度)**
不同数据结构操作的时间复杂度分析。

**Haskell实现：**

```haskell
-- 性能测试函数
performanceTest :: IO ()
performanceTest = do
  let -- 列表操作性能
      largeList = [1..10000]
      listSearch = elem 5000 largeList
      listInsert = 0 : largeList
      
      -- 树操作性能
      largeTree = foldr btInsert BEmpty [1..1000]
      treeSearch = btSearch 500 largeTree
      
      -- 哈希表操作性能
      largeHT = foldr (\i ht -> htInsert (show i) i ht) htEmpty [1..1000]
      htLookup = htLookup "500" largeHT
  putStrLn "Performance test completed!"
  putStrLn "List search: O(n)"
  putStrLn "Tree search: O(log n)"
  putStrLn "Hash table lookup: O(1) average"
```

### 8.2 空间复杂度

**定义 8.2 (空间复杂度)**
不同数据结构的空间使用分析。

**Haskell实现：**

```haskell
-- 空间复杂度分析
spaceComplexityAnalysis :: IO ()
spaceComplexityAnalysis = do
  let -- 空间使用分析
      listSpace = length [1..1000]  -- O(n)
      treeSpace = btSize (foldr btInsert BEmpty [1..1000])  -- O(n)
      hashTableSpace = length (htKeys (foldr (\i ht -> htInsert (show i) i ht) htEmpty [1..1000]))  -- O(n)
  putStrLn "Space complexity analysis:"
  putStrLn "List: O(n)"
  putStrLn "Tree: O(n)"
  putStrLn "Hash table: O(n)"
```

## 🔗 9. 数据结构选择

### 9.1 选择指南

**定理 9.1 (数据结构选择)**
根据具体需求选择合适的数据结构。

**Haskell实现：**

```haskell
-- 数据结构选择指南
dataStructureGuide :: IO ()
dataStructureGuide = do
  putStrLn "Data Structure Selection Guide:"
  putStrLn "1. Lists: Sequential access, simple operations"
  putStrLn "2. Stacks: LIFO operations, function calls"
  putStrLn "3. Queues: FIFO operations, task scheduling"
  putStrLn "4. Trees: Hierarchical data, search operations"
  putStrLn "5. Heaps: Priority queues, sorting"
  putStrLn "6. Graphs: Network relationships, path finding"
  putStrLn "7. Hash Tables: Key-value storage, fast lookup"
```

### 9.2 实际应用场景

**定义 9.2 (应用场景)**
不同数据结构在实际应用中的使用场景。

**Haskell实现：**

```haskell
-- 实际应用场景
applicationScenarios :: IO ()
applicationScenarios = do
  putStrLn "Real-world Application Scenarios:"
  putStrLn "1. Lists: File processing, data streams"
  putStrLn "2. Stacks: Expression evaluation, undo operations"
  putStrLn "3. Queues: Task scheduling, event processing"
  putStrLn "4. Trees: File systems, XML parsing"
  putStrLn "5. Heaps: Priority scheduling, graph algorithms"
  putStrLn "6. Graphs: Social networks, routing algorithms"
  putStrLn "7. Hash Tables: Caching, database indexing"
```

## 📚 10. 总结与展望

### 10.1 数据结构的核心概念

1. **抽象数据类型**：接口与实现分离
2. **不可变性**：函数式数据结构的特点
3. **类型安全**：编译时类型检查
4. **性能优化**：时间空间复杂度分析

### 10.2 数据结构的优势

1. **类型安全**：编译时错误检查
2. **不可变性**：避免副作用
3. **组合性**：易于组合和扩展
4. **表达力**：直观的数据表示

### 10.3 未来发展方向

1. **持久化数据结构**：高效的不可变数据结构
2. **并行数据结构**：支持并发访问
3. **类型级数据结构**：编译时数据结构
4. **领域特定数据结构**：针对特定应用优化

---

**相关文档**：

- [函数式编程基础](../01-Basic-Concepts/001-Functional-Programming-Foundation.md)
- [递归和列表](../01-Basic-Concepts/003-Recursion-and-Lists.md)
- [类型系统基础](../04-Type-System/001-Type-System-Foundation.md)
- [高级数据结构](./002-Advanced-Data-Structures.md)

**实现示例**：

- [算法实现](../07-Algorithms/001-Sorting-Algorithms.md)
- [性能优化](../09-Performance/001-Performance-Analysis.md)
- [Web开发](../11-Web-Development/001-Web-Development-Foundation.md)
