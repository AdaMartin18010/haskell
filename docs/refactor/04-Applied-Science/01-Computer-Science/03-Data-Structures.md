# 数据结构

## 概述

数据结构是组织和存储数据的方式，是算法设计的基础。本文档从形式化角度探讨各种数据结构的定义、实现和分析。

## 1. 基本数据结构

### 1.1 线性数据结构

线性数据结构按顺序组织数据。

```haskell
-- 线性数据结构
data LinearStructure = 
  Array | List | Stack | Queue | Deque

-- 数组
data Array a = Array
  { arrayElements :: [a]
  , arraySize :: Int
  , arrayCapacity :: Int
  }

-- 创建数组
createArray :: Int -> a -> Array a
createArray size defaultValue = 
  Array {
    arrayElements = replicate size defaultValue,
    arraySize = size,
    arrayCapacity = size
  }

-- 数组访问
arrayAccess :: Array a -> Int -> Maybe a
arrayAccess array index = 
  if index >= 0 && index < arraySize array
  then Just (arrayElements array !! index)
  else Nothing

-- 数组更新
arrayUpdate :: Array a -> Int -> a -> Array a
arrayUpdate array index value = 
  if index >= 0 && index < arraySize array
  then array { arrayElements = updateList (arrayElements array) index value }
  else array

-- 链表
data LinkedList a = 
  Empty
  | Node a (LinkedList a)

-- 链表操作
listCons :: a -> LinkedList a -> LinkedList a
listCons x xs = Node x xs

listHead :: LinkedList a -> Maybe a
listHead Empty = Nothing
listHead (Node x _) = Just x

listTail :: LinkedList a -> Maybe (LinkedList a)
listTail Empty = Nothing
listTail (Node _ xs) = Just xs

-- 栈
data Stack a = Stack
  { stackElements :: [a]
  , stackSize :: Int
  }

-- 栈操作
emptyStack :: Stack a
emptyStack = Stack [] 0

push :: a -> Stack a -> Stack a
push x stack = 
  Stack {
    stackElements = x : stackElements stack,
    stackSize = stackSize stack + 1
  }

pop :: Stack a -> Maybe (a, Stack a)
pop stack = 
  case stackElements stack of
    [] -> Nothing
    (x:xs) -> Just (x, Stack xs (stackSize stack - 1))

peek :: Stack a -> Maybe a
peek stack = 
  case stackElements stack of
    [] -> Nothing
    (x:_) -> Just x

-- 队列
data Queue a = Queue
  { queueElements :: [a]
  , queueSize :: Int
  }

-- 队列操作
emptyQueue :: Queue a
emptyQueue = Queue [] 0

enqueue :: a -> Queue a -> Queue a
enqueue x queue = 
  Queue {
    queueElements = queueElements queue ++ [x],
    queueSize = queueSize queue + 1
  }

dequeue :: Queue a -> Maybe (a, Queue a)
dequeue queue = 
  case queueElements queue of
    [] -> Nothing
    (x:xs) -> Just (x, Queue xs (queueSize queue - 1))

front :: Queue a -> Maybe a
front queue = 
  case queueElements queue of
    [] -> Nothing
    (x:_) -> Just x
```

### 1.2 树形数据结构

树形数据结构具有层次关系。

```haskell
-- 二叉树
data BinaryTree a = 
  Empty
  | Node a (BinaryTree a) (BinaryTree a)

-- 二叉树操作
emptyTree :: BinaryTree a
emptyTree = Empty

insert :: Ord a => a -> BinaryTree a -> BinaryTree a
insert x Empty = Node x Empty Empty
insert x (Node value left right) = 
  if x <= value
  then Node value (insert x left) right
  else Node value left (insert x right)

search :: Ord a => a -> BinaryTree a -> Bool
search _ Empty = False
search x (Node value left right) = 
  if x == value
  then True
  else if x < value
       then search x left
       else search x right

-- 二叉搜索树
data BinarySearchTree a = BinarySearchTree
  { treeRoot :: BinaryTree a
  , treeSize :: Int
  }

-- 创建二叉搜索树
createBST :: BinarySearchTree a
createBST = BinarySearchTree Empty 0

-- 插入到BST
bstInsert :: Ord a => a -> BinarySearchTree a -> BinarySearchTree a
bstInsert x bst = 
  BinarySearchTree {
    treeRoot = insert x (treeRoot bst),
    treeSize = treeSize bst + 1
  }

-- 在BST中搜索
bstSearch :: Ord a => a -> BinarySearchTree a -> Bool
bstSearch x bst = search x (treeRoot bst)

-- 树遍历
data TraversalOrder = 
  PreOrder | InOrder | PostOrder | LevelOrder

-- 前序遍历
preorder :: BinaryTree a -> [a]
preorder Empty = []
preorder (Node value left right) = 
  value : preorder left ++ preorder right

-- 中序遍历
inorder :: BinaryTree a -> [a]
inorder Empty = []
inorder (Node value left right) = 
  inorder left ++ [value] ++ inorder right

-- 后序遍历
postorder :: BinaryTree a -> [a]
postorder Empty = []
postorder (Node value left right) = 
  postorder left ++ postorder right ++ [value]

-- 层序遍历
levelorder :: BinaryTree a -> [a]
levelorder tree = 
  let levels = levelorderHelper [tree]
  in concat levels

-- 层序遍历辅助函数
levelorderHelper :: [BinaryTree a] -> [[a]]
levelorderHelper [] = []
levelorderHelper trees = 
  let currentLevel = [value | Node value _ _ <- trees]
      nextLevel = concat [[left, right] | Node _ left right <- trees, 
                                         left /= Empty || right /= Empty]
  in currentLevel : levelorderHelper nextLevel
```

### 1.3 图数据结构

图数据结构表示对象之间的关系。

```haskell
-- 图
data Graph a = Graph
  { graphVertices :: [a]
  , graphEdges :: [(a, a)]
  , graphAdjacencyList :: [(a, [a])]
  }

-- 创建图
createGraph :: [a] -> [(a, a)] -> Graph a
createGraph vertices edges = 
  let adjacencyList = [(v, [u | (u, w) <- edges, v == u || v == w]) | v <- vertices]
  in Graph {
    graphVertices = vertices,
    graphEdges = edges,
    graphAdjacencyList = adjacencyList
  }

-- 添加顶点
addVertex :: a -> Graph a -> Graph a
addVertex v graph = 
  Graph {
    graphVertices = v : graphVertices graph,
    graphEdges = graphEdges graph,
    graphAdjacencyList = (v, []) : graphAdjacencyList graph
  }

-- 添加边
addEdge :: (a, a) -> Graph a -> Graph a
addEdge (u, v) graph = 
  let newEdges = (u, v) : graphEdges graph
      newAdjacencyList = updateAdjacencyList graph u v
  in Graph {
    graphVertices = graphVertices graph,
    graphEdges = newEdges,
    graphAdjacencyList = newAdjacencyList
  }

-- 更新邻接表
updateAdjacencyList :: Graph a -> a -> a -> [(a, [a])]
updateAdjacencyList graph u v = 
  let adjacencyList = graphAdjacencyList graph
      updateForVertex vertex neighbor = 
        case lookup vertex adjacencyList of
          Just neighbors -> (vertex, neighbor : neighbors)
          Nothing -> (vertex, [neighbor])
  in updateForVertex u v : updateForVertex v u : 
     filter (\(vertex, _) -> vertex /= u && vertex /= v) adjacencyList

-- 获取邻居
getNeighbors :: Eq a => Graph a -> a -> [a]
getNeighbors graph vertex = 
  case lookup vertex (graphAdjacencyList graph) of
    Just neighbors -> neighbors
    Nothing -> []

-- 图的度
vertexDegree :: Eq a => Graph a -> a -> Int
vertexDegree graph vertex = 
  length (getNeighbors graph vertex)

-- 图是否连通
isConnected :: Eq a => Graph a -> Bool
isConnected graph = 
  let vertices = graphVertices graph
      startVertex = head vertices
      reachable = dfs graph startVertex []
  in length reachable == length vertices

-- 深度优先搜索
dfs :: Eq a => Graph a -> a -> [a] -> [a]
dfs graph vertex visited = 
  if vertex `elem` visited
  then visited
  else 
    let newVisited = vertex : visited
        neighbors = getNeighbors graph vertex
    in foldl (\vis neighbor -> dfs graph neighbor vis) newVisited neighbors
```

## 2. 高级数据结构

### 2.1 堆

堆是一种特殊的树形数据结构。

```haskell
-- 堆
data Heap a = Heap
  { heapElements :: [a]
  , heapSize :: Int
  , heapType :: HeapType
  }

-- 堆类型
data HeapType = 
  MinHeap | MaxHeap

-- 创建最小堆
createMinHeap :: Ord a => Heap a
createMinHeap = Heap [] 0 MinHeap

-- 创建最大堆
createMaxHeap :: Ord a => Heap a
createMaxHeap = Heap [] 0 MaxHeap

-- 插入堆
heapInsert :: Ord a => a -> Heap a -> Heap a
heapInsert x heap = 
  let newElements = x : heapElements heap
      newSize = heapSize heap + 1
      heapified = heapifyUp newElements newSize (heapType heap)
  in Heap {
    heapElements = heapified,
    heapSize = newSize,
    heapType = heapType heap
  }

-- 向上堆化
heapifyUp :: Ord a => [a] -> Int -> HeapType -> [a]
heapifyUp elements size heapType = 
  let currentIndex = size - 1
      parentIndex = (currentIndex - 1) `div` 2
  in if currentIndex == 0
     then elements
     else 
       let current = elements !! currentIndex
           parent = elements !! parentIndex
           shouldSwap = case heapType of
                          MinHeap -> current < parent
                          MaxHeap -> current > parent
       in if shouldSwap
          then heapifyUp (swapElements elements currentIndex parentIndex) size heapType
          else elements

-- 交换元素
swapElements :: [a] -> Int -> Int -> [a]
swapElements elements i j = 
  let elementI = elements !! i
      elementJ = elements !! j
  in updateList (updateList elements i elementJ) j elementI

-- 提取堆顶
heapExtract :: Ord a => Heap a -> Maybe (a, Heap a)
heapExtract heap = 
  if heapSize heap == 0
  then Nothing
  else 
    let root = head (heapElements heap)
        lastElement = last (heapElements heap)
        newElements = lastElement : tail (init (heapElements heap))
        newSize = heapSize heap - 1
        heapified = heapifyDown newElements newSize (heapType heap)
    in Just (root, Heap {
      heapElements = heapified,
      heapSize = newSize,
      heapType = heapType heap
    })

-- 向下堆化
heapifyDown :: Ord a => [a] -> Int -> HeapType -> [a]
heapifyDown elements size heapType = 
  heapifyDownHelper elements 0 size heapType

-- 向下堆化辅助函数
heapifyDownHelper :: Ord a => [a] -> Int -> Int -> HeapType -> [a]
heapifyDownHelper elements index size heapType = 
  let leftChild = 2 * index + 1
      rightChild = 2 * index + 2
      largest = index
      largest = if leftChild < size && shouldSwap (elements !! leftChild) (elements !! largest) heapType
                then leftChild
                else largest
      largest = if rightChild < size && shouldSwap (elements !! rightChild) (elements !! largest) heapType
                then rightChild
                else largest
  in if largest /= index
     then heapifyDownHelper (swapElements elements index largest) largest size heapType
     else elements

-- 判断是否应该交换
shouldSwap :: Ord a => a -> a -> HeapType -> Bool
shouldSwap child parent heapType = case heapType of
  MinHeap -> child < parent
  MaxHeap -> child > parent

-- 堆排序
heapSort :: Ord a => [a] -> [a]
heapSort elements = 
  let heap = foldl (flip heapInsert) createMaxHeap elements
      sorted = heapSortHelper heap []
  in sorted

-- 堆排序辅助函数
heapSortHelper :: Ord a => Heap a -> [a] -> [a]
heapSortHelper heap sorted = 
  case heapExtract heap of
    Nothing -> sorted
    Just (element, newHeap) -> heapSortHelper newHeap (element : sorted)
```

### 2.2 散列表

散列表提供快速的数据访问。

```haskell
-- 散列表
data HashTable k v = HashTable
  { tableBuckets :: [[(k, v)]]
  , tableSize :: Int
  , tableLoadFactor :: Double
  }

-- 创建散列表
createHashTable :: Int -> HashTable k v
createHashTable size = 
  HashTable {
    tableBuckets = replicate size [],
    tableSize = size,
    tableLoadFactor = 0.0
  }

-- 散列函数
hashFunction :: (Hashable k) => k -> Int -> Int
hashFunction key size = 
  let hash = hash key
  in hash `mod` size

-- 散列类型类
class Hashable a where
  hash :: a -> Int

-- 整数散列
instance Hashable Int where
  hash x = x

-- 字符串散列
instance Hashable String where
  hash s = foldl (\acc c -> acc * 31 + fromEnum c) 0 s

-- 插入散列表
hashInsert :: (Hashable k, Eq k) => k -> v -> HashTable k v -> HashTable k v
hashInsert key value table = 
  let index = hashFunction key (tableSize table)
      buckets = tableBuckets table
      bucket = buckets !! index
      newBucket = updateBucket bucket key value
      newBuckets = updateList buckets index newBucket
      newLoadFactor = fromIntegral (countEntries newBuckets) / fromIntegral (tableSize table)
  in HashTable {
    tableBuckets = newBuckets,
    tableSize = tableSize table,
    tableLoadFactor = newLoadFactor
  }

-- 更新桶
updateBucket :: Eq k => [(k, v)] -> k -> v -> [(k, v)]
updateBucket [] key value = [(key, value)]
updateBucket ((k, v):pairs) key value = 
  if k == key
  then (key, value) : pairs
  else (k, v) : updateBucket pairs key value

-- 计算条目数
countEntries :: [[(k, v)]] -> Int
countEntries buckets = 
  sum (map length buckets)

-- 查找散列表
hashLookup :: (Hashable k, Eq k) => k -> HashTable k v -> Maybe v
hashLookup key table = 
  let index = hashFunction key (tableSize table)
      bucket = tableBuckets table !! index
  in lookup key bucket

-- 删除散列表
hashDelete :: (Hashable k, Eq k) => k -> HashTable k v -> HashTable k v
hashDelete key table = 
  let index = hashFunction key (tableSize table)
      buckets = tableBuckets table
      bucket = buckets !! index
      newBucket = filter (\(k, _) -> k /= key) bucket
      newBuckets = updateList buckets index newBucket
      newLoadFactor = fromIntegral (countEntries newBuckets) / fromIntegral (tableSize table)
  in HashTable {
    tableBuckets = newBuckets,
    tableSize = tableSize table,
    tableLoadFactor = newLoadFactor
  }

-- 重新散列
rehash :: (Hashable k, Eq k) => HashTable k v -> HashTable k v
rehash table = 
  let newSize = tableSize table * 2
      newTable = createHashTable newSize
      allEntries = concat (tableBuckets table)
  in foldl (\t (k, v) -> hashInsert k v t) newTable allEntries
```

### 2.3 平衡树

平衡树保持树的平衡性以提高性能。

```haskell
-- AVL树
data AVLTree a = 
  AVLEmpty
  | AVLNode a (AVLTree a) (AVLTree a) Int

-- 创建AVL树
createAVLTree :: AVLTree a
createAVLTree = AVLEmpty

-- 获取高度
avlHeight :: AVLTree a -> Int
avlHeight AVLEmpty = 0
avlHeight (AVLNode _ _ _ height) = height

-- 获取平衡因子
avlBalanceFactor :: AVLTree a -> Int
avlBalanceFactor AVLEmpty = 0
avlBalanceFactor (AVLNode _ left right _) = 
  avlHeight left - avlHeight right

-- 右旋转
avlRightRotate :: AVLTree a -> AVLTree a
avlRightRotate (AVLNode value left right _) = 
  case left of
    AVLEmpty -> AVLNode value left right 1
    (AVLNode leftValue leftLeft leftRight _) -> 
      let newRight = AVLNode value leftRight right 1
          newHeight = max (avlHeight leftLeft) (avlHeight newRight) + 1
      in AVLNode leftValue leftLeft newRight newHeight

-- 左旋转
avlLeftRotate :: AVLTree a -> AVLTree a
avlLeftRotate (AVLNode value left right _) = 
  case right of
    AVLEmpty -> AVLNode value left right 1
    (AVLNode rightValue rightLeft rightRight _) -> 
      let newLeft = AVLNode value left rightLeft 1
          newHeight = max (avlHeight newLeft) (avlHeight rightRight) + 1
      in AVLNode rightValue newLeft rightRight newHeight

-- 插入AVL树
avlInsert :: Ord a => a -> AVLTree a -> AVLTree a
avlInsert x AVLEmpty = AVLNode x AVLEmpty AVLEmpty 1
avlInsert x (AVLNode value left right height) = 
  let newTree = if x <= value
                then AVLNode value (avlInsert x left) right height
                else AVLNode value left (avlInsert x right) height
      balancedTree = avlBalance newTree
  in balancedTree

-- 平衡AVL树
avlBalance :: AVLTree a -> AVLTree a
avlBalance tree = 
  let balanceFactor = avlBalanceFactor tree
  in if balanceFactor > 1
     then 
       case tree of
         (AVLNode value left right height) -> 
           if avlBalanceFactor left < 0
           then avlRightRotate (AVLNode value (avlLeftRotate left) right height)
           else avlRightRotate tree
     else if balanceFactor < -1
          then 
            case tree of
              (AVLNode value left right height) -> 
                if avlBalanceFactor right > 0
                then avlLeftRotate (AVLNode value left (avlRightRotate right) height)
                else avlLeftRotate tree
          else tree

-- 红黑树
data Color = Red | Black

data RedBlackTree a = 
  RBEmpty
  | RBNode Color a (RedBlackTree a) (RedBlackTree a)

-- 创建红黑树
createRedBlackTree :: RedBlackTree a
createRedBlackTree = RBEmpty

-- 插入红黑树
rbInsert :: Ord a => a -> RedBlackTree a -> RedBlackTree a
rbInsert x tree = 
  let insertedTree = rbInsertHelper x tree
  in rbFixInsert insertedTree

-- 红黑树插入辅助函数
rbInsertHelper :: Ord a => a -> RedBlackTree a -> RedBlackTree a
rbInsertHelper x RBEmpty = RBNode Red x RBEmpty RBEmpty
rbInsertHelper x (RBNode color value left right) = 
  if x <= value
  then RBNode color value (rbInsertHelper x left) right
  else RBNode color value left (rbInsertHelper x right)

-- 修复红黑树插入
rbFixInsert :: RedBlackTree a -> RedBlackTree a
rbFixInsert tree = 
  case tree of
    RBEmpty -> RBEmpty
    (RBNode Red value left right) -> 
      let fixedTree = rbFixInsertHelper tree
      in case fixedTree of
           (RBNode _ value' left' right') -> RBNode Black value' left' right'
    _ -> tree

-- 红黑树插入修复辅助函数
rbFixInsertHelper :: RedBlackTree a -> RedBlackTree a
rbFixInsertHelper tree = 
  -- 简化实现，实际需要复杂的修复逻辑
  tree
```

## 3. 数据结构分析

### 3.1 性能分析

分析数据结构的性能特征。

```haskell
-- 数据结构性能
data DataStructurePerformance = DataStructurePerformance
  { accessTime :: TimeComplexity
  , searchTime :: TimeComplexity
  , insertTime :: TimeComplexity
  , deleteTime :: TimeComplexity
  , spaceComplexity :: SpaceComplexity
  }

-- 时间复杂度
data TimeComplexity = TimeComplexity
  { complexityFunction :: Int -> Int
  , complexityClass :: ComplexityClass
  }

-- 复杂性类
data ComplexityClass = 
  Constant | Logarithmic | Linear | Linearithmic | Quadratic | Cubic

-- 空间复杂度
data SpaceComplexity = SpaceComplexity
  { spaceFunction :: Int -> Int
  , spaceClass :: ComplexityClass
  }

-- 分析数组性能
analyzeArrayPerformance :: DataStructurePerformance
analyzeArrayPerformance = 
  DataStructurePerformance {
    accessTime = TimeComplexity (\n -> 1) Constant,
    searchTime = TimeComplexity (\n -> n) Linear,
    insertTime = TimeComplexity (\n -> n) Linear,
    deleteTime = TimeComplexity (\n -> n) Linear,
    spaceComplexity = SpaceComplexity (\n -> n) Linear
  }

-- 分析链表性能
analyzeLinkedListPerformance :: DataStructurePerformance
analyzeLinkedListPerformance = 
  DataStructurePerformance {
    accessTime = TimeComplexity (\n -> n) Linear,
    searchTime = TimeComplexity (\n -> n) Linear,
    insertTime = TimeComplexity (\n -> 1) Constant,
    deleteTime = TimeComplexity (\n -> n) Linear,
    spaceComplexity = SpaceComplexity (\n -> n) Linear
  }

-- 分析二叉搜索树性能
analyzeBSTPerformance :: DataStructurePerformance
analyzeBSTPerformance = 
  DataStructurePerformance {
    accessTime = TimeComplexity (\n -> floor (log (fromIntegral n))) Logarithmic,
    searchTime = TimeComplexity (\n -> floor (log (fromIntegral n))) Logarithmic,
    insertTime = TimeComplexity (\n -> floor (log (fromIntegral n))) Logarithmic,
    deleteTime = TimeComplexity (\n -> floor (log (fromIntegral n))) Logarithmic,
    spaceComplexity = SpaceComplexity (\n -> n) Linear
  }

-- 分析散列表性能
analyzeHashTablePerformance :: DataStructurePerformance
analyzeHashTablePerformance = 
  DataStructurePerformance {
    accessTime = TimeComplexity (\n -> 1) Constant,
    searchTime = TimeComplexity (\n -> 1) Constant,
    insertTime = TimeComplexity (\n -> 1) Constant,
    deleteTime = TimeComplexity (\n -> 1) Constant,
    spaceComplexity = SpaceComplexity (\n -> n) Linear
  }
```

### 3.2 选择指南

为不同应用场景选择合适的数据结构。

```haskell
-- 应用场景
data ApplicationScenario = 
  FrequentAccess | FrequentSearch | FrequentInsert | FrequentDelete | MemoryEfficient

-- 数据结构选择
selectDataStructure :: ApplicationScenario -> String
selectDataStructure scenario = case scenario of
  FrequentAccess -> "Array or Hash Table"
  FrequentSearch -> "Hash Table or Binary Search Tree"
  FrequentInsert -> "Linked List or Hash Table"
  FrequentDelete -> "Linked List or Hash Table"
  MemoryEfficient -> "Array or Compact Data Structures"

-- 数据结构比较
data StructureComparison = StructureComparison
  { structure1 :: String
  , structure2 :: String
  , comparisonMetrics :: [ComparisonMetric]
  }

-- 比较指标
data ComparisonMetric = ComparisonMetric
  { metricName :: String
  , structure1Value :: String
  , structure2Value :: String
  , winner :: String
  }

-- 比较数组和链表
compareArrayLinkedList :: StructureComparison
compareArrayLinkedList = 
  StructureComparison {
    structure1 = "Array",
    structure2 = "Linked List",
    comparisonMetrics = [
      ComparisonMetric "Access Time" "O(1)" "O(n)" "Array",
      ComparisonMetric "Insert Time" "O(n)" "O(1)" "Linked List",
      ComparisonMetric "Memory Usage" "Contiguous" "Scattered" "Array",
      ComparisonMetric "Cache Performance" "Good" "Poor" "Array"
    ]
  }

-- 比较BST和散列表
compareBSTHashTable :: StructureComparison
compareBSTHashTable = 
  StructureComparison {
    structure1 = "Binary Search Tree",
    structure2 = "Hash Table",
    comparisonMetrics = [
      ComparisonMetric "Search Time" "O(log n)" "O(1)" "Hash Table",
      ComparisonMetric "Ordered Operations" "Yes" "No" "Binary Search Tree",
      ComparisonMetric "Memory Overhead" "Low" "High" "Binary Search Tree",
      ComparisonMetric "Worst Case" "O(n)" "O(n)" "Equal"
    ]
  }
```

## 总结

数据结构为组织和存储数据提供了系统的方法。通过形式化方法，我们可以：

1. **精确建模**：用数学结构精确描述数据结构
2. **性能分析**：分析各种操作的复杂度
3. **算法设计**：为算法提供合适的数据结构基础
4. **应用指导**：为不同场景选择最优的数据结构

数据结构的研究将继续推动我们对数据组织的理解，并为高效算法设计提供基础。 