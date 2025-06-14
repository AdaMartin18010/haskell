# 基础数据结构

## 📋 概述

基础数据结构是计算机科学的核心概念，包括数组、链表、栈、队列、树等。在Haskell中，这些数据结构通常以不可变的形式实现，利用函数式编程的特性提供类型安全和高效的操作。

## 🎯 核心概念

### 数据结构分类

```haskell
-- 数据结构类型
data DataStructureType = 
    LinearStructure
  | HierarchicalStructure
  | GraphStructure
  | SetStructure
  deriving (Eq, Show)

-- 线性结构
data LinearStructure = 
    Array
  | List
  | Stack
  | Queue
  | Deque
  deriving (Eq, Show)

-- 层次结构
data HierarchicalStructure = 
    Tree
  | BinaryTree
  | AVLTree
  | RedBlackTree
  | BTree
  deriving (Eq, Show)

-- 图结构
data GraphStructure = 
    DirectedGraph
  | UndirectedGraph
  | WeightedGraph
  | DAG
  deriving (Eq, Show)

-- 集合结构
data SetStructure = 
    Set
  | Map
  | HashTable
  | BloomFilter
  deriving (Eq, Show)
```

### 操作接口

```haskell
-- 基本操作接口
class DataStructure ds where
  type Element ds
  empty :: ds
  isEmpty :: ds -> Bool
  size :: ds -> Int

-- 线性结构操作
class LinearStructure ds => LinearDataStructure ds where
  insert :: Element ds -> ds -> ds
  delete :: Element ds -> ds -> ds
  search :: Element ds -> ds -> Bool
  access :: Int -> ds -> Maybe (Element ds)

-- 栈操作
class Stack ds where
  push :: Element ds -> ds -> ds
  pop :: ds -> Maybe (Element ds, ds)
  top :: ds -> Maybe (Element ds)
  peek :: ds -> Maybe (Element ds)

-- 队列操作
class Queue ds where
  enqueue :: Element ds -> ds -> ds
  dequeue :: ds -> Maybe (Element ds, ds)
  front :: ds -> Maybe (Element ds)
  rear :: ds -> Maybe (Element ds)
```

## 🔧 实现

### 列表（List）

```haskell
-- 列表实现
data List a = 
    Nil
  | Cons a (List a)
  deriving (Eq, Show)

-- 列表实例
instance DataStructure List where
  type Element List = a
  empty = Nil
  isEmpty Nil = True
  isEmpty _ = False
  size = length

-- 列表操作
length :: List a -> Int
length Nil = 0
length (Cons _ xs) = 1 + length xs

head :: List a -> Maybe a
head Nil = Nothing
head (Cons x _) = Just x

tail :: List a -> Maybe (List a)
tail Nil = Nothing
tail (Cons _ xs) = Just xs

-- 列表连接
append :: List a -> List a -> List a
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

-- 列表反转
reverse :: List a -> List a
reverse = reverseAcc Nil
  where
    reverseAcc acc Nil = acc
    reverseAcc acc (Cons x xs) = reverseAcc (Cons x acc) xs

-- 列表映射
map :: (a -> b) -> List a -> List b
map _ Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

-- 列表过滤
filter :: (a -> Bool) -> List a -> List a
filter _ Nil = Nil
filter p (Cons x xs)
  | p x       = Cons x (filter p xs)
  | otherwise = filter p xs

-- 列表折叠
foldr :: (a -> b -> b) -> b -> List a -> b
foldr _ z Nil = z
foldr f z (Cons x xs) = f x (foldr f z xs)

foldl :: (b -> a -> b) -> b -> List a -> b
foldl _ z Nil = z
foldl f z (Cons x xs) = foldl f (f z x) xs
```

### 栈（Stack）

```haskell
-- 栈实现
data Stack a = Stack
  { elements :: List a
  } deriving (Eq, Show)

-- 栈实例
instance DataStructure Stack where
  type Element Stack = a
  empty = Stack Nil
  isEmpty (Stack Nil) = True
  isEmpty _ = False
  size (Stack xs) = length xs

instance Stack Stack where
  push x (Stack xs) = Stack (Cons x xs)
  
  pop (Stack Nil) = Nothing
  pop (Stack (Cons x xs)) = Just (x, Stack xs)
  
  top (Stack Nil) = Nothing
  top (Stack (Cons x _)) = Just x
  
  peek = top

-- 栈操作示例
stackExample :: Stack Int
stackExample = 
  empty
  |> push 1
  |> push 2
  |> push 3

-- 栈应用：括号匹配
bracketMatching :: String -> Bool
bracketMatching = bracketMatchingAcc empty
  where
    bracketMatchingAcc :: Stack Char -> String -> Bool
    bracketMatchingAcc _ [] = isEmpty stack
    bracketMatchingAcc stack (c:cs)
      | c == '(' || c == '[' || c == '{' = 
          bracketMatchingAcc (push c stack) cs
      | c == ')' = 
          case pop stack of
            Just ('(', newStack) -> bracketMatchingAcc newStack cs
            _ -> False
      | c == ']' = 
          case pop stack of
            Just ('[', newStack) -> bracketMatchingAcc newStack cs
            _ -> False
      | c == '}' = 
          case pop stack of
            Just ('{', newStack) -> bracketMatchingAcc newStack cs
            _ -> False
      | otherwise = bracketMatchingAcc stack cs
```

### 队列（Queue）

```haskell
-- 队列实现（使用两个列表）
data Queue a = Queue
  { front :: List a
  , rear :: List a
  } deriving (Eq, Show)

-- 队列实例
instance DataStructure Queue where
  type Element Queue = a
  empty = Queue Nil Nil
  isEmpty (Queue Nil Nil) = True
  isEmpty _ = False
  size (Queue front rear) = length front + length rear

instance Queue Queue where
  enqueue x (Queue front rear) = Queue front (Cons x rear)
  
  dequeue (Queue Nil Nil) = Nothing
  dequeue (Queue Nil rear) = 
    let front = reverse rear
    in case front of
         Cons x xs -> Just (x, Queue xs Nil)
         Nil -> Nothing
  dequeue (Queue (Cons x xs) rear) = Just (x, Queue xs rear)
  
  front (Queue Nil Nil) = Nothing
  front (Queue Nil rear) = 
    case reverse rear of
      Cons x _ -> Just x
      Nil -> Nothing
  front (Queue (Cons x _) _) = Just x
  
  rear (Queue _ Nil) = Nothing
  rear (Queue _ (Cons x _)) = Just x

-- 队列平衡
balance :: Queue a -> Queue a
balance (Queue Nil rear) = Queue (reverse rear) Nil
balance queue = queue

-- 队列应用：广度优先搜索
bfs :: (a -> [a]) -> a -> [a]
bfs neighbors start = bfsAcc (enqueue start empty) []
  where
    bfsAcc :: Queue a -> [a] -> [a]
    bfsAcc queue visited = 
      case dequeue queue of
        Nothing -> reverse visited
        Just (current, newQueue) ->
          if current `elem` visited
            then bfsAcc newQueue visited
            else 
              let newNeighbors = filter (`notElem` visited) (neighbors current)
                  updatedQueue = foldr enqueue newQueue newNeighbors
              in bfsAcc updatedQueue (current : visited)
```

### 树（Tree）

```haskell
-- 二叉树实现
data BinaryTree a = 
    Empty
  | Node a (BinaryTree a) (BinaryTree a)
  deriving (Eq, Show)

-- 二叉树实例
instance DataStructure BinaryTree where
  type Element BinaryTree = a
  empty = Empty
  isEmpty Empty = True
  isEmpty _ = False
  size = treeSize

-- 树大小
treeSize :: BinaryTree a -> Int
treeSize Empty = 0
treeSize (Node _ left right) = 1 + treeSize left + treeSize right

-- 树高度
treeHeight :: BinaryTree a -> Int
treeHeight Empty = 0
treeHeight (Node _ left right) = 1 + max (treeHeight left) (treeHeight right)

-- 树遍历
inorder :: BinaryTree a -> [a]
inorder Empty = []
inorder (Node x left right) = inorder left ++ [x] ++ inorder right

preorder :: BinaryTree a -> [a]
preorder Empty = []
preorder (Node x left right) = [x] ++ preorder left ++ preorder right

postorder :: BinaryTree a -> [a]
postorder Empty = []
postorder (Node x left right) = postorder left ++ postorder right ++ [x]

-- 二叉搜索树
class Ord a => BinarySearchTree t a where
  insert :: a -> t a -> t a
  delete :: a -> t a -> t a
  search :: a -> t a -> Bool
  minimum :: t a -> Maybe a
  maximum :: t a -> Maybe a

instance Ord a => BinarySearchTree BinaryTree a where
  insert x Empty = Node x Empty Empty
  insert x (Node y left right)
    | x < y = Node y (insert x left) right
    | x > y = Node y left (insert x right)
    | otherwise = Node y left right
  
  delete x Empty = Empty
  delete x (Node y left right)
    | x < y = Node y (delete x left) right
    | x > y = Node y left (delete x right)
    | otherwise = 
        case (left, right) of
          (Empty, Empty) -> Empty
          (Empty, r) -> r
          (l, Empty) -> l
          (l, r) -> 
            let minVal = fromJust (minimum r)
            in Node minVal l (delete minVal r)
  
  search x Empty = False
  search x (Node y left right)
    | x == y = True
    | x < y = search x left
    | otherwise = search x right
  
  minimum Empty = Nothing
  minimum (Node x Empty _) = Just x
  minimum (Node _ left _) = minimum left
  
  maximum Empty = Nothing
  maximum (Node x _ Empty) = Just x
  maximum (Node _ _ right) = maximum right

-- 平衡二叉树（AVL树）
data AVLTree a = 
    AVLEmpty
  | AVLNode a Int (AVLTree a) (AVLTree a)
  deriving (Eq, Show)

-- AVL树平衡因子
balanceFactor :: AVLTree a -> Int
balanceFactor AVLEmpty = 0
balanceFactor (AVLNode _ _ left right) = 
  treeHeight left - treeHeight right

-- AVL树旋转
rotateLeft :: AVLTree a -> AVLTree a
rotateLeft (AVLNode x _ left (AVLNode y _ yLeft yRight)) = 
  AVLNode y (1 + max (treeHeight left) (treeHeight yLeft)) 
           (AVLNode x (1 + treeHeight left) left yLeft) 
           yRight
rotateLeft tree = tree

rotateRight :: AVLTree a -> AVLTree a
rotateRight (AVLNode x _ (AVLNode y _ yLeft yRight) right) = 
  AVLNode y (1 + max (treeHeight yRight) (treeHeight right)) 
           yLeft 
           (AVLNode x (1 + treeHeight yRight) yRight right)
rotateRight tree = tree

-- AVL树插入
avlInsert :: Ord a => a -> AVLTree a -> AVLTree a
avlInsert x AVLEmpty = AVLNode x 1 AVLEmpty AVLEmpty
avlInsert x (AVLNode y h left right)
  | x < y = 
      let newLeft = avlInsert x left
          newHeight = 1 + max (treeHeight newLeft) (treeHeight right)
          balanced = balanceAVL (AVLNode y newHeight newLeft right)
      in balanced
  | x > y = 
      let newRight = avlInsert x right
          newHeight = 1 + max (treeHeight left) (treeHeight newRight)
          balanced = balanceAVL (AVLNode y newHeight left newRight)
      in balanced
  | otherwise = AVLNode y h left right

-- AVL树平衡
balanceAVL :: AVLTree a -> AVLTree a
balanceAVL tree = 
  let bf = balanceFactor tree
  in case bf of
       2 -> 
         case balanceFactor (leftSubtree tree) of
           1 -> rotateRight tree
           _ -> rotateRight (rotateLeft tree)
       -2 -> 
         case balanceFactor (rightSubtree tree) of
           -1 -> rotateLeft tree
           _ -> rotateLeft (rotateRight tree)
       _ -> tree
  where
    leftSubtree (AVLNode _ _ left _) = left
    leftSubtree _ = AVLEmpty
    rightSubtree (AVLNode _ _ _ right) = right
    rightSubtree _ = AVLEmpty
```

### 堆（Heap）

```haskell
-- 堆实现
data Heap a = 
    EmptyHeap
  | HeapNode a (Heap a) (Heap a)
  deriving (Eq, Show)

-- 堆属性
isHeap :: Ord a => Heap a -> Bool
isHeap EmptyHeap = True
isHeap (HeapNode x left right) = 
  all (x <=) (heapToList left) &&
  all (x <=) (heapToList right) &&
  isHeap left &&
  isHeap right

-- 堆转列表
heapToList :: Heap a -> [a]
heapToList EmptyHeap = []
heapToList (HeapNode x left right) = 
  x : heapToList left ++ heapToList right

-- 堆插入
heapInsert :: Ord a => a -> Heap a -> Heap a
heapInsert x EmptyHeap = HeapNode x EmptyHeap EmptyHeap
heapInsert x (HeapNode y left right)
  | x <= y = HeapNode x (heapInsert y right) left
  | otherwise = HeapNode y (heapInsert x right) left

-- 堆删除最小元素
heapDeleteMin :: Ord a => Heap a -> Maybe (a, Heap a)
heapDeleteMin EmptyHeap = Nothing
heapDeleteMin (HeapNode x EmptyHeap EmptyHeap) = Just (x, EmptyHeap)
heapDeleteMin (HeapNode x left right) = 
  let (minLeft, newLeft) = fromJust (heapDeleteMin left)
      (minRight, newRight) = fromJust (heapDeleteMin right)
      minChild = min minLeft minRight
      newHeap = if minChild == minLeft
                then HeapNode minChild newLeft right
                else HeapNode minChild left newRight
  in Just (x, newHeap)

-- 堆化
heapify :: Ord a => [a] -> Heap a
heapify = foldr heapInsert EmptyHeap

-- 堆排序
heapSort :: Ord a => [a] -> [a]
heapSort xs = heapSortAcc (heapify xs)
  where
    heapSortAcc EmptyHeap = []
    heapSortAcc heap = 
      case heapDeleteMin heap of
        Just (min, newHeap) -> min : heapSortAcc newHeap
        Nothing -> []
```

## 📊 形式化证明

### 数据结构正确性定理

**定理 1 (栈后进先出)**: 栈操作满足后进先出（LIFO）性质。

```haskell
-- 栈LIFO性质
data StackLIFO = StackLIFO
  { operations :: [StackOperation]
  | result :: Stack Int
  | isLIFO :: Bool
  }

-- LIFO检查
isLIFO :: [StackOperation] -> Bool
isLIFO ops = 
  let finalStack = executeOperations ops empty
      poppedElements = getPoppedElements ops
  in poppedElements == reverse (getPushedElements ops)

-- 证明：栈操作满足LIFO性质
theorem_stackLIFO :: 
  [StackOperation] -> 
  Property
theorem_stackLIFO operations = 
  property $ do
    -- 执行栈操作
    let lifo = StackLIFO operations (executeOperations operations empty) True
    -- 证明LIFO性质
    assert $ isLIFO operations
```

### 队列先进先出定理

**定理 2 (队列先进先出)**: 队列操作满足先进先出（FIFO）性质。

```haskell
-- 队列FIFO性质
data QueueFIFO = QueueFIFO
  { operations :: [QueueOperation]
  | result :: Queue Int
  | isFIFO :: Bool
  }

-- FIFO检查
isFIFO :: [QueueOperation] -> Bool
isFIFO ops = 
  let finalQueue = executeQueueOperations ops empty
      dequeuedElements = getDequeuedElements ops
  in dequeuedElements == getEnqueuedElements ops

-- 证明：队列操作满足FIFO性质
theorem_queueFIFO :: 
  [QueueOperation] -> 
  Property
theorem_queueFIFO operations = 
  property $ do
    -- 执行队列操作
    let fifo = QueueFIFO operations (executeQueueOperations operations empty) True
    -- 证明FIFO性质
    assert $ isFIFO operations
```

### 二叉搜索树性质定理

**定理 3 (二叉搜索树性质)**: 二叉搜索树的中序遍历产生有序序列。

```haskell
-- 二叉搜索树性质
data BSTProperty = BSTProperty
  { tree :: BinaryTree Int
  | inorderTraversal :: [Int]
  | isOrdered :: Bool
  }

-- 有序性检查
isOrdered :: [Int] -> Bool
isOrdered [] = True
isOrdered [_] = True
isOrdered (x:y:xs) = x <= y && isOrdered (y:xs)

-- 证明：二叉搜索树中序遍历有序
theorem_bstInorder :: 
  BinaryTree Int -> 
  Property
theorem_bstInorder tree = 
  property $ do
    -- 假设树是二叉搜索树
    assume $ isBinarySearchTree tree
    -- 获取中序遍历
    let traversal = inorder tree
    -- 检查有序性
    let property = BSTProperty tree traversal True
    -- 证明有序性
    assert $ isOrdered traversal
```

### 堆性质定理

**定理 4 (堆性质)**: 堆的根节点总是最小（或最大）元素。

```haskell
-- 堆性质
data HeapProperty = HeapProperty
  { heap :: Heap Int
  | root :: Int
  | allElements :: [Int]
  | isMinHeap :: Bool
  }

-- 最小堆检查
isMinHeap :: Heap Int -> Bool
isMinHeap heap = 
  let root = getRoot heap
      allElements = heapToList heap
  in all (root <=) allElements

-- 证明：堆根节点是最小元素
theorem_heapMin :: 
  Heap Int -> 
  Property
theorem_heapMin heap = 
  property $ do
    -- 假设堆不为空
    assume $ not (isEmpty heap)
    -- 获取根节点和所有元素
    let root = getRoot heap
    let allElements = heapToList heap
    let property = HeapProperty heap root allElements True
    -- 证明根节点最小
    assert $ all (root <=) allElements
```

## 🔄 性能分析

### 时间复杂度分析

```haskell
-- 时间复杂度
data TimeComplexity = TimeComplexity
  { operation :: String
  | bestCase :: String
  | averageCase :: String
  | worstCase :: String
  }

-- 各种数据结构的时间复杂度
dataStructureComplexity :: DataStructureType -> [TimeComplexity]
dataStructureComplexity structure = case structure of
  LinearStructure -> 
    [ TimeComplexity "Access" "O(1)" "O(n)" "O(n)"
    , TimeComplexity "Search" "O(1)" "O(n)" "O(n)"
    , TimeComplexity "Insert" "O(1)" "O(n)" "O(n)"
    , TimeComplexity "Delete" "O(1)" "O(n)" "O(n)"
    ]
  HierarchicalStructure -> 
    [ TimeComplexity "Access" "O(log n)" "O(log n)" "O(n)"
    , TimeComplexity "Search" "O(log n)" "O(log n)" "O(n)"
    , TimeComplexity "Insert" "O(log n)" "O(log n)" "O(n)"
    , TimeComplexity "Delete" "O(log n)" "O(log n)" "O(n)"
    ]
  _ -> []
```

### 空间复杂度分析

```haskell
-- 空间复杂度
data SpaceComplexity = SpaceComplexity
  { structure :: String
  | spaceComplexity :: String
  | overhead :: String
  }

-- 各种数据结构的空间复杂度
spaceComplexity :: [SpaceComplexity]
spaceComplexity = 
  [ SpaceComplexity "Array" "O(n)" "O(1)"
  , SpaceComplexity "List" "O(n)" "O(n)"
  , SpaceComplexity "Stack" "O(n)" "O(n)"
  , SpaceComplexity "Queue" "O(n)" "O(n)"
  , SpaceComplexity "Tree" "O(n)" "O(n)"
  , SpaceComplexity "Heap" "O(n)" "O(n)"
  ]
```

## 🎯 最佳实践

### 1. 数据结构选择

- **数组**: 适用于随机访问和已知大小的数据
- **链表**: 适用于频繁插入删除操作
- **栈**: 适用于后进先出的场景
- **队列**: 适用于先进先出的场景
- **树**: 适用于需要层次结构的数据
- **堆**: 适用于需要快速找到最值的场景

### 2. 性能优化

- **缓存友好**: 选择缓存友好的数据结构
- **内存效率**: 考虑内存使用和分配开销
- **算法匹配**: 选择与算法匹配的数据结构
- **并发安全**: 在并发环境中选择合适的数据结构

### 3. 函数式编程

- **不可变性**: 优先使用不可变数据结构
- **持久化**: 利用数据结构的持久化特性
- **函数组合**: 使用函数组合操作数据结构
- **类型安全**: 充分利用类型系统保证安全

### 4. 错误处理

- **边界检查**: 检查操作的边界条件
- **空值处理**: 正确处理空数据结构
- **异常处理**: 在适当的地方使用异常
- **验证**: 验证数据结构的完整性

## 📚 总结

基础数据结构是计算机科学的基础，在Haskell中它们以函数式的方式实现。

关键要点：

1. **类型安全**: 利用Haskell类型系统保证操作安全
2. **不可变性**: 数据结构操作返回新的实例
3. **函数式**: 使用函数式编程范式操作数据
4. **性能**: 理解各种操作的时间复杂度
5. **选择**: 根据应用场景选择合适的数据结构

通过Haskell的函数式特性，我们可以构建出类型安全、易于推理的数据结构实现。
