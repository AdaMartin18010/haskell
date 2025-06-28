# 数据结构

## 概述

本文档介绍重要的数据结构及其在Haskell中的实现。

## 基本数据结构

### 列表 (List)

```haskell
-- 列表是Haskell的基本数据结构
-- 单链表实现
data List a = Nil | Cons a (List a)

-- 基本操作
head :: List a -> Maybe a
head Nil = Nothing
head (Cons x _) = Just x

tail :: List a -> Maybe (List a)
tail Nil = Nothing
tail (Cons _ xs) = Just xs

-- 长度
length :: List a -> Int
length Nil = 0
length (Cons _ xs) = 1 + length xs

-- 连接
append :: List a -> List a -> List a
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)
```

### 树 (Tree)

```haskell
-- 二叉树
data Tree a = Empty | Node a (Tree a) (Tree a)

-- 二叉搜索树
insert :: Ord a => a -> Tree a -> Tree a
insert x Empty = Node x Empty Empty
insert x (Node y left right)
  | x < y = Node y (insert x left) right
  | otherwise = Node y left (insert x right)

-- 查找
search :: Ord a => a -> Tree a -> Bool
search _ Empty = False
search x (Node y left right)
  | x == y = True
  | x < y = search x left
  | otherwise = search x right

-- 中序遍历
inorder :: Tree a -> [a]
inorder Empty = []
inorder (Node x left right) = inorder left ++ [x] ++ inorder right
```

### 堆 (Heap)

```haskell
-- 最小堆
data Heap a = EmptyHeap | Heap a (Heap a) (Heap a)

-- 插入
insertHeap :: Ord a => a -> Heap a -> Heap a
insertHeap x EmptyHeap = Heap x EmptyHeap EmptyHeap
insertHeap x (Heap y left right)
  | x <= y = Heap x (insertHeap y right) left
  | otherwise = Heap y (insertHeap x right) left

-- 删除最小值
deleteMin :: Ord a => Heap a -> Maybe (a, Heap a)
deleteMin EmptyHeap = Nothing
deleteMin (Heap x left right) = Just (x, merge left right)

-- 合并堆
merge :: Ord a => Heap a -> Heap a -> Heap a
merge EmptyHeap h = h
merge h EmptyHeap = h
merge (Heap x left1 right1) (Heap y left2 right2)
  | x <= y = Heap x (merge right1 (Heap y left2 right2)) left1
  | otherwise = Heap y (merge right2 (Heap x left1 right1)) left2
```

## 高级数据结构

### 红黑树

```haskell
-- 红黑树
data Color = Red | Black

data RBTree a = EmptyRB | RBNode Color (RBTree a) a (RBTree a)

-- 插入
insertRB :: Ord a => a -> RBTree a -> RBTree a
insertRB x t = 
  let t' = insert' x t
  in case t' of
       RBNode _ left y right -> RBNode Black left y right
       EmptyRB -> EmptyRB

insert' :: Ord a => a -> RBTree a -> RBTree a
insert' x EmptyRB = RBNode Red EmptyRB x EmptyRB
insert' x (RBNode color left y right)
  | x < y = balance color (insert' x left) y right
  | otherwise = balance color left y (insert' x right)

-- 平衡
balance :: Color -> RBTree a -> a -> RBTree a -> RBTree a
balance Black (RBNode Red (RBNode Red a x b) y c) z d = 
  RBNode Red (RBNode Black a x b) y (RBNode Black c z d)
balance Black (RBNode Red a x (RBNode Red b y c)) z d = 
  RBNode Red (RBNode Black a x b) y (RBNode Black c z d)
balance Black a x (RBNode Red (RBNode Red b y c) z d) = 
  RBNode Red (RBNode Black a x b) y (RBNode Black c z d)
balance Black a x (RBNode Red b y (RBNode Red c z d)) = 
  RBNode Red (RBNode Black a x b) y (RBNode Black c z d)
balance color left x right = RBNode color left x right
```

### 散列表 (Hash Table)

```haskell
-- 散列表
data HashTable k v = HashTable Int [(k, v)]

-- 创建散列表
newHashTable :: Int -> HashTable k v
newHashTable size = HashTable size []

-- 插入
insertHash :: (Eq k, Hashable k) => k -> v -> HashTable k v -> HashTable k v
insertHash key value (HashTable size buckets) = 
  let index = hash key `mod` size
      bucket = buckets !! index
      newBucket = (key, value) : filter ((/= key) . fst) bucket
      newBuckets = updateAt index newBucket buckets
  in HashTable size newBuckets

-- 查找
lookupHash :: (Eq k, Hashable k) => k -> HashTable k v -> Maybe v
lookupHash key (HashTable size buckets) = 
  let index = hash key `mod` size
      bucket = buckets !! index
  in lookup key bucket

-- 哈希函数类型类
class Hashable a where
  hash :: a -> Int

instance Hashable Int where
  hash = id

instance Hashable String where
  hash = foldl (\h c -> h * 31 + fromEnum c) 0
```

### 图 (Graph)

```haskell
-- 图
data Graph a = Graph [(a, [a])]

-- 邻接表表示
adjacencyList :: Graph a -> [(a, [a])]
adjacencyList (Graph edges) = edges

-- 添加边
addEdge :: Eq a => a -> a -> Graph a -> Graph a
addEdge from to (Graph edges) = 
  let updateNode (node, neighbors) = 
        if node == from 
        then (node, to : neighbors)
        else (node, neighbors)
  in Graph (map updateNode edges)

-- 深度优先搜索
dfs :: Eq a => Graph a -> a -> [a]
dfs graph start = dfs' graph start []

dfs' :: Eq a => Graph a -> a -> [a] -> [a]
dfs' graph node visited
  | node `elem` visited = visited
  | otherwise = 
      let neighbors = findNeighbors graph node
          newVisited = node : visited
      in foldr (dfs' graph) newVisited neighbors

findNeighbors :: Eq a => Graph a -> a -> [a]
findNeighbors (Graph edges) node = 
  case lookup node edges of
    Just neighbors -> neighbors
    Nothing -> []
```

## 函数式数据结构

### 不可变队列

```haskell
-- 不可变队列（使用两个列表）
data Queue a = Queue [a] [a]

-- 空队列
emptyQueue :: Queue a
emptyQueue = Queue [] []

-- 入队
enqueue :: a -> Queue a -> Queue a
enqueue x (Queue front back) = Queue front (x : back)

-- 出队
dequeue :: Queue a -> Maybe (a, Queue a)
dequeue (Queue [] []) = Nothing
dequeue (Queue [] back) = dequeue (Queue (reverse back) [])
dequeue (Queue (x:front) back) = Just (x, Queue front back)
```

### 不可变栈

```haskell
-- 不可变栈
data Stack a = Stack [a]

-- 空栈
emptyStack :: Stack a
emptyStack = Stack []

-- 压栈
push :: a -> Stack a -> Stack a
push x (Stack xs) = Stack (x : xs)

-- 弹栈
pop :: Stack a -> Maybe (a, Stack a)
pop (Stack []) = Nothing
pop (Stack (x:xs)) = Just (x, Stack xs)

-- 查看栈顶
peek :: Stack a -> Maybe a
peek (Stack []) = Nothing
peek (Stack (x:_)) = Just x
```

### 持久化数据结构

```haskell
-- 持久化二叉树
data PersistentTree a = Empty | Node a (PersistentTree a) (PersistentTree a)

-- 路径复制
updatePath :: Eq a => a -> a -> PersistentTree a -> PersistentTree a
updatePath oldVal newVal Empty = Empty
updatePath oldVal newVal (Node x left right)
  | x == oldVal = Node newVal left right
  | otherwise = Node x (updatePath oldVal newVal left) (updatePath oldVal newVal right)

-- 共享结构
insertPersistent :: Ord a => a -> PersistentTree a -> PersistentTree a
insertPersistent x Empty = Node x Empty Empty
insertPersistent x (Node y left right)
  | x < y = Node y (insertPersistent x left) right
  | otherwise = Node y left (insertPersistent x right)
```

## 性能分析

### 时间复杂度

```haskell
-- 数据结构操作复杂度
data Operation = Insert | Delete | Search | Update

data TimeComplexity = O1 | OLogN | ON | ONLogN | ON2

-- 复杂度分析
complexityAnalysis :: Operation -> String -> TimeComplexity
complexityAnalysis Insert "List" = ON
complexityAnalysis Insert "Tree" = OLogN
complexityAnalysis Insert "HashTable" = O1
complexityAnalysis Search "List" = ON
complexityAnalysis Search "Tree" = OLogN
complexityAnalysis Search "HashTable" = O1
complexityAnalysis _ _ = ON
```

### 空间复杂度

```haskell
-- 空间复杂度分析
spaceComplexity :: String -> Int -> Int
spaceComplexity "List" n = n
spaceComplexity "Tree" n = n
spaceComplexity "HashTable" n = n
spaceComplexity "Graph" n = n * n  -- 邻接矩阵
spaceComplexity _ n = n
```

## 实际应用

### 缓存实现

```haskell
-- LRU缓存
data LRUCache k v = LRUCache Int (Map k v) (Queue k)

-- 创建缓存
newLRUCache :: Int -> LRUCache k v
newLRUCache capacity = LRUCache capacity Map.empty emptyQueue

-- 获取值
get :: (Eq k, Ord k) => k -> LRUCache k v -> Maybe (v, LRUCache k v)
get key (LRUCache capacity cache queue) = 
  case Map.lookup key cache of
    Just value -> Just (value, LRUCache capacity cache (enqueue key queue))
    Nothing -> Nothing

-- 设置值
put :: (Eq k, Ord k) => k -> v -> LRUCache k v -> LRUCache k v
put key value (LRUCache capacity cache queue) = 
  let newCache = Map.insert key value cache
      newQueue = enqueue key queue
  in if Map.size newCache > capacity
     then evictLRU (LRUCache capacity newCache newQueue)
     else LRUCache capacity newCache newQueue

-- 淘汰最久未使用的项
evictLRU :: (Eq k, Ord k) => LRUCache k v -> LRUCache k v
evictLRU (LRUCache capacity cache queue) = 
  case dequeue queue of
    Just (oldKey, newQueue) -> 
      LRUCache capacity (Map.delete oldKey cache) newQueue
    Nothing -> LRUCache capacity cache queue
```

---

**相关链接**：

- [算法](./004-Algorithms.md)
- [性能优化](./006-Performance-Optimization.md)
