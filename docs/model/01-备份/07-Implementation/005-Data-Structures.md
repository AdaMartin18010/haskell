# 数据结构

## 概述

本文档介绍重要的数据结构及其在Haskell中的实现。数据结构是程序设计的基础，选择合适的数据结构对程序性能至关重要。

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

-- 折叠
foldr :: (a -> b -> b) -> b -> List a -> b
foldr _ z Nil = z
foldr f z (Cons x xs) = f x (foldr f z xs)

-- 映射
map :: (a -> b) -> List a -> List b
map _ Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)
```

### 数组 (Array)

```haskell
import qualified Data.Array as A

-- 固定大小数组
type Array i e = A.Array i e

-- 创建数组
createArray :: (Int, Int) -> [e] -> Array Int e
createArray bounds elems = A.listArray bounds elems

-- 访问元素
getElement :: Array Int e -> Int -> e
getElement arr i = arr A.! i

-- 更新元素
updateElement :: Array Int e -> Int -> e -> Array Int e
updateElement arr i new = arr A.// [(i, new)]

-- 示例：矩阵操作
type Matrix = Array (Int, Int) Double

matrixMultiply :: Matrix -> Matrix -> Matrix
matrixMultiply a b = 
  let ((ar1, ac1), (ar2, ac2)) = A.bounds a
      ((br1, bc1), (br2, bc2)) = A.bounds b
      bounds = ((ar1, bc1), (ar2, bc2))
  in A.array bounds [((i, j), sum [a A.! (i, k) * b A.! (k, j) | k <- [ac1..ac2]]) 
                    | i <- [ar1..ar2], j <- [bc1..bc2]]
```

### 树 (Tree)

```haskell
-- 二叉树
data Tree a = Empty | Node a (Tree a) (Tree a)
  deriving (Show, Eq)

-- 二叉搜索树
insert :: Ord a => a -> Tree a -> Tree a
insert x Empty = Node x Empty Empty
insert x (Node y left right)
  | x < y = Node y (insert x left) right
  | x > y = Node y left (insert x right)
  | otherwise = Node y left right  -- 重复元素不插入

-- 查找
search :: Ord a => a -> Tree a -> Bool
search _ Empty = False
search x (Node y left right)
  | x == y = True
  | x < y = search x left
  | otherwise = search x right

-- 遍历
inorder :: Tree a -> [a]
inorder Empty = []
inorder (Node x left right) = inorder left ++ [x] ++ inorder right

preorder :: Tree a -> [a]
preorder Empty = []
preorder (Node x left right) = x : preorder left ++ preorder right

postorder :: Tree a -> [a]
postorder Empty = []
postorder (Node x left right) = postorder left ++ postorder right ++ [x]

-- 树的高度
height :: Tree a -> Int
height Empty = 0
height (Node _ left right) = 1 + max (height left) (height right)

-- 平衡性检查
isBalanced :: Tree a -> Bool
isBalanced Empty = True
isBalanced (Node _ left right) = 
  abs (height left - height right) <= 1 && isBalanced left && isBalanced right
```

### 堆 (Heap)

```haskell
-- 最小堆
data Heap a = EmptyHeap | Heap a (Heap a) (Heap a)
  deriving (Show, Eq)

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

-- 从列表创建堆
fromList :: Ord a => [a] -> Heap a
fromList = foldr insertHeap EmptyHeap

-- 堆排序
heapSort :: Ord a => [a] -> [a]
heapSort xs = 
  let heap = fromList xs
  in heapSort' heap []
  where
    heapSort' EmptyHeap acc = reverse acc
    heapSort' h acc = 
      case deleteMin h of
        Nothing -> reverse acc
        Just (x, h') -> heapSort' h' (x : acc)
```

## 高级数据结构

### 红黑树

```haskell
-- 红黑树
data Color = Red | Black
  deriving (Show, Eq)

data RBTree a = EmptyRB | RBNode Color (RBTree a) a (RBTree a)
  deriving (Show, Eq)

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
  | x > y = balance color left y (insert' x right)
  | otherwise = RBNode color left y right

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

-- 查找
memberRB :: Ord a => a -> RBTree a -> Bool
memberRB _ EmptyRB = False
memberRB x (RBNode _ left y right)
  | x < y = memberRB x left
  | x > y = memberRB x right
  | otherwise = True
```

### AVL 树

```haskell
-- AVL 树
data AVLTree a = EmptyAVL | AVLNode Int (AVLTree a) a (AVLTree a)
  deriving (Show, Eq)

-- 获取高度
heightAVL :: AVLTree a -> Int
heightAVL EmptyAVL = 0
heightAVL (AVLNode h _ _ _) = h

-- 创建节点
nodeAVL :: AVLTree a -> a -> AVLTree a -> AVLTree a
nodeAVL left x right = 
  AVLNode (1 + max (heightAVL left) (heightAVL right)) left x right

-- 平衡因子
balanceFactor :: AVLTree a -> Int
balanceFactor EmptyAVL = 0
balanceFactor (AVLNode _ left _ right) = heightAVL left - heightAVL right

-- 旋转
rotateLeft :: AVLTree a -> AVLTree a
rotateLeft (AVLNode _ left x (AVLNode _ rleft y rright)) = 
  nodeAVL (nodeAVL left x rleft) y rright
rotateLeft t = t

rotateRight :: AVLTree a -> AVLTree a
rotateRight (AVLNode _ (AVLNode _ lleft y lright) x right) = 
  nodeAVL lleft y (nodeAVL lright x right)
rotateRight t = t

-- AVL 插入
insertAVL :: Ord a => a -> AVLTree a -> AVLTree a
insertAVL x EmptyAVL = nodeAVL EmptyAVL x EmptyAVL
insertAVL x (AVLNode _ left y right)
  | x < y = balanceAVL (nodeAVL (insertAVL x left) y right)
  | x > y = balanceAVL (nodeAVL left y (insertAVL x right))
  | otherwise = nodeAVL left y right

-- AVL 平衡
balanceAVL :: AVLTree a -> AVLTree a
balanceAVL t@(AVLNode _ left x right)
  | balanceFactor t > 1 && balanceFactor left >= 0 = rotateRight t
  | balanceFactor t > 1 && balanceFactor left < 0 = 
      rotateRight (nodeAVL (rotateLeft left) x right)
  | balanceFactor t < -1 && balanceFactor right <= 0 = rotateLeft t
  | balanceFactor t < -1 && balanceFactor right > 0 = 
      rotateLeft (nodeAVL left x (rotateRight right))
  | otherwise = t
balanceAVL t = t
```

### 散列表 (Hash Table)

```haskell
import qualified Data.Array as A

-- 散列表
data HashTable k v = HashTable Int (A.Array Int [(k, v)])

-- 创建散列表
newHashTable :: Int -> HashTable k v
newHashTable size = HashTable size (A.array (0, size-1) [(i, []) | i <- [0..size-1]])

-- 哈希函数类型类
class Hashable a where
  hash :: a -> Int

instance Hashable Int where
  hash = abs

instance Hashable String where
  hash = abs . foldl (\h c -> h * 31 + fromEnum c) 0

-- 插入
insertHash :: (Eq k, Hashable k) => k -> v -> HashTable k v -> HashTable k v
insertHash key value (HashTable size buckets) = 
  let index = hash key `mod` size
      bucket = buckets A.! index
      newBucket = (key, value) : filter ((/= key) . fst) bucket
  in HashTable size (buckets A.// [(index, newBucket)])

-- 查找
lookupHash :: (Eq k, Hashable k) => k -> HashTable k v -> Maybe v
lookupHash key (HashTable size buckets) = 
  let index = hash key `mod` size
      bucket = buckets A.! index
  in lookup key bucket

-- 删除
deleteHash :: (Eq k, Hashable k) => k -> HashTable k v -> HashTable k v
deleteHash key (HashTable size buckets) = 
  let index = hash key `mod` size
      bucket = buckets A.! index
      newBucket = filter ((/= key) . fst) bucket
  in HashTable size (buckets A.// [(index, newBucket)])

-- 获取所有键值对
toListHash :: HashTable k v -> [(k, v)]
toListHash (HashTable _ buckets) = concat (A.elems buckets)
```

### 图 (Graph)

```haskell
import qualified Data.Map as M
import qualified Data.Set as S

-- 图的不同表示
data Graph a = Graph (M.Map a [a])  -- 邻接表
  deriving (Show, Eq)

-- 创建空图
emptyGraph :: Graph a
emptyGraph = Graph M.empty

-- 添加顶点
addVertex :: Ord a => a -> Graph a -> Graph a
addVertex v (Graph m) = Graph (M.insertWith (++) v [] m)

-- 添加边
addEdge :: Ord a => a -> a -> Graph a -> Graph a
addEdge from to (Graph m) = 
  Graph (M.insertWith (++) from [to] (M.insertWith (++) to [] m))

-- 获取邻居
neighbors :: Ord a => a -> Graph a -> [a]
neighbors v (Graph m) = M.findWithDefault [] v m

-- 深度优先搜索
dfs :: Ord a => Graph a -> a -> [a]
dfs graph start = dfs' graph start S.empty []

dfs' :: Ord a => Graph a -> a -> S.Set a -> [a] -> [a]
dfs' graph node visited acc
  | S.member node visited = acc
  | otherwise = 
      let newVisited = S.insert node visited
          neighs = neighbors node graph
      in foldr (\n acc' -> dfs' graph n newVisited acc') (node : acc) neighs

-- 广度优先搜索
bfs :: Ord a => Graph a -> a -> [a]
bfs graph start = bfs' graph [start] S.empty []

bfs' :: Ord a => Graph a -> [a] -> S.Set a -> [a] -> [a]
bfs' _ [] _ acc = reverse acc
bfs' graph (node:queue) visited acc
  | S.member node visited = bfs' graph queue visited acc
  | otherwise = 
      let newVisited = S.insert node visited
          neighs = neighbors node graph
          newQueue = queue ++ neighs
      in bfs' graph newQueue newVisited (node : acc)

-- 拓扑排序
topologicalSort :: Ord a => Graph a -> Maybe [a]
topologicalSort graph@(Graph m) = 
  let vertices = M.keys m
      sorted = topSort graph vertices []
  in if length sorted == length vertices then Just sorted else Nothing

topSort :: Ord a => Graph a -> [a] -> [a] -> [a]
topSort _ [] acc = reverse acc
topSort graph vertices acc = 
  case filter (hasNoIncomingEdges graph vertices) vertices of
    [] -> acc  -- 有环
    (v:_) -> topSort graph (filter (/= v) vertices) (v : acc)

hasNoIncomingEdges :: Ord a => Graph a -> [a] -> a -> Bool
hasNoIncomingEdges (Graph m) vertices target = 
  not $ any (\v -> target `elem` M.findWithDefault [] v m) vertices
```

### 字典树 (Trie)

```haskell
-- 字典树
data Trie = Trie Bool (M.Map Char Trie)
  deriving (Show, Eq)

-- 空字典树
emptyTrie :: Trie
emptyTrie = Trie False M.empty

-- 插入字符串
insertTrie :: String -> Trie -> Trie
insertTrie [] (Trie _ children) = Trie True children
insertTrie (c:cs) (Trie isEnd children) = 
  let childTrie = M.findWithDefault emptyTrie c children
      newChildTrie = insertTrie cs childTrie
      newChildren = M.insert c newChildTrie children
  in Trie isEnd newChildren

-- 查找字符串
searchTrie :: String -> Trie -> Bool
searchTrie [] (Trie isEnd _) = isEnd
searchTrie (c:cs) (Trie _ children) = 
  case M.lookup c children of
    Nothing -> False
    Just childTrie -> searchTrie cs childTrie

-- 前缀搜索
startsWith :: String -> Trie -> Bool
startsWith [] _ = True
startsWith (c:cs) (Trie _ children) = 
  case M.lookup c children of
    Nothing -> False
    Just childTrie -> startsWith cs childTrie

-- 获取所有以给定前缀开始的字符串
getAllWords :: String -> Trie -> [String]
getAllWords prefix trie = 
  case findPrefix prefix trie of
    Nothing -> []
    Just subTrie -> map (prefix ++) (getWordsFromTrie subTrie)

findPrefix :: String -> Trie -> Maybe Trie
findPrefix [] trie = Just trie
findPrefix (c:cs) (Trie _ children) = 
  case M.lookup c children of
    Nothing -> Nothing
    Just childTrie -> findPrefix cs childTrie

getWordsFromTrie :: Trie -> [String]
getWordsFromTrie (Trie isEnd children) = 
  let currentWord = if isEnd then [""] else []
      childWords = concatMap (\(c, trie) -> map (c:) (getWordsFromTrie trie)) 
                             (M.toList children)
  in currentWord ++ childWords
```

## 性能分析

### 时间复杂度比较

| 操作 | 数组 | 链表 | BST | 散列表 | 堆 |
|------|------|------|-----|--------|-----|
| 访问 | O(1) | O(n) | O(log n) | O(1) | - |
| 搜索 | O(n) | O(n) | O(log n) | O(1) | O(n) |
| 插入 | O(n) | O(1) | O(log n) | O(1) | O(log n) |
| 删除 | O(n) | O(1) | O(log n) | O(1) | O(log n) |

### 空间复杂度

```haskell
-- 分析不同数据结构的空间使用
spaceAnalysis :: IO ()
spaceAnalysis = do
  putStrLn "数据结构空间复杂度分析："
  putStrLn "- 数组: O(n)"
  putStrLn "- 链表: O(n)"
  putStrLn "- 二叉搜索树: O(n)"
  putStrLn "- 散列表: O(n + m) - m 为桶数"
  putStrLn "- 堆: O(n)"
  putStrLn "- 图: O(V + E) - V 顶点数，E 边数"
```

## 实际应用示例

### 文本处理

```haskell
-- 使用字典树进行文本自动补全
type AutoComplete = Trie

-- 构建自动补全系统
buildAutoComplete :: [String] -> AutoComplete
buildAutoComplete words = foldr insertTrie emptyTrie words

-- 获取建议
getSuggestions :: String -> AutoComplete -> [String]
getSuggestions prefix ac = take 10 $ getAllWords prefix ac

-- 示例使用
textProcessingExample :: IO ()
textProcessingExample = do
  let words = ["apple", "application", "apply", "appreciate", "approach"]
  let ac = buildAutoComplete words
  let suggestions = getSuggestions "app" ac
  print suggestions  -- ["apple", "application", "apply", "appreciate", "approach"]
```

### 图算法应用

```haskell
-- 社交网络分析
type Person = String
type SocialNetwork = Graph Person

-- 构建社交网络
buildSocialNetwork :: [(Person, Person)] -> SocialNetwork
buildSocialNetwork connections = 
  foldr (\(a, b) g -> addEdge a b (addEdge b a g)) emptyGraph connections

-- 找到共同朋友
mutualFriends :: Person -> Person -> SocialNetwork -> [Person]
mutualFriends p1 p2 network = 
  let friends1 = S.fromList $ neighbors p1 network
      friends2 = S.fromList $ neighbors p2 network
  in S.toList $ S.intersection friends1 friends2

-- 计算度中心性
degreeCentrality :: Person -> SocialNetwork -> Int
degreeCentrality person network = length $ neighbors person network
```

### 优先队列应用

```haskell
-- 任务调度系统
data Task = Task
  { taskId :: Int
  , priority :: Int
  , description :: String
  } deriving (Show, Eq)

instance Ord Task where
  compare (Task _ p1 _) (Task _ p2 _) = compare p2 p1  -- 高优先级在前

type TaskQueue = Heap Task

-- 添加任务
addTask :: Task -> TaskQueue -> TaskQueue
addTask = insertHeap

-- 执行下一个任务
executeNextTask :: TaskQueue -> Maybe (Task, TaskQueue)
executeNextTask = deleteMin

-- 示例
taskSchedulingExample :: IO ()
taskSchedulingExample = do
  let task1 = Task 1 3 "普通任务"
  let task2 = Task 2 5 "重要任务"
  let task3 = Task 3 1 "低优先级任务"
  
  let queue = foldr addTask EmptyHeap [task1, task2, task3]
  
  case executeNextTask queue of
    Nothing -> putStrLn "没有任务"
    Just (task, remainingQueue) -> do
      putStrLn $ "执行任务: " ++ description task
      print $ fmap fst $ executeNextTask remainingQueue
```

## 最佳实践

### 选择合适的数据结构

```haskell
-- 数据结构选择指南
dataStructureGuide :: String -> String
dataStructureGuide useCase = case useCase of
  "frequent_access" -> "使用数组或向量"
  "frequent_insertion" -> "使用链表或动态数组"
  "sorted_data" -> "使用二叉搜索树或红黑树"
  "key_value_lookup" -> "使用散列表"
  "priority_queue" -> "使用堆"
  "graph_algorithms" -> "使用邻接表或邻接矩阵"
  "string_matching" -> "使用字典树"
  _ -> "根据具体需求选择"
```

### 性能优化技巧

```haskell
-- 惰性求值优化
lazyOptimization :: [Int] -> Int
lazyOptimization xs = head $ dropWhile (<= 100) xs

-- 尾递归优化
tailRecursiveSum :: [Int] -> Int
tailRecursiveSum xs = sumHelper xs 0
  where
    sumHelper [] acc = acc
    sumHelper (y:ys) acc = sumHelper ys (acc + y)

-- 内存效率优化
memoryEfficientMap :: (a -> b) -> [a] -> [b]
memoryEfficientMap f = foldr ((:) . f) []
```

## 总结

数据结构是程序设计的基础。选择合适的数据结构可以显著提高程序性能：

1. **基本结构**: 列表、数组、树为其他结构提供基础
2. **高级结构**: 红黑树、AVL树提供平衡保证
3. **专用结构**: 散列表、字典树针对特定用途优化
4. **图结构**: 解决复杂关系问题

在Haskell中，函数式编程范式为数据结构实现提供了优雅的解决方案，通过类型系统保证安全性，通过惰性求值提供效率。

## 参考资料

- [Haskell Data Structures](https://wiki.haskell.org/Data_structures)
- [Functional Data Structures](https://www.cs.cmu.edu/~rwh/students/okasaki.pdf)
- [Algorithm Design with Haskell](https://www.cambridge.org/core/books/algorithm-design-with-haskell/)

---

**相关链接**：

- [算法](./004-Algorithms.md)
- [性能优化](./006-Performance-Optimization.md)
