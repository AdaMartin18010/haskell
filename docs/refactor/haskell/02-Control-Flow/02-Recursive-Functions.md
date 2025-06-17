# Haskell 递归函数

## 概述

递归函数是Haskell中实现循环和迭代的核心机制，基于数学归纳法和不动点理论。

## 数学定义

### 递归函数形式化定义

给定类型 $A$ 和 $B$，递归函数定义为：

$$f : A \rightarrow B$$

其中 $f$ 满足递归方程：

$$
f(x) = \begin{cases}
\text{base}(x) & \text{if } \text{isBase}(x) \\
\text{step}(x, f(\text{next}(x))) & \text{otherwise}
\end{cases}
$$

### 不动点理论

递归函数可以表示为不动点：

$$f = \text{fix}(F)$$

其中 $F : (A \rightarrow B) \rightarrow (A \rightarrow B)$ 是函数变换器，满足：

$$\text{fix}(F) = F(\text{fix}(F))$$

## Haskell实现

### 基础递归函数

```haskell
-- 基础递归函数模块
module ControlFlow.Recursive where

-- 阶乘函数
factorial :: Integer -> Integer
factorial 0 = 1
factorial n = n * factorial (n - 1)

-- 斐波那契数列
fibonacci :: Integer -> Integer
fibonacci 0 = 0
fibonacci 1 = 1
fibonacci n = fibonacci (n - 1) + fibonacci (n - 2)

-- 列表长度
length' :: [a] -> Int
length' [] = 0
length' (_:xs) = 1 + length' xs

-- 列表求和
sum' :: Num a => [a] -> a
sum' [] = 0
sum' (x:xs) = x + sum' xs
```

### 尾递归优化

```haskell
-- 尾递归阶乘
factorialTail :: Integer -> Integer
factorialTail n = go n 1
  where
    go 0 acc = acc
    go n acc = go (n - 1) (n * acc)

-- 尾递归斐波那契
fibonacciTail :: Integer -> Integer
fibonacciTail n = go n 0 1
  where
    go 0 a _ = a
    go 1 _ b = b
    go n a b = go (n - 1) b (a + b)

-- 尾递归列表处理
reverse' :: [a] -> [a]
reverse' xs = go xs []
  where
    go [] acc = acc
    go (x:xs) acc = go xs (x:acc)
```

### 高阶递归函数

```haskell
-- 高阶递归函数
foldr' :: (a -> b -> b) -> b -> [a] -> b
foldr' _ z [] = z
foldr' f z (x:xs) = f x (foldr' f z xs)

foldl' :: (b -> a -> b) -> b -> [a] -> b
foldl' _ z [] = z
foldl' f z (x:xs) = foldl' f (f z x) xs

-- 映射函数
map' :: (a -> b) -> [a] -> [b]
map' _ [] = []
map' f (x:xs) = f x : map' f xs

-- 过滤函数
filter' :: (a -> Bool) -> [a] -> [a]
filter' _ [] = []
filter' p (x:xs)
  | p x = x : filter' p xs
  | otherwise = filter' p xs
```

### 相互递归

```haskell
-- 相互递归函数
data Tree a = Empty | Node a (Tree a) (Tree a)

-- 计算树的高度
height :: Tree a -> Int
height Empty = 0
height (Node _ left right) = 1 + max (height left) (height right)

-- 计算树的节点数
size :: Tree a -> Int
size Empty = 0
size (Node _ left right) = 1 + size left + size right

-- 相互递归的奇偶判断
isEven :: Integer -> Bool
isEven 0 = True
isEven n = isOdd (n - 1)

isOdd :: Integer -> Bool
isOdd 0 = False
isOdd n = isEven (n - 1)
```

## 形式化语义

### 递归函数的语义

```haskell
-- 递归函数的语义定义
data RecursiveSemantics a b =
  RecursiveSemantics
    { baseCase :: a -> Bool
    , baseValue :: a -> b
    , stepFunction :: a -> b -> b
    , nextValue :: a -> a
    }

-- 递归函数解释器
interpretRecursive :: RecursiveSemantics a b -> a -> b
interpretRecursive (RecursiveSemantics isBase base step next) x =
  if isBase x
    then base x
    else step x (interpretRecursive (RecursiveSemantics isBase base step next) (next x))

-- 不动点语义
newtype Fix f = Fix { unFix :: f (Fix f) }

-- 不动点组合子
fix :: (a -> a) -> a
fix f = let x = f x in x

-- 递归函数的代数性质
class RecursiveAlgebra a where
  -- 递归组合
  recursiveCompose :: (a -> a) -> (a -> a) -> a -> a
  -- 递归映射
  recursiveMap :: (a -> b) -> (a -> a) -> a -> b
```

### 递归模式

```haskell
-- 递归模式定义
data RecursionPattern a b =
  SimpleRecursion (a -> Bool) (a -> b) (a -> a -> b)
  | MutualRecursion [(a -> Bool)] [(a -> b)] [(a -> a -> b)]
  | TailRecursion (a -> Bool) (a -> b) (a -> a -> b)

-- 递归模式解释器
interpretPattern :: RecursionPattern a b -> a -> b
interpretPattern (SimpleRecursion isBase base step) x =
  if isBase x
    then base x
    else step x (interpretPattern (SimpleRecursion isBase base step) x)
```

## 类型安全保证

### 递归函数的类型系统

```haskell
-- 递归函数的类型检查
class TypeSafeRecursive a b where
  type BaseType a b
  type StepType a b
  
  -- 类型安全的递归函数
  typeSafeRecursive :: BaseType a b -> StepType a b -> a -> b
  
  -- 类型安全的尾递归
  typeSafeTailRecursive :: BaseType a b -> StepType a b -> a -> b

-- 实例化
instance TypeSafeRecursive Int Int where
  type BaseType Int Int = (Int -> Bool, Int -> Int)
  type StepType Int Int = (Int -> Int -> Int)
  
  typeSafeRecursive (isBase, base) step x =
    if isBase x then base x else step x (typeSafeRecursive (isBase, base) step x)
```

## 性能优化

### 记忆化递归

```haskell
-- 记忆化递归
memoize :: (Int -> a) -> Int -> a
memoize f = (map f [0..] !!)

-- 记忆化斐波那契
fibonacciMemo :: Int -> Integer
fibonacciMemo = memoize fib
  where
    fib 0 = 0
    fib 1 = 1
    fib n = fibonacciMemo (n - 1) + fibonacciMemo (n - 2)

-- 动态规划风格的记忆化
dynamicFibonacci :: Int -> Integer
dynamicFibonacci n = go n (replicate (n + 1) (-1))
  where
    go 0 memo = 0
    go 1 memo = 1
    go i memo
      | memo !! i /= -1 = memo !! i
      | otherwise =
          let val = go (i - 1) memo + go (i - 2) memo
          in val
```

### 惰性递归

```haskell
-- 惰性递归列表
infiniteList :: [Integer]
infiniteList = 0 : 1 : zipWith (+) infiniteList (tail infiniteList)

-- 惰性斐波那契
lazyFibonacci :: [Integer]
lazyFibonacci = 0 : 1 : zipWith (+) lazyFibonacci (tail lazyFibonacci)

-- 惰性素数生成
primes :: [Integer]
primes = sieve [2..]
  where
    sieve (p:xs) = p : sieve [x | x <- xs, x `mod` p /= 0]
```

## 实际应用

### 算法实现

```haskell
-- 快速排序
quicksort :: Ord a => [a] -> [a]
quicksort [] = []
quicksort (x:xs) =
  let smaller = quicksort [a | a <- xs, a <= x]
      larger = quicksort [a | a <- xs, a > x]
  in smaller ++ [x] ++ larger

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
merge (x:xs) (y:ys)
  | x <= y = x : merge xs (y:ys)
  | otherwise = y : merge (x:xs) ys

-- 深度优先搜索
dfs :: Eq a => (a -> [a]) -> a -> [a]
dfs neighbors start = go [start] []
  where
    go [] visited = visited
    go (x:xs) visited
      | x `elem` visited = go xs visited
      | otherwise = go (neighbors x ++ xs) (x:visited)
```

### 数据结构操作

```haskell
-- 二叉树操作
data BinaryTree a = Empty | Node a (BinaryTree a) (BinaryTree a)

-- 中序遍历
inorder :: BinaryTree a -> [a]
inorder Empty = []
inorder (Node x left right) = inorder left ++ [x] ++ inorder right

-- 前序遍历
preorder :: BinaryTree a -> [a]
preorder Empty = []
preorder (Node x left right) = [x] ++ preorder left ++ preorder right

-- 后序遍历
postorder :: BinaryTree a -> [a]
postorder Empty = []
postorder (Node x left right) = postorder left ++ postorder right ++ [x]

-- 树的高度
treeHeight :: BinaryTree a -> Int
treeHeight Empty = 0
treeHeight (Node _ left right) = 1 + max (treeHeight left) (treeHeight right)
```

### 业务逻辑

```haskell
-- 文件系统遍历
data FileSystem = File String | Directory String [FileSystem]

-- 计算文件大小
fileSize :: FileSystem -> Int
fileSize (File _) = 1
fileSize (Directory _ children) = sum (map fileSize children)

-- 查找文件
findFile :: String -> FileSystem -> Maybe FileSystem
findFile name (File fname)
  | fname == name = Just (File fname)
  | otherwise = Nothing
findFile name (Directory dname children) =
  case findFile name (File dname) of
    Just file -> Just file
    Nothing -> foldr (<|>) Nothing (map (findFile name) children)

-- 权限检查递归
data Permission = Read | Write | Execute

checkPermissions :: [Permission] -> FileSystem -> Bool
checkPermissions perms (File _) = Read `elem` perms
checkPermissions perms (Directory _ children) =
  all (checkPermissions perms) children
```

## 总结

Haskell的递归函数提供了：

1. **数学基础**：基于数学归纳法和不动点理论
2. **类型安全**：编译时检查确保递归正确性
3. **性能优化**：尾递归优化和记忆化
4. **惰性求值**：支持无限数据结构
5. **组合性**：易于与其他函数式构造组合

递归函数是Haskell中实现复杂算法和数据结构操作的核心工具，体现了函数式编程的优雅和强大。

---

**相关链接**：

- [函数式编程基础](../01-Basic-Concepts/函数式编程基础.md)
- [条件表达式](./01-Conditional-Expressions.md)
- [高阶函数](./03-Higher-Order-Functions.md)
