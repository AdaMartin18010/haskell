# Haskell函数式编程基础

## 🎯 概述

函数式编程是一种编程范式，强调使用函数作为主要的计算单元。Haskell作为纯函数式编程语言的代表，提供了强大的类型系统、惰性求值和不可变性等特性。本文档从数学基础、语言特性到实际应用全面介绍Haskell函数式编程。

## 📚 快速导航

### 相关理论

- [类型系统](../04-Type-System/001-Type-System-Foundation.md)
- [模式匹配](./002-Pattern-Matching.md)
- [高阶函数](./004-Higher-Order-Functions.md)

### 实现示例

- [数据结构](../06-Data-Structures/001-Basic-Data-Structures.md)
- [算法实现](../07-Algorithms/001-Sorting-Algorithms.md)

### 应用领域

- [Web开发](../11-Web-Development/001-Web-Development-Foundation.md)
- [系统编程](../12-System-Programming/001-System-Programming-Foundation.md)

## 📖 1. 函数式编程数学基础

### 1.1 函数定义

**定义 1.1 (函数)**
函数 $f: A \rightarrow B$ 是从集合 $A$ 到集合 $B$ 的映射，满足：
$$\forall a \in A, \exists! b \in B: f(a) = b$$

**定义 1.2 (纯函数)**
纯函数 $f$ 满足：

1. **确定性**：相同输入总是产生相同输出
2. **无副作用**：不修改外部状态
3. **引用透明性**：函数调用可以用其返回值替换

**定理 1.1 (函数组合)**
对于函数 $f: A \rightarrow B$ 和 $g: B \rightarrow C$，组合函数 $g \circ f: A \rightarrow C$ 定义为：
$$(g \circ f)(a) = g(f(a))$$

**证明：** 通过函数定义直接验证：

1. 对于任意 $a \in A$，$f(a) \in B$
2. 对于任意 $b \in B$，$g(b) \in C$
3. 因此 $(g \circ f)(a) = g(f(a)) \in C$

```haskell
-- 函数类型定义
type Function a b = a -> b

-- 函数组合
(.) :: (b -> c) -> (a -> b) -> (a -> c)
(.) g f = \x -> g (f x)

-- 纯函数示例
add :: Num a => a -> a -> a
add x y = x + y

multiply :: Num a => a -> a -> a
multiply x y = x * y

-- 函数组合示例
addThenMultiply :: Num a => a -> a -> a -> a
addThenMultiply x y z = multiply (add x y) z

-- 使用函数组合操作符
addThenMultiply' :: Num a => a -> a -> a -> a
addThenMultiply' x y = multiply (add x y)
```

### 1.2 不可变性

**定义 1.3 (不可变性)**
在函数式编程中，数据一旦创建就不能被修改，只能通过创建新的数据来表示状态变化。

**定理 1.2 (不可变性优势)**
不可变性提供以下优势：

1. **线程安全**：无需锁机制
2. **可预测性**：状态变化明确
3. **可测试性**：函数行为独立

```haskell
-- 不可变数据结构
data ImmutableList a = Nil | Cons a (ImmutableList a)

-- 添加元素（创建新列表）
addElement :: a -> ImmutableList a -> ImmutableList a
addElement x xs = Cons x xs

-- 删除元素（创建新列表）
removeElement :: Eq a => a -> ImmutableList a -> ImmutableList a
removeElement _ Nil = Nil
removeElement x (Cons y ys)
  | x == y = ys
  | otherwise = Cons y (removeElement x ys)

-- 示例使用
exampleList :: ImmutableList Int
exampleList = Cons 1 (Cons 2 (Cons 3 Nil))

newList :: ImmutableList Int
newList = addElement 0 exampleList  -- 原列表不变
```

### 1.3 惰性求值

**定义 1.4 (惰性求值)**
惰性求值是一种求值策略，只在需要时才计算表达式的值。

**定理 1.3 (惰性求值性质)**
惰性求值具有以下性质：

1. **按需计算**：只在需要时计算
2. **无限数据结构**：可以表示无限序列
3. **记忆化**：相同表达式只计算一次

```haskell
-- 无限列表
infiniteList :: [Integer]
infiniteList = [1..]

-- 惰性求值示例
takeFirst :: Int -> [a] -> [a]
takeFirst 0 _ = []
takeFirst _ [] = []
takeFirst n (x:xs) = x : takeFirst (n-1) xs

-- 使用无限列表
firstTen :: [Integer]
firstTen = takeFirst 10 infiniteList  -- 只计算前10个元素

-- 斐波那契数列（惰性实现）
fibonacci :: [Integer]
fibonacci = 0 : 1 : zipWith (+) fibonacci (tail fibonacci)

-- 获取第n个斐波那契数
fib :: Int -> Integer
fib n = fibonacci !! n
```

## 🔧 2. Haskell语言特性

### 2.1 类型系统

**定义 2.1 (类型)**
类型是值的集合，用于分类和约束数据。

**定义 2.2 (类型签名)**
函数类型签名 $f :: A \rightarrow B$ 表示函数 $f$ 接受类型 $A$ 的输入，返回类型 $B$ 的输出。

```haskell
-- 基本类型
type Int = Integer
type Double = Double
type Char = Char
type Bool = Bool

-- 函数类型
type FunctionType = Int -> Int -> Int

-- 类型别名
type Point = (Double, Double)
type Name = String
type Age = Int

-- 函数类型签名
add :: Int -> Int -> Int
add x y = x + y

distance :: Point -> Point -> Double
distance (x1, y1) (x2, y2) = sqrt ((x2 - x1)^2 + (y2 - y1)^2)
```

### 2.2 模式匹配

**定义 2.3 (模式匹配)**
模式匹配是一种解构数据结构的方法，根据数据形状选择不同的计算路径。

```haskell
-- 列表模式匹配
listLength :: [a] -> Int
listLength [] = 0
listLength (_:xs) = 1 + listLength xs

-- 元组模式匹配
swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

-- 自定义数据类型模式匹配
data Tree a = Empty | Node a (Tree a) (Tree a)

treeSize :: Tree a -> Int
treeSize Empty = 0
treeSize (Node _ left right) = 1 + treeSize left + treeSize right

-- 守卫表达式
absolute :: (Num a, Ord a) => a -> a
absolute x
  | x >= 0 = x
  | otherwise = -x
```

### 2.3 递归

**定义 2.4 (递归)**
递归是函数调用自身的过程，是函数式编程的核心控制结构。

**定理 2.1 (递归终止性)**
递归函数必须满足：

1. **基本情况**：存在不递归调用的分支
2. **递归情况**：每次递归调用都向基本情况收敛

```haskell
-- 递归函数示例

-- 阶乘函数
factorial :: Integer -> Integer
factorial 0 = 1
factorial n = n * factorial (n - 1)

-- 快速排序
quicksort :: Ord a => [a] -> [a]
quicksort [] = []
quicksort (x:xs) = 
  let smaller = quicksort [a | a <- xs, a <= x]
      larger = quicksort [a | a <- xs, a > x]
  in smaller ++ [x] ++ larger

-- 二叉树遍历
inorder :: Tree a -> [a]
inorder Empty = []
inorder (Node x left right) = inorder left ++ [x] ++ inorder right
```

## 🎯 3. 函数式编程模式

### 3.1 高阶函数

**定义 3.1 (高阶函数)**
高阶函数是接受函数作为参数或返回函数的函数。

```haskell
-- map函数
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs

-- filter函数
filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs)
  | p x = x : filter p xs
  | otherwise = filter p xs

-- fold函数
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ z [] = z
foldr f z (x:xs) = f x (foldr f z xs)

-- 高阶函数使用示例
numbers :: [Int]
numbers = [1, 2, 3, 4, 5]

squared :: [Int]
squared = map (^2) numbers

evens :: [Int]
evens = filter even numbers

sum :: [Int]
sum = foldr (+) 0 numbers
```

### 3.2 函数组合

**定义 3.2 (函数组合)**
函数组合是将多个函数连接起来形成新函数的过程。

```haskell
-- 函数组合操作符
(.) :: (b -> c) -> (a -> b) -> (a -> c)
(.) g f = \x -> g (f x)

-- 管道操作符（从左到右）
($>) :: a -> (a -> b) -> b
x $> f = f x

-- 函数组合示例
processData :: [Int] -> Int
processData = filter even . map (^2) . take 10

-- 使用管道操作符
processData' :: [Int] -> Int
processData' xs = xs $> take 10 $> map (^2) $> filter even $> sum
```

### 3.3 部分应用

**定义 3.3 (部分应用)**
部分应用是固定函数的部分参数，创建新的函数。

```haskell
-- 部分应用示例
add :: Int -> Int -> Int
add x y = x + y

-- 部分应用
addFive :: Int -> Int
addFive = add 5

-- 使用部分应用
result :: Int
result = addFive 3  -- 结果为8

-- 更多部分应用示例
multiply :: Int -> Int -> Int
multiply x y = x * y

double :: Int -> Int
double = multiply 2

triple :: Int -> Int
triple = multiply 3
```

## 🔍 4. 函数式编程优势

### 4.1 可读性

**定理 4.1 (函数式可读性)**
函数式代码具有更高的可读性，因为：

1. **声明式**：描述"做什么"而不是"怎么做"
2. **无副作用**：函数行为可预测
3. **组合性**：复杂操作由简单函数组合

```haskell
-- 命令式风格（伪代码）
-- sum = 0
-- for i in numbers:
--     if i % 2 == 0:
--         sum += i * i

-- 函数式风格
sumEvenSquares :: [Int] -> Int
sumEvenSquares = sum . map (^2) . filter even

-- 更清晰的表达
sumEvenSquares' :: [Int] -> Int
sumEvenSquares' numbers = 
  let evenNumbers = filter even numbers
      squaredNumbers = map (^2) evenNumbers
  in sum squaredNumbers
```

### 4.2 可测试性

**定理 4.2 (函数式可测试性)**
函数式代码更容易测试，因为：

1. **纯函数**：相同输入总是相同输出
2. **无状态**：不需要设置复杂的状态
3. **组合性**：可以独立测试每个函数

```haskell
-- 可测试的函数
isPalindrome :: String -> Bool
isPalindrome str = str == reverse str

-- 测试用例
testPalindrome :: Bool
testPalindrome = 
  isPalindrome "racecar" && 
  isPalindrome "anna" && 
  not (isPalindrome "hello")

-- 属性测试
propPalindrome :: String -> Bool
propPalindrome str = 
  isPalindrome str == isPalindrome (reverse str)
```

### 4.3 并发性

**定理 4.3 (函数式并发性)**
函数式代码天然支持并发，因为：

1. **不可变性**：无需锁机制
2. **无副作用**：函数可以安全并行执行
3. **引用透明性**：函数调用可以重排序

```haskell
-- 并发安全的函数
processDataConcurrent :: [Int] -> [Int]
processDataConcurrent = map processItem

processItem :: Int -> Int
processItem x = x * x + 1

-- 可以安全并行执行
-- 因为每个processItem都是纯函数
```

## 🚀 5. 实际应用

### 5.1 数据处理

```haskell
-- 数据处理管道
data Person = Person
  { name :: String
  , age :: Int
  , city :: String
  }

-- 数据处理函数
filterAdults :: [Person] -> [Person]
filterAdults = filter (\p -> age p >= 18)

groupByCity :: [Person] -> [(String, [Person])]
groupByCity = groupBy city

averageAge :: [Person] -> Double
averageAge people = 
  let ages = map age people
      total = sum ages
      count = length ages
  in fromIntegral total / fromIntegral count

-- 完整的数据处理管道
processPeopleData :: [Person] -> [(String, Double)]
processPeopleData = 
  filterAdults .> groupByCity .> map (\(city, people) -> (city, averageAge people))
```

### 5.2 算法实现

```haskell
-- 函数式算法实现

-- 归并排序
merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys)
  | x <= y = x : merge xs (y:ys)
  | otherwise = y : merge (x:xs) ys

mergeSort :: Ord a => [a] -> [a]
mergeSort [] = []
mergeSort [x] = [x]
mergeSort xs = 
  let (left, right) = splitAt (length xs `div` 2) xs
  in merge (mergeSort left) (mergeSort right)

-- 深度优先搜索
dfs :: Eq a => (a -> [a]) -> a -> [a]
dfs neighbors start = dfs' [start] []
  where
    dfs' [] visited = visited
    dfs' (x:xs) visited
      | x `elem` visited = dfs' xs visited
      | otherwise = dfs' (neighbors x ++ xs) (x:visited)
```

## 📊 总结

函数式编程通过纯函数、不可变性和高阶函数等特性，提供了更安全、更可读、更可维护的编程方式。Haskell作为纯函数式编程语言的代表，展示了函数式编程的强大能力和优雅性。

---

**相关文档**：

- [类型系统](../04-Type-System/001-Type-System-Foundation.md)
- [模式匹配](./002-Pattern-Matching.md)
- [高阶函数](./004-Higher-Order-Functions.md)
