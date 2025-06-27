# Haskell函数式编程基础模式

## 🎯 概述

本文档详细介绍Haskell函数式编程的基础模式，包括纯函数、高阶函数、函数组合、模式匹配等核心概念。这些基础模式是构建更复杂函数式设计模式的基础。

## 📊 核心概念

### 1. 纯函数模式 (Pure Function Pattern)

#### 1.1 纯函数定义

```haskell
-- 纯函数：相同输入总是产生相同输出，无副作用
add :: Int -> Int -> Int
add x y = x + y

-- 非纯函数：有副作用
getCurrentTime :: IO UTCTime
getCurrentTime = getCurrentTime

-- 纯函数示例
square :: Num a => a -> a
square x = x * x

factorial :: Integer -> Integer
factorial 0 = 1
factorial n = n * factorial (n - 1)
```

#### 1.2 纯函数的优势

```haskell
-- 可测试性
testAdd :: Bool
testAdd = add 2 3 == 5 && add (-1) 1 == 0

-- 可组合性
composedFunction :: Int -> Int
composedFunction = square . add 1

-- 可并行性
parallelComputation :: [Int] -> [Int]
parallelComputation = map square
```

### 2. 高阶函数模式 (Higher-Order Function Pattern)

#### 2.1 函数作为参数

```haskell
-- 高阶函数：接受函数作为参数
applyTwice :: (a -> a) -> a -> a
applyTwice f x = f (f x)

-- 使用示例
double :: Num a => a -> a
double x = x * 2

result :: Int
result = applyTwice double 3  -- 结果：12

-- 更复杂的高阶函数
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs

filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs)
    | p x = x : filter p xs
    | otherwise = filter p xs
```

#### 2.2 函数作为返回值

```haskell
-- 返回函数的函数
makeAdder :: Int -> (Int -> Int)
makeAdder x = \y -> x + y

-- 使用示例
addFive :: Int -> Int
addFive = makeAdder 5

result1 :: Int
result1 = addFive 3  -- 结果：8

-- 柯里化
curriedAdd :: Int -> Int -> Int
curriedAdd x y = x + y

partialAdd :: Int -> Int
partialAdd = curriedAdd 10
```

### 3. 函数组合模式 (Function Composition Pattern)

#### 3.1 基础函数组合

```haskell
-- 函数组合操作符
(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

-- 组合示例
composedFunction :: Int -> Int
composedFunction = square . double

-- 多函数组合
complexComposition :: Int -> Int
complexComposition = square . double . add 1

-- 管道风格（使用 $ 操作符）
pipelineStyle :: Int -> Int
pipelineStyle x = square $ double $ add 1 x
```

#### 3.2 高级函数组合

```haskell
-- 函数组合的代数性质
-- 结合律：(f . g) . h = f . (g . h)
-- 单位元：id . f = f . id = f

-- 使用 id 函数
id :: a -> a
id x = x

-- 组合的恒等性
identityComposition :: Int -> Int
identityComposition = id . square . id

-- 多参数函数的组合
composeWithMultipleArgs :: Int -> Int -> Int
composeWithMultipleArgs = (.) square . (+)
```

### 4. 模式匹配模式 (Pattern Matching Pattern)

#### 4.1 基础模式匹配

```haskell
-- 代数数据类型的模式匹配
data Shape = Circle Double | Rectangle Double Double

area :: Shape -> Double
area (Circle r) = pi * r * r
area (Rectangle w h) = w * h

-- 列表模式匹配
listLength :: [a] -> Int
listLength [] = 0
listLength (_:xs) = 1 + listLength xs

-- 元组模式匹配
swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)
```

#### 4.2 高级模式匹配

```haskell
-- 嵌套模式匹配
data Tree a = Leaf a | Node (Tree a) (Tree a)

treeDepth :: Tree a -> Int
treeDepth (Leaf _) = 0
treeDepth (Node left right) = 1 + max (treeDepth left) (treeDepth right)

-- 守卫表达式
absolute :: (Ord a, Num a) => a -> a
absolute x
    | x < 0 = -x
    | otherwise = x

-- 模式匹配与函数组合
processList :: [Int] -> [Int]
processList [] = []
processList (x:xs) = if x > 0 then x : processList xs else processList xs
```

### 5. 递归模式 (Recursion Pattern)

#### 5.1 基础递归

```haskell
-- 简单递归
factorial :: Integer -> Integer
factorial 0 = 1
factorial n = n * factorial (n - 1)

-- 列表递归
sumList :: Num a => [a] -> a
sumList [] = 0
sumList (x:xs) = x + sumList xs

-- 树递归
treeSum :: Num a => Tree a -> a
treeSum (Leaf x) = x
treeSum (Node left right) = treeSum left + treeSum right
```

#### 5.2 尾递归优化

```haskell
-- 尾递归版本
factorialTail :: Integer -> Integer
factorialTail n = go n 1
  where
    go 0 acc = acc
    go n acc = go (n - 1) (n * acc)

-- 尾递归列表处理
reverseTail :: [a] -> [a]
reverseTail xs = go xs []
  where
    go [] acc = acc
    go (x:xs) acc = go xs (x:acc)
```

### 6. 不可变性模式 (Immutability Pattern)

#### 6.1 不可变数据结构

```haskell
-- 不可变列表操作
addToList :: a -> [a] -> [a]
addToList x xs = x : xs  -- 创建新列表，不修改原列表

-- 不可变记录更新
data Person = Person { name :: String, age :: Int }

updateAge :: Person -> Int -> Person
updateAge person newAge = person { age = newAge }

-- 不可变树更新
updateLeaf :: Tree a -> a -> Tree a
updateLeaf (Leaf _) newValue = Leaf newValue
updateLeaf (Node left right) newValue = Node left right
```

#### 6.2 不可变性的优势

```haskell
-- 线程安全
safeIncrement :: Int -> Int
safeIncrement x = x + 1

-- 可预测性
predictableFunction :: Int -> Int
predictableFunction x = square (add 1 x)

-- 可缓存性
memoizedFactorial :: Integer -> Integer
memoizedFactorial = memoize factorial
  where
    memoize f = let cache = Map.empty in f
```

### 7. 类型安全模式 (Type Safety Pattern)

#### 7.1 强类型系统

```haskell
-- 类型安全的函数
safeDivide :: Double -> Double -> Maybe Double
safeDivide _ 0 = Nothing
safeDivide x y = Just (x / y)

-- 类型安全的列表操作
safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x

-- 类型安全的错误处理
data Result a = Success a | Error String

safeOperation :: Int -> Result Int
safeOperation x
    | x < 0 = Error "Negative number"
    | otherwise = Success (x * 2)
```

#### 7.2 类型约束

```haskell
-- 类型类约束
sumNumbers :: Num a => [a] -> a
sumNumbers = foldr (+) 0

-- 多类型类约束
compareAndShow :: (Ord a, Show a) => a -> a -> String
compareAndShow x y
    | x < y = show x ++ " < " ++ show y
    | x > y = show x ++ " > " ++ show y
    | otherwise = show x ++ " == " ++ show y
```

## 🎯 模式组合示例

### 1. 函数式管道

```haskell
-- 构建数据处理管道
dataProcessingPipeline :: [Int] -> [Int]
dataProcessingPipeline = 
    filter (> 0) .           -- 过滤正数
    map (* 2) .              -- 每个数乘以2
    map square .             -- 每个数平方
    filter (> 10)            -- 过滤大于10的数

-- 使用示例
example :: [Int]
example = dataProcessingPipeline [-2, 1, 3, 5, 7]
-- 结果：[16, 36, 100, 196]
```

### 2. 递归数据结构处理

```haskell
-- 处理嵌套数据结构
data NestedList a = Elem a | List [NestedList a]

flatten :: NestedList a -> [a]
flatten (Elem x) = [x]
flatten (List xs) = concatMap flatten xs

-- 使用示例
nestedExample :: NestedList Int
nestedExample = List [Elem 1, List [Elem 2, Elem 3], Elem 4]

flattened :: [Int]
flattened = flatten nestedExample  -- 结果：[1, 2, 3, 4]
```

### 3. 高阶函数组合

```haskell
-- 构建可配置的处理函数
buildProcessor :: (a -> Bool) -> (a -> b) -> [a] -> [b]
buildProcessor filterFn mapFn = map mapFn . filter filterFn

-- 使用示例
positiveDoubles :: [Int] -> [Int]
positiveDoubles = buildProcessor (> 0) (* 2)

result :: [Int]
result = positiveDoubles [-1, 2, -3, 4]  -- 结果：[4, 8]
```

## 📊 性能优化指南

### 1. 惰性求值优化

```haskell
-- 利用惰性求值
infiniteList :: [Integer]
infiniteList = [1..]

-- 只计算需要的部分
takeFirst :: Int -> [a] -> [a]
takeFirst n xs = take n xs

-- 避免不必要的计算
lazyEvaluation :: [Int]
lazyEvaluation = take 5 (map square [1..])
```

### 2. 尾递归优化

```haskell
-- 尾递归版本
efficientSum :: Num a => [a] -> a
efficientSum xs = go xs 0
  where
    go [] acc = acc
    go (x:xs) acc = go xs (acc + x)
```

### 3. 函数组合优化

```haskell
-- 优化函数组合
optimizedPipeline :: [Int] -> [Int]
optimizedPipeline = 
    filter (> 0) .           -- 先过滤，减少后续计算
    map (* 2) .              -- 然后映射
    take 10                  -- 最后限制数量
```

## 🎯 最佳实践

### 1. 函数设计原则

1. **单一职责**：每个函数只做一件事
2. **纯函数优先**：尽可能使用纯函数
3. **类型安全**：利用类型系统防止错误
4. **可组合性**：设计易于组合的函数

### 2. 性能考虑

1. **惰性求值**：利用Haskell的惰性求值特性
2. **尾递归**：对递归函数使用尾递归优化
3. **函数组合**：合理使用函数组合减少中间值
4. **数据结构选择**：选择合适的数据结构

### 3. 代码质量

1. **可读性**：使用清晰的函数名和类型签名
2. **可测试性**：编写易于测试的纯函数
3. **可维护性**：保持代码的简洁和模块化
4. **文档化**：为复杂函数提供清晰的文档

## 🎯 总结

Haskell函数式编程基础模式提供了构建复杂系统的坚实基础。通过深入理解这些模式，可以：

1. **提高代码质量**：利用类型安全和纯函数特性
2. **增强可维护性**：通过不可变性和函数组合
3. **优化性能**：利用惰性求值和尾递归优化
4. **简化并发编程**：利用不可变性和纯函数特性

这些基础模式为学习更高级的函数式设计模式奠定了重要基础。
