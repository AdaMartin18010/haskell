# 函数式编程基础

## 🎯 概述

函数式编程是一种编程范式，它将计算过程视为数学函数的求值，强调使用不可变数据和纯函数。本章介绍函数式编程的核心概念，包括纯函数、不可变性、高阶函数等，并通过Haskell代码示例进行说明。

## 📚 核心概念

### 1. 纯函数 (Pure Functions)

#### 形式化定义

纯函数是一个数学函数 $f: A \rightarrow B$，满足以下条件：

1. **确定性**: 对于相同的输入，总是产生相同的输出
2. **无副作用**: 不修改外部状态，不产生可观察的副作用
3. **引用透明性**: 函数调用可以用其返回值替换，而不改变程序行为

数学表示为：
$$f(x) = y \implies f(x) = y \text{ for all } x \in A$$

#### Haskell实现

```haskell
-- 纯函数示例
add :: Num a => a -> a -> a
add x y = x + y

-- 这个函数是纯的，因为：
-- 1. 相同输入总是产生相同输出
-- 2. 没有副作用
-- 3. 引用透明

-- 非纯函数示例（在IO单子中）
getCurrentTime :: IO UTCTime
getCurrentTime = getCurrentTime  -- 每次调用结果不同

-- 测试纯函数
testPureFunction :: Bool
testPureFunction = 
    let result1 = add 3 4
        result2 = add 3 4
    in result1 == result2  -- 总是True
```

### 2. 不可变性 (Immutability)

#### 形式化定义

不可变性是指数据结构一旦创建就不能被修改。在函数式编程中，所有数据都是不可变的。

数学表示为：
$$\forall x \in D, \forall f \in F: f(x) \neq x \implies f(x) \text{ is a new value}$$

#### Haskell实现

```haskell
-- 不可变数据结构
data ImmutableList a = Empty | Cons a (ImmutableList a)

-- 创建列表
myList :: ImmutableList Int
myList = Cons 1 (Cons 2 (Cons 3 Empty))

-- 添加元素（创建新列表，不修改原列表）
addElement :: a -> ImmutableList a -> ImmutableList a
addElement x Empty = Cons x Empty
addElement x (Cons y ys) = Cons y (addElement x ys)

-- 原列表保持不变
newList = addElement 4 myList
-- myList仍然是 Cons 1 (Cons 2 (Cons 3 Empty))
-- newList是 Cons 1 (Cons 2 (Cons 3 (Cons 4 Empty)))
```

### 3. 高阶函数 (Higher-Order Functions)

#### 形式化定义

高阶函数是接受函数作为参数或返回函数作为结果的函数。

数学表示为：
$$H: (A \rightarrow B) \rightarrow C \text{ or } H: A \rightarrow (B \rightarrow C)$$

#### Haskell实现

```haskell
-- 高阶函数：接受函数作为参数
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs

-- 高阶函数：返回函数
addN :: Num a => a -> (a -> a)
addN n = \x -> x + n

-- 部分应用
add5 :: Int -> Int
add5 = addN 5

-- 使用高阶函数
doubleList :: [Int] -> [Int]
doubleList = map (*2)

-- 测试
testHigherOrder :: Bool
testHigherOrder = 
    let numbers = [1, 2, 3, 4, 5]
        doubled = doubleList numbers
        added5 = map add5 numbers
    in doubled == [2, 4, 6, 8, 10] && added5 == [6, 7, 8, 9, 10]
```

### 4. 函数组合 (Function Composition)

#### 形式化定义

函数组合是将两个函数 $f: B \rightarrow C$ 和 $g: A \rightarrow B$ 组合成一个新函数 $f \circ g: A \rightarrow C$。

数学表示为：
$$(f \circ g)(x) = f(g(x))$$

#### Haskell实现

```haskell
-- 函数组合操作符
(.) :: (b -> c) -> (a -> b) -> a -> c
(f . g) x = f (g x)

-- 示例函数
addOne :: Num a => a -> a
addOne = (+1)

multiplyByTwo :: Num a => a -> a
multiplyByTwo = (*2)

square :: Num a => a -> a
square = (^2)

-- 函数组合
addOneThenDouble :: Num a => a -> a
addOneThenDouble = multiplyByTwo . addOne

addOneThenSquare :: Num a => a -> a
addOneThenSquare = square . addOne

complexFunction :: Num a => a -> a
complexFunction = square . multiplyByTwo . addOne

-- 测试
testComposition :: Bool
testComposition = 
    let x = 3
        result1 = addOneThenDouble x  -- (3+1)*2 = 8
        result2 = addOneThenSquare x  -- (3+1)^2 = 16
        result3 = complexFunction x   -- ((3+1)*2)^2 = 64
    in result1 == 8 && result2 == 16 && result3 == 64
```

### 5. 柯里化 (Currying)

#### 形式化定义

柯里化是将接受多个参数的函数转换为接受单个参数的函数序列的过程。

数学表示为：
$$f: A \times B \rightarrow C \text{ becomes } f': A \rightarrow (B \rightarrow C)$$

#### Haskell实现

```haskell
-- 多参数函数（隐式柯里化）
add :: Num a => a -> a -> a
add x y = x + y

-- 等价于
add' :: Num a => a -> (a -> a)
add' = \x -> \y -> x + y

-- 部分应用
addFive :: Int -> Int
addFive = add 5

-- 测试柯里化
testCurrying :: Bool
testCurrying = 
    let add3and4 = add 3 4
        add3 = add 3
        add3and4' = add3 4
    in add3and4 == 7 && add3and4' == 7
```

### 6. 惰性求值 (Lazy Evaluation)

#### 形式化定义

惰性求值是一种求值策略，只在需要时才计算表达式的值。

数学表示为：
$$\text{eval}(e) = \begin{cases} 
\text{value} & \text{if } e \text{ is needed} \\
\text{unevaluated} & \text{otherwise}
\end{cases}$$

#### Haskell实现

```haskell
-- 惰性求值示例
infiniteList :: [Integer]
infiniteList = [1..]  -- 无限列表，但不会立即计算所有元素

-- 只取前5个元素
takeFive :: [Integer]
takeFive = take 5 infiniteList

-- 惰性求值的好处
expensiveComputation :: Integer -> Integer
expensiveComputation n = 
    let result = sum [1..n]  -- 昂贵的计算
    in trace ("Computing for " ++ show n) result

-- 只有在需要时才计算
lazyExample :: [Integer]
lazyExample = map expensiveComputation [1, 2, 3, 4, 5]

-- 只取前2个元素，只计算前2个
takeTwo :: [Integer]
takeTwo = take 2 lazyExample
```

## 🧮 数学基础

### Lambda演算

函数式编程的理论基础是Lambda演算，它提供了函数的形式化定义。

#### 基本规则

1. **变量**: $x$ 是一个变量
2. **抽象**: $\lambda x.M$ 表示函数，其中 $x$ 是参数，$M$ 是函数体
3. **应用**: $(M N)$ 表示将函数 $M$ 应用于参数 $N$

#### Haskell对应

```haskell
-- Lambda演算在Haskell中的对应
-- 变量
x :: a
x = undefined

-- 抽象 (lambda表达式)
lambdaFunction :: a -> b
lambdaFunction = \x -> undefined

-- 应用
apply :: (a -> b) -> a -> b
apply f x = f x

-- 示例
identity :: a -> a
identity = \x -> x

constant :: a -> b -> a
constant = \x -> \y -> x
```

### 类型理论

Haskell使用Hindley-Milner类型系统，支持类型推断。

#### 类型推断规则

1. **变量**: 如果 $x: \tau$ 在环境中，则 $\Gamma \vdash x: \tau$
2. **抽象**: 如果 $\Gamma, x: \tau_1 \vdash e: \tau_2$，则 $\Gamma \vdash \lambda x.e: \tau_1 \rightarrow \tau_2$
3. **应用**: 如果 $\Gamma \vdash e_1: \tau_1 \rightarrow \tau_2$ 且 $\Gamma \vdash e_2: \tau_1$，则 $\Gamma \vdash e_1 e_2: \tau_2$

#### Haskell实现

```haskell
-- 类型推断示例
-- Haskell会自动推断类型
autoInfer :: [Int]
autoInfer = [1, 2, 3, 4, 5]

-- 显式类型注解
explicitType :: [Int]
explicitType = [1, 2, 3, 4, 5]

-- 多态类型
polymorphicFunction :: a -> a
polymorphicFunction x = x

-- 类型类约束
constrainedFunction :: (Num a, Ord a) => a -> a -> a
constrainedFunction x y = if x > y then x else y
```

## 🛠️ 实践应用

### 数据处理管道

```haskell
-- 数据处理管道示例
dataProcessingPipeline :: [Int] -> [Int]
dataProcessingPipeline = 
    filter (>0)      -- 过滤正数
    . map (*2)       -- 每个数乘以2
    . take 10        -- 取前10个
    . drop 5         -- 跳过前5个

-- 使用管道
processNumbers :: [Int]
processNumbers = dataProcessingPipeline [1..20]
-- 结果: [12, 14, 16, 18, 20, 22, 24, 26, 28, 30]
```

### 函数式设计模式

```haskell
-- 策略模式（函数式实现）
type Strategy a b = a -> b

applyStrategy :: Strategy a b -> a -> b
applyStrategy strategy input = strategy input

-- 不同的策略
doubleStrategy :: Strategy Int Int
doubleStrategy = (*2)

squareStrategy :: Strategy Int Int
squareStrategy = (^2)

-- 使用策略
useStrategy :: Int -> Int
useStrategy = applyStrategy doubleStrategy
```

## 📊 性能考虑

### 空间复杂度

```haskell
-- 空间效率的列表处理
efficientListProcessing :: [Int] -> [Int]
efficientListProcessing = 
    foldr (\x acc -> if x > 0 then x*2 : acc else acc) []

-- 避免中间列表
avoidIntermediateLists :: [Int] -> Int
avoidIntermediateLists = 
    foldl' (+) 0 . map (*2) . filter (>0)
```

### 时间复杂度

```haskell
-- 高效的查找
efficientLookup :: Eq a => a -> [(a, b)] -> Maybe b
efficientLookup _ [] = Nothing
efficientLookup key ((k, v):xs) = 
    if key == k then Just v else efficientLookup key xs

-- 使用Data.Map进行更高效的查找
import qualified Data.Map as Map

mapLookup :: Ord a => a -> Map.Map a b -> Maybe b
mapLookup key map = Map.lookup key map
```

## 🔗 相关链接

- [Haskell语言特性](02-Haskell-Language-Features.md)
- [类型系统入门](03-Type-System-Introduction.md)
- [高阶函数](05-Higher-Order-Functions.md)
- [控制流](../02-Control-Flow/README.md)
- [数据流](../04-Data-Flow/README.md)

---

**最后更新**: 2024年12月  
**版本**: 1.0.0  
**状态**: 完成 