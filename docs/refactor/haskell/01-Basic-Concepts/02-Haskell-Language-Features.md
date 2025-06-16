# Haskell语言特性

## 🎯 概述

Haskell是一种纯函数式编程语言，具有强大的类型系统、惰性求值、模式匹配等特性。本章详细介绍Haskell的核心语言特性，包括语法、类型系统、高级特性等。

## 📚 核心特性

### 1. 强类型系统 (Strong Type System)

#### 形式化定义

Haskell使用静态强类型系统，每个表达式在编译时都有确定的类型。类型系统基于Hindley-Milner类型推断算法。

数学表示为：
$$\Gamma \vdash e : \tau \text{ where } \tau \text{ is the type of expression } e$$

#### Haskell实现

```haskell
-- 基本类型
intValue :: Int
intValue = 42

doubleValue :: Double
doubleValue = 3.14

charValue :: Char
charValue = 'A'

stringValue :: String
stringValue = "Hello, Haskell!"

boolValue :: Bool
boolValue = True

-- 类型推断
inferredType = 42  -- Haskell推断为 Int
inferredList = [1, 2, 3, 4, 5]  -- Haskell推断为 [Int]

-- 显式类型注解
explicitType :: [Int]
explicitType = [1, 2, 3, 4, 5]
```

### 2. 代数数据类型 (Algebraic Data Types)

#### 形式化定义

代数数据类型是Haskell中定义自定义类型的主要方式，包括乘积类型（记录）和和类型（变体）。

数学表示为：
$$T = C_1 \times T_{11} \times \cdots \times T_{1n_1} + \cdots + C_m \times T_{m1} \times \cdots \times T_{mn_m}$$

#### Haskell实现

```haskell
-- 和类型（变体）
data Shape = Circle Double | Rectangle Double Double | Triangle Double Double Double

-- 乘积类型（记录）
data Person = Person 
    { name :: String
    , age :: Int
    , email :: String
    }

-- 递归类型
data List a = Nil | Cons a (List a)

-- 参数化类型
data Maybe a = Nothing | Just a

data Either a b = Left a | Right b

-- 使用代数数据类型
circle :: Shape
circle = Circle 5.0

rectangle :: Shape
rectangle = Rectangle 3.0 4.0

person :: Person
person = Person "Alice" 30 "alice@example.com"

-- 模式匹配
area :: Shape -> Double
area (Circle r) = pi * r * r
area (Rectangle w h) = w * h
area (Triangle a b c) = sqrt (s * (s - a) * (s - b) * (s - c))
  where s = (a + b + c) / 2
```

### 3. 模式匹配 (Pattern Matching)

#### 形式化定义

模式匹配是函数式编程的核心特性，允许根据数据结构的形式进行条件分支。

数学表示为：
$$f(x) = \begin{cases}
g_1(x) & \text{if } x \text{ matches pattern } p_1 \\
g_2(x) & \text{if } x \text{ matches pattern } p_2 \\
\vdots \\
g_n(x) & \text{if } x \text{ matches pattern } p_n
\end{cases}$$

#### Haskell实现

```haskell
-- 基本模式匹配
factorial :: Integer -> Integer
factorial 0 = 1
factorial n = n * factorial (n - 1)

-- 列表模式匹配
sumList :: [Int] -> Int
sumList [] = 0
sumList (x:xs) = x + sumList xs

-- 元组模式匹配
first :: (a, b) -> a
first (x, _) = x

second :: (a, b) -> b
second (_, y) = y

-- 嵌套模式匹配
nestedPattern :: [(Int, String)] -> [String]
nestedPattern [] = []
nestedPattern ((n, s):xs) = 
    if n > 0 then s : nestedPattern xs else nestedPattern xs

-- 守卫表达式（模式匹配的扩展）
absolute :: (Num a, Ord a) => a -> a
absolute x
    | x < 0 = -x
    | otherwise = x

-- 模式匹配与记录
getAge :: Person -> Int
getAge (Person {age = a}) = a

getName :: Person -> String
getName (Person {name = n}) = n
```

### 4. 类型类 (Type Classes)

#### 形式化定义

类型类是Haskell的接口系统，定义了类型必须实现的操作集合。

数学表示为：
$$C(\tau) \text{ means type } \tau \text{ is an instance of class } C$$

#### Haskell实现

```haskell
-- 类型类定义
class Eq a where
    (==) :: a -> a -> Bool
    (/=) :: a -> a -> Bool
    
    -- 默认实现
    x /= y = not (x == y)

-- 类型类实例
instance Eq Bool where
    True == True = True
    False == False = True
    _ == _ = False

-- 自动派生
data Color = Red | Green | Blue deriving (Eq, Show)

-- 多参数类型类
class Show a => Pretty a where
    pretty :: a -> String
    pretty = show

-- 函数依赖
class Collection c e | c -> e where
    empty :: c
    insert :: e -> c -> c
    member :: e -> c -> Bool

-- 实例实现
instance Collection [a] a where
    empty = []
    insert x xs = x : xs
    member _ [] = False
    member x (y:ys) = x == y || member x ys
```

### 5. 单子 (Monads)

#### 形式化定义

单子是Haskell中处理副作用和顺序计算的核心抽象。单子是一个类型类，定义了三个操作：return、bind和fail。

数学表示为：
$$\text{Monad } M \text{ satisfies: } \text{return}: A \rightarrow M A, \text{bind}: M A \rightarrow (A \rightarrow M B) \rightarrow M B$$

#### Haskell实现

```haskell
-- 单子类型类
class Monad m where
    return :: a -> m a
    (>>=) :: m a -> (a -> m b) -> m b
    (>>) :: m a -> m b -> m b
    fail :: String -> m a

-- Maybe单子
instance Monad Maybe where
    return = Just
    Nothing >>= _ = Nothing
    Just x >>= f = f x
    fail _ = Nothing

-- 列表单子
instance Monad [] where
    return x = [x]
    xs >>= f = concat (map f xs)
    fail _ = []

-- 使用单子
maybeExample :: Maybe Int
maybeExample = do
    x <- Just 5
    y <- Just 3
    return (x + y)

listExample :: [Int]
listExample = do
    x <- [1, 2, 3]
    y <- [10, 20]
    return (x + y)

-- IO单子
ioExample :: IO String
ioExample = do
    putStrLn "Enter your name:"
    name <- getLine
    putStrLn ("Hello, " ++ name ++ "!")
    return name
```

### 6. 函子 (Functors)

#### 形式化定义

函子是保持结构的映射，将函数应用到容器内的值而不改变容器结构。

数学表示为：
$$F: \mathcal{C} \rightarrow \mathcal{D} \text{ with } fmap: (A \rightarrow B) \rightarrow F A \rightarrow F B$$

#### Haskell实现

```haskell
-- 函子类型类
class Functor f where
    fmap :: (a -> b) -> f a -> f b

-- Maybe函子
instance Functor Maybe where
    fmap _ Nothing = Nothing
    fmap f (Just x) = Just (f x)

-- 列表函子
instance Functor [] where
    fmap = map

-- 元组函子（对第二个参数）
instance Functor ((,) a) where
    fmap f (x, y) = (x, f y)

-- 使用函子
maybeFmap :: Maybe Int
maybeFmap = fmap (+1) (Just 5)  -- Just 6

listFmap :: [Int]
listFmap = fmap (*2) [1, 2, 3, 4, 5]  -- [2, 4, 6, 8, 10]

-- 函子定律验证
functorLaws :: Bool
functorLaws = 
    let f = (+1)
        g = (*2)
        x = Just 5
    in fmap id x == x &&  -- 单位律
       fmap (f . g) x == (fmap f . fmap g) x  -- 复合律
```

### 7. 应用函子 (Applicative Functors)

#### 形式化定义

应用函子扩展了函子，允许将包含函数的容器应用到包含值的容器。

数学表示为：
$$\text{pure}: A \rightarrow F A, \text{<*>}: F (A \rightarrow B) \rightarrow F A \rightarrow F B$$

#### Haskell实现

```haskell
-- 应用函子类型类
class Functor f => Applicative f where
    pure :: a -> f a
    (<*>) :: f (a -> b) -> f a -> f b

-- Maybe应用函子
instance Applicative Maybe where
    pure = Just
    Nothing <*> _ = Nothing
    _ <*> Nothing = Nothing
    Just f <*> Just x = Just (f x)

-- 列表应用函子
instance Applicative [] where
    pure x = [x]
    fs <*> xs = [f x | f <- fs, x <- xs]

-- 使用应用函子
maybeApplicative :: Maybe Int
maybeApplicative = pure (+) <*> Just 3 <*> Just 4  -- Just 7

listApplicative :: [Int]
listApplicative = pure (+) <*> [1, 2] <*> [10, 20]  -- [11, 21, 12, 22]

-- 应用函子语法糖
applicativeDo :: Maybe Int
applicativeDo = do
    x <- Just 3
    y <- Just 4
    return (x + y)
```

### 8. 惰性求值 (Lazy Evaluation)

#### 形式化定义

惰性求值是一种求值策略，只在需要时才计算表达式的值。

数学表示为：
$$\text{eval}(e) = \begin{cases} 
\text{value} & \text{if } e \text{ is demanded} \\
\text{thunk} & \text{otherwise}
\end{cases}$$

#### Haskell实现

```haskell
-- 无限数据结构
infiniteList :: [Integer]
infiniteList = [1..]

-- 只计算需要的部分
finiteList :: [Integer]
finiteList = take 5 infiniteList

-- 惰性求值的好处
expensiveComputation :: Integer -> Integer
expensiveComputation n = 
    let result = sum [1..n]
    in trace ("Computing for " ++ show n) result

-- 只有在需要时才计算
lazyComputation :: [Integer]
lazyComputation = map expensiveComputation [1, 2, 3, 4, 5]

-- 只取前2个，只计算前2个
partialResult :: [Integer]
partialResult = take 2 lazyComputation

-- 无限递归数据结构
data InfiniteTree a = Node a (InfiniteTree a) (InfiniteTree a)

-- 创建无限树
infiniteTree :: InfiniteTree Integer
infiniteTree = Node 1 infiniteTree infiniteTree

-- 只访问有限部分
finiteTreeAccess :: Integer
finiteTreeAccess = case infiniteTree of
    Node x _ _ -> x
```

### 9. 类型族 (Type Families)

#### 形式化定义

类型族允许在类型级别进行函数式编程，提供类型级别的计算能力。

数学表示为：
$$F: \kappa_1 \rightarrow \kappa_2 \text{ where } \kappa \text{ are kinds}$$

#### Haskell实现

```haskell
-- 类型族定义
type family Element c :: *

-- 类型族实例
type instance Element [a] = a
type instance Element (Maybe a) = a
type instance Element (Either a b) = a

-- 关联类型族
class Collection c where
    type Elem c :: *
    empty :: c
    insert :: Elem c -> c -> c

-- 实例实现
instance Collection [a] where
    type Elem [a] = a
    empty = []
    insert x xs = x : xs

-- 数据族
data family Array i e

data instance Array Int e = IntArray (Vector e)
data instance Array Bool e = BoolArray (Vector e)

-- 使用类型族
getElement :: Element [Int] -> [Int] -> Element [Int]
getElement _ [] = error "Empty list"
getElement _ (x:_) = x
```

### 10. GADTs (Generalized Algebraic Data Types)

#### 形式化定义

GADTs允许构造函数返回不同的类型，提供类型级别的约束。

数学表示为：
$$C: \tau_1 \rightarrow \cdots \rightarrow \tau_n \rightarrow T \text{ where } T \text{ may vary}$$

#### Haskell实现

```haskell
-- GADT定义
data Expr a where
    LitInt :: Int -> Expr Int
    LitBool :: Bool -> Expr Bool
    Add :: Expr Int -> Expr Int -> Expr Int
    If :: Expr Bool -> Expr a -> Expr a -> Expr a

-- 类型安全的求值
eval :: Expr a -> a
eval (LitInt n) = n
eval (LitBool b) = b
eval (Add e1 e2) = eval e1 + eval e2
eval (If cond e1 e2) = if eval cond then eval e1 else eval e2

-- 使用GADT
exampleExpr :: Expr Int
exampleExpr = If (LitBool True) (Add (LitInt 1) (LitInt 2)) (LitInt 0)

-- 类型安全的表达式构建
safeExpr :: Expr Int
safeExpr = Add (LitInt 5) (LitInt 3)  -- 类型安全
```

## 🛠️ 高级特性

### 1. 模板Haskell (Template Haskell)

```haskell
-- 模板Haskell示例
{-# LANGUAGE TemplateHaskell #-}

-- 生成记录访问器
data Person = Person 
    { name :: String
    , age :: Int
    } deriving Show

-- 使用模板Haskell生成代码
$(deriveJSON defaultOptions ''Person)
```

### 2. 类型级编程

```haskell
-- 类型级自然数
data Zero
data Succ n

-- 类型级加法
type family Add a b :: *
type instance Add Zero b = b
type instance Add (Succ a) b = Succ (Add a b)

-- 类型级向量
data Vec n a where
    Nil :: Vec Zero a
    Cons :: a -> Vec n a -> Vec (Succ n) a

-- 类型安全的向量操作
safeHead :: Vec (Succ n) a -> a
safeHead (Cons x _) = x
```

### 3. 并行和并发

```haskell
-- 并行计算
import Control.Parallel

parallelSum :: [Int] -> Int
parallelSum xs = 
    let (left, right) = splitAt (length xs `div` 2) xs
        leftSum = sum left
        rightSum = sum right
    in leftSum `par` rightSum `pseq` (leftSum + rightSum)

-- 并发计算
import Control.Concurrent

concurrentExample :: IO ()
concurrentExample = do
    threadId1 <- forkIO (putStrLn "Thread 1")
    threadId2 <- forkIO (putStrLn "Thread 2")
    putStrLn "Main thread"
```

## 📊 性能特性

### 1. 严格求值

```haskell
-- 严格求值
strictSum :: [Int] -> Int
strictSum = foldl' (+) 0

-- 严格数据结构
data StrictList a = SNil | SCons !a !(StrictList a)
```

### 2. 内存优化

```haskell
-- 内存效率的列表处理
efficientProcessing :: [Int] -> [Int]
efficientProcessing = 
    foldr (\x acc -> if x > 0 then x*2 : acc else acc) []

-- 避免空间泄漏
avoidSpaceLeak :: [Int] -> Int
avoidSpaceLeak = foldl' (+) 0
```

## 🔗 相关链接

- [函数式编程基础](01-Functional-Programming-Basics.md)
- [类型系统入门](03-Type-System-Introduction.md)
- [模式匹配](04-Pattern-Matching.md)
- [高阶函数](05-Higher-Order-Functions.md)
- [控制流](../02-Control-Flow/README.md)
- [类型体系](../05-Type-System/README.md)

---

**最后更新**: 2024年12月  
**版本**: 1.0.0  
**状态**: 完成 