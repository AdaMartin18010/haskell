# Haskell函数式编程基础

## 📚 快速导航

### 相关理论

- [类型理论基础](./03-Theory/04-Type-Theory/001-Simple-Type-Theory.md)
- [形式逻辑理论](./02-Formal-Science/02-Formal-Logic/001-Propositional-Logic.md)
- [范畴论基础](./02-Formal-Science/03-Category-Theory/001-Basic-Concepts.md)

### 实现示例

- [模式匹配](./haskell/01-Basic-Concepts/002-Pattern-Matching.md)
- [递归和列表](./haskell/01-Basic-Concepts/003-Recursion-and-Lists.md)
- [高阶函数](./haskell/01-Basic-Concepts/004-Higher-Order-Functions.md)

### 应用领域

- [Web开发](./haskell/11-Web-Development/001-Web-Development-Foundation.md)
- [系统编程](./haskell/12-System-Programming/001-System-Programming-Foundation.md)
- [科学计算](./haskell/14-Real-World-Applications/002-Scientific-Computing.md)

## 🎯 概述

函数式编程是一种编程范式，它将计算视为数学函数的求值，避免状态和可变数据。Haskell作为纯函数式编程语言的代表，提供了强大的类型系统、惰性求值和高级抽象能力。

## 📖 1. 函数式编程核心概念

### 1.1 纯函数

**定义 1.1 (纯函数)**
纯函数是满足以下条件的函数：

1. **引用透明性**：对于相同的输入，总是产生相同的输出
2. **无副作用**：不修改外部状态或产生可观察的副作用
3. **确定性**：结果完全由输入决定

**数学定义：**
$$f : A \rightarrow B$$

其中 $f$ 是纯函数，$A$ 是输入类型，$B$ 是输出类型。

**Haskell实现：**

```haskell
-- 纯函数示例
add :: Int -> Int -> Int
add x y = x + y

multiply :: Int -> Int -> Int
multiply x y = x * y

-- 非纯函数示例（在IO中）
getCurrentTime :: IO UTCTime
getCurrentTime = getCurrentTime  -- 有副作用，每次调用结果不同
```

### 1.2 不可变性

**定义 1.2 (不可变性)**
在函数式编程中，数据一旦创建就不能被修改，只能通过创建新的数据来表示变化。

**数学基础：**
$$\forall x \in A, f(x) \neq x \Rightarrow f(x) \text{ 创建新值}$$

**Haskell实现：**

```haskell
-- 不可变列表操作
originalList :: [Int]
originalList = [1, 2, 3, 4, 5]

-- 添加元素（创建新列表）
newList :: [Int]
newList = 0 : originalList  -- [0, 1, 2, 3, 4, 5]

-- 原始列表保持不变
-- originalList 仍然是 [1, 2, 3, 4, 5]

-- 不可变记录
data Person = Person
  { name :: String
  , age :: Int
  } deriving (Show, Eq)

-- 更新记录（创建新记录）
updateAge :: Person -> Int -> Person
updateAge person newAge = person { age = newAge }

-- 原始记录保持不变
originalPerson :: Person
originalPerson = Person "Alice" 25

updatedPerson :: Person
updatedPerson = updateAge originalPerson 26
-- originalPerson 仍然是 Person "Alice" 25
```

### 1.3 高阶函数

**定义 1.3 (高阶函数)**
高阶函数是接受函数作为参数或返回函数作为结果的函数。

**数学定义：**
$$H : (A \rightarrow B) \rightarrow (C \rightarrow D)$$

**Haskell实现：**

```haskell
-- 高阶函数示例
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs

filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs)
  | p x = x : filter p xs
  | otherwise = filter p xs

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ acc [] = acc
foldr f acc (x:xs) = f x (foldr f acc xs)

-- 函数组合
(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

-- 部分应用
add :: Int -> Int -> Int
add x y = x + y

addFive :: Int -> Int
addFive = add 5  -- 部分应用
```

## 🔧 2. 类型系统基础

### 2.1 静态类型系统

**定义 2.1 (静态类型)**
Haskell使用静态类型系统，所有类型在编译时确定。

**类型推断：**
$$\frac{\Gamma \vdash e_1 : \tau_1 \rightarrow \tau_2 \quad \Gamma \vdash e_2 : \tau_1}{\Gamma \vdash e_1 e_2 : \tau_2}$$

**Haskell实现：**

```haskell
-- 显式类型注解
explicitFunction :: Int -> String -> Bool
explicitFunction x str = x > 0 && length str > 0

-- 类型推断
inferredFunction x y = x + y  -- 推断为 Num a => a -> a -> a

-- 多态类型
identity :: a -> a
identity x = x

-- 类型约束
sumList :: Num a => [a] -> a
sumList [] = 0
sumList (x:xs) = x + sumList xs
```

### 2.2 代数数据类型

**定义 2.2 (代数数据类型)**
代数数据类型是通过和类型（sum）和积类型（product）构造的复合类型。

**数学定义：**
$$\text{ADT} = \sum_{i=1}^{n} \prod_{j=1}^{m_i} T_{i,j}$$

**Haskell实现：**

```haskell
-- 积类型（记录）
data Point = Point
  { x :: Double
  , y :: Double
  } deriving (Show, Eq)

-- 和类型（枚举）
data Shape
  = Circle Double
  | Rectangle Double Double
  | Triangle Double Double Double
  deriving (Show, Eq)

-- 递归类型
data Tree a
  = Leaf
  | Node a (Tree a) (Tree a)
  deriving (Show, Eq)

-- 参数化类型
data Maybe a
  = Nothing
  | Just a
  deriving (Show, Eq)

data Either a b
  = Left a
  | Right b
  deriving (Show, Eq)
```

### 2.3 类型类

**定义 2.3 (类型类)**
类型类是Haskell的接口系统，定义了类型必须实现的操作。

**数学基础：**
$$\text{TypeClass} = \{ \text{methods} : \text{Type} \rightarrow \text{Type} \}$$

**Haskell实现：**

```haskell
-- 基本类型类
class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool
  x /= y = not (x == y)

class Ord a where
  compare :: a -> a -> Ordering
  (<) :: a -> a -> Bool
  (<=) :: a -> a -> Bool
  (>) :: a -> a -> Bool
  (>=) :: a -> a -> Bool
  max :: a -> a -> a
  min :: a -> a -> a

class Show a where
  show :: a -> String

-- 数值类型类
class Num a where
  (+) :: a -> a -> a
  (-) :: a -> a -> a
  (*) :: a -> a -> a
  negate :: a -> a
  abs :: a -> a
  signum :: a -> a
  fromInteger :: Integer -> a

-- 自定义类型类
class Printable a where
  printValue :: a -> String
  printValue = show  -- 默认实现

-- 类型类实例
instance Eq Point where
  (Point x1 y1) == (Point x2 y2) = x1 == x2 && y1 == y2

instance Show Point where
  show (Point x y) = "Point (" ++ show x ++ ", " ++ show y ++ ")"

instance Printable Point where
  printValue = show
```

## 📊 3. 惰性求值

### 3.1 惰性求值原理

**定义 3.1 (惰性求值)**
惰性求值是一种求值策略，只在需要时才计算表达式的值。

**数学基础：**
$$\text{thunk} : \text{Expression} \rightarrow \text{Value}$$

**Haskell实现：**

```haskell
-- 惰性列表
infiniteList :: [Integer]
infiniteList = [1..]  -- 不会立即计算所有元素

-- 惰性求值示例
takeFirst :: Int -> [a] -> [a]
takeFirst 0 _ = []
takeFirst _ [] = []
takeFirst n (x:xs) = x : takeFirst (n-1) xs

-- 只计算需要的部分
firstFive :: [Integer]
firstFive = takeFirst 5 infiniteList  -- 只计算前5个元素

-- 惰性函数
lazyFunction :: Int -> Int
lazyFunction x = expensiveComputation x
  where
    expensiveComputation n = sum [1..n]  -- 只在需要时计算
```

### 3.2 记忆化

**定义 3.2 (记忆化)**
记忆化是缓存函数计算结果的技术，避免重复计算。

**数学定义：**
$$memo(f)(x) = \begin{cases}
f(x) & \text{if } x \notin \text{cache} \\
\text{cache}[x] & \text{if } x \in \text{cache}
\end{cases}$$

**Haskell实现：**
```haskell
-- 简单记忆化
memoize :: (Int -> a) -> Int -> a
memoize f = let cache = map f [0..] in (cache !!)

-- 斐波那契数列记忆化
fib :: Int -> Integer
fib = memoize fib'
  where
    fib' 0 = 0
    fib' 1 = 1
    fib' n = fib (n-1) + fib (n-2)

-- 使用Data.MemoTrie进行记忆化
import Data.MemoTrie

memoizedFunction :: (Int, Int) -> Int
memoizedFunction = memo (\(x, y) -> x + y)
```

## 🎯 4. 函数式编程模式

### 4.1 函数组合

**定义 4.1 (函数组合)**
函数组合是将多个函数连接起来形成新函数的技术。

**数学定义：**
$$(f \circ g)(x) = f(g(x))$$

**Haskell实现：**
```haskell
-- 函数组合操作符
(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

-- 函数组合示例
addOne :: Int -> Int
addOne = (+1)

multiplyByTwo :: Int -> Int
multiplyByTwo = (*2)

addOneThenMultiply :: Int -> Int
addOneThenMultiply = multiplyByTwo . addOne

-- 管道操作符
(|>) :: a -> (a -> b) -> b
x |> f = f x

-- 使用管道
result :: Int
result = 5 |> addOne |> multiplyByTwo  -- 结果为 12
```

### 4.2 柯里化

**定义 4.2 (柯里化)**
柯里化是将接受多个参数的函数转换为接受单个参数的函数序列。

**数学定义：**
$$\text{curry} : (A \times B \rightarrow C) \rightarrow (A \rightarrow (B \rightarrow C))$$

**Haskell实现：**
```haskell
-- 柯里化函数
curry :: ((a, b) -> c) -> a -> b -> c
curry f a b = f (a, b)

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f (a, b) = f a b

-- 柯里化示例
add :: Int -> Int -> Int
add x y = x + y

addFive :: Int -> Int
addFive = add 5  -- 部分应用

-- 使用柯里化
mapAddFive :: [Int] -> [Int]
mapAddFive = map addFive

-- 等价于
mapAddFive' :: [Int] -> [Int]
mapAddFive' = map (add 5)
```

### 4.3 函子

**定义 4.3 (函子)**
函子是保持函数结构的类型构造子。

**数学定义：**
$$\text{Functor} : \text{Type} \rightarrow \text{Type}$$

**函子定律：**
1. $fmap\ id = id$
2. $fmap\ (f \circ g) = fmap\ f \circ fmap\ g$

**Haskell实现：**
```haskell
class Functor f where
  fmap :: (a -> b) -> f a -> f b

-- Maybe函子
instance Functor Maybe where
  fmap _ Nothing = Nothing
  fmap f (Just x) = Just (f x)

-- 列表函子
instance Functor [] where
  fmap = map

-- Either函子
instance Functor (Either a) where
  fmap _ (Left x) = Left x
  fmap f (Right y) = Right (f y)

-- 函子使用示例
maybeAddOne :: Maybe Int -> Maybe Int
maybeAddOne = fmap (+1)

listAddOne :: [Int] -> [Int]
listAddOne = fmap (+1)
```

## 🚀 5. 实际应用

### 5.1 数据处理

```haskell
-- 数据处理管道
processData :: [String] -> [Int]
processData = filter (not . null)  -- 过滤空字符串
           . map read              -- 转换为数字
           . filter (> 0)          -- 过滤正数
           . map (* 2)             -- 乘以2

-- 使用管道操作符
processData' :: [String] -> [Int]
processData' = filter (not . null)
            |> map read
            |> filter (> 0)
            |> map (* 2)

-- 错误处理
safeRead :: String -> Maybe Int
safeRead str = case reads str of
  [(n, "")] -> Just n
  _ -> Nothing

processDataSafe :: [String] -> [Int]
processDataSafe = mapMaybe safeRead
               . filter (not . null)
               . filter (> 0)
               . map (* 2)
```

### 5.2 配置管理

```haskell
-- 配置数据类型
data Config = Config
  { databaseUrl :: String
  , port :: Int
  , debug :: Bool
  } deriving (Show, Eq)

-- 默认配置
defaultConfig :: Config
defaultConfig = Config
  { databaseUrl = "localhost:5432"
  , port = 8080
  , debug = False
  }

-- 配置更新函数
updateDatabaseUrl :: String -> Config -> Config
updateDatabaseUrl url config = config { databaseUrl = url }

updatePort :: Int -> Config -> Config
updatePort newPort config = config { port = newPort }

-- 配置组合
updateConfig :: String -> Int -> Config -> Config
updateConfig url port = updateDatabaseUrl url . updatePort port
```

### 5.3 状态管理

```haskell
-- 状态类型
data GameState = GameState
  { playerHealth :: Int
  , playerScore :: Int
  , gameLevel :: Int
  } deriving (Show, Eq)

-- 初始状态
initialState :: GameState
initialState = GameState
  { playerHealth = 100
  , playerScore = 0
  , gameLevel = 1
  }

-- 状态更新函数
takeDamage :: Int -> GameState -> GameState
takeDamage damage state = state { playerHealth = max 0 (playerHealth state - damage) }

addScore :: Int -> GameState -> GameState
addScore points state = state { playerScore = playerScore state + points }

levelUp :: GameState -> GameState
levelUp state = state { gameLevel = gameLevel state + 1 }

-- 状态转换
gameAction :: GameState -> GameState
gameAction = takeDamage 10 . addScore 100 . levelUp
```

## 📈 6. 性能优化

### 6.1 严格求值

```haskell
-- 严格求值
{-# LANGUAGE BangPatterns #-}

strictSum :: [Int] -> Int
strictSum = go 0
  where
    go !acc [] = acc
    go !acc (x:xs) = go (acc + x) xs

-- 严格数据类型
data StrictList a = StrictList !a !(StrictList a) | StrictNil

-- 严格字段
data StrictPoint = StrictPoint
  { strictX :: !Double
  , strictY :: !Double
  }
```

### 6.2 空间优化

```haskell
-- 尾递归优化
tailRecursiveSum :: [Int] -> Int
tailRecursiveSum = go 0
  where
    go acc [] = acc
    go acc (x:xs) = go (acc + x) xs

-- 使用foldl'进行严格折叠
import Data.List (foldl')

strictFoldSum :: [Int] -> Int
strictFoldSum = foldl' (+) 0
```

## 🎯 总结

Haskell函数式编程提供了：

1. **纯函数**：确保程序的可预测性和可测试性
2. **不可变性**：避免状态相关的错误
3. **高阶函数**：提供强大的抽象能力
4. **类型安全**：在编译时捕获错误
5. **惰性求值**：提高程序效率
6. **函数组合**：构建模块化程序

这些特性使得Haskell成为构建可靠、高效和可维护软件的强大工具。

---

**相关文档**:
- [模式匹配](./haskell/01-Basic-Concepts/002-Pattern-Matching.md)
- [递归和列表](./haskell/01-Basic-Concepts/003-Recursion-and-Lists.md)
- [高阶函数](./haskell/01-Basic-Concepts/004-Higher-Order-Functions.md)

**实现示例**:
- [类型系统基础](./haskell/04-Type-System/001-Type-System-Foundation.md)
- [设计模式](./haskell/05-Design-Patterns/001-Functional-Design-Patterns.md)
