# 01-Syntax-Basics (Haskell基础语法)

## 概述

Haskell是一种纯函数式编程语言，具有强类型系统、惰性求值和模式匹配等特性。本文档详细介绍Haskell的基础语法，包括表达式、函数定义、数据类型等核心概念。

## 基本语法结构

### 1. 表达式和值

#### 基本表达式

```haskell
-- 字面量
integerLiteral :: Integer
integerLiteral = 42

floatLiteral :: Double
floatLiteral = 3.14159

stringLiteral :: String
stringLiteral = "Hello, Haskell!"

charLiteral :: Char
charLiteral = 'A'

boolLiteral :: Bool
boolLiteral = True

-- 列表
listLiteral :: [Integer]
listLiteral = [1, 2, 3, 4, 5]

-- 元组
tupleLiteral :: (Integer, String, Bool)
tupleLiteral = (42, "answer", True)
```

#### 函数应用

```haskell
-- 函数调用
functionApplication :: Integer
functionApplication = succ 41  -- 结果为42

-- 中缀操作符
infixApplication :: Integer
infixApplication = 2 + 3 * 4  -- 结果为14

-- 前缀操作符
prefixApplication :: Integer
prefixApplication = (+) 2 3   -- 结果为5

-- 函数组合
functionComposition :: Integer -> Integer
functionComposition = succ . (*2)  -- 先乘2，再加1
```

### 2. 函数定义

#### 基本函数定义

```haskell
-- 简单函数
simpleFunction :: Integer -> Integer
simpleFunction x = x + 1

-- 多参数函数
multiParamFunction :: Integer -> Integer -> Integer
multiParamFunction x y = x + y

-- 无参数函数（常量）
constantFunction :: Integer
constantFunction = 42

-- 类型推断
inferredFunction x = x + 1  -- 类型为 Num a => a -> a
```

#### 函数签名

```haskell
-- 显式类型签名
explicitSignature :: Integer -> Integer -> Integer
explicitSignature x y = x + y

-- 多态类型签名
polymorphicSignature :: Num a => a -> a -> a
polymorphicSignature x y = x + y

-- 约束类型签名
constrainedSignature :: (Ord a, Num a) => a -> a -> a
constrainedSignature x y = if x > y then x else y

-- 高阶函数签名
higherOrderSignature :: (a -> b) -> [a] -> [b]
higherOrderSignature f = map f
```

### 3. 模式匹配

#### 基本模式匹配

```haskell
-- 值模式
valuePattern :: Integer -> String
valuePattern 0 = "zero"
valuePattern 1 = "one"
valuePattern 2 = "two"
valuePattern _ = "other"

-- 构造函数模式
constructorPattern :: Maybe Integer -> String
constructorPattern Nothing = "nothing"
constructorPattern (Just x) = "just " ++ show x

-- 列表模式
listPattern :: [Integer] -> String
listPattern [] = "empty"
listPattern [x] = "singleton " ++ show x
listPattern (x:y:xs) = "multiple: " ++ show x ++ ", " ++ show y

-- 元组模式
tuplePattern :: (Integer, String) -> String
tuplePattern (0, s) = "zero with " ++ s
tuplePattern (n, s) = show n ++ " with " ++ s
```

#### 守卫表达式

```haskell
-- 基本守卫
guardFunction :: Integer -> String
guardFunction x
    | x < 0     = "negative"
    | x == 0    = "zero"
    | x < 10    = "small"
    | otherwise = "large"

-- 多条件守卫
multiGuardFunction :: Integer -> Integer -> String
multiGuardFunction x y
    | x < 0 && y < 0 = "both negative"
    | x < 0          = "x negative"
    | y < 0          = "y negative"
    | x == y         = "equal"
    | x > y          = "x greater"
    | otherwise      = "y greater"
```

### 4. 数据类型

#### 基本数据类型

```haskell
-- 预定义类型
predefinedTypes :: (Integer, Double, Char, String, Bool)
predefinedTypes = (42, 3.14, 'A', "Hello", True)

-- 类型别名
type Age = Integer
type Name = String
type Person = (Name, Age)

-- 新类型
newtype NewAge = NewAge Integer
    deriving (Show, Eq, Ord)

-- 代数数据类型
data Color = Red | Green | Blue
    deriving (Show, Eq)

data Shape = Circle Double | Rectangle Double Double
    deriving (Show)

-- 参数化类型
data Maybe a = Nothing | Just a
    deriving (Show, Eq)

data Either a b = Left a | Right b
    deriving (Show, Eq)
```

#### 记录语法

```haskell
-- 记录类型定义
data Person = Person
    { name :: String
    , age  :: Integer
    , city :: String
    }
    deriving (Show, Eq)

-- 记录构造
createPerson :: String -> Integer -> String -> Person
createPerson n a c = Person { name = n, age = a, city = c }

-- 记录更新
updateAge :: Person -> Integer -> Person
updateAge person newAge = person { age = newAge }

-- 记录访问
getPersonInfo :: Person -> String
getPersonInfo person = name person ++ " is " ++ show (age person) ++ " years old"
```

### 5. 列表和列表推导

#### 列表操作

```haskell
-- 列表构造
listConstruction :: [Integer]
listConstruction = [1, 2, 3, 4, 5]

-- 范围语法
rangeSyntax :: [Integer]
rangeSyntax = [1..10]  -- [1,2,3,4,5,6,7,8,9,10]

-- 步长范围
stepRange :: [Integer]
stepRange = [0,2..10]  -- [0,2,4,6,8,10]

-- 无限列表
infiniteList :: [Integer]
infiniteList = [1..]  -- 无限列表

-- 列表操作
listOperations :: [Integer]
listOperations = head [1,2,3] : tail [4,5,6]  -- [1,5,6]
```

#### 列表推导

```haskell
-- 基本列表推导
basicListComprehension :: [Integer]
basicListComprehension = [x | x <- [1..10], even x]  -- [2,4,6,8,10]

-- 多生成器
multipleGenerators :: [(Integer, Integer)]
multipleGenerators = [(x, y) | x <- [1..3], y <- [1..3]]

-- 条件过滤
conditionalComprehension :: [Integer]
conditionalComprehension = [x | x <- [1..20], x `mod` 3 == 0, x `mod` 5 == 0]

-- 嵌套推导
nestedComprehension :: [Integer]
nestedComprehension = [x*y | x <- [1..3], y <- [1..3], x < y]
```

### 6. 高阶函数

#### 常用高阶函数

```haskell
-- map函数
mapExample :: [Integer] -> [Integer]
mapExample xs = map (+1) xs

-- filter函数
filterExample :: [Integer] -> [Integer]
filterExample xs = filter even xs

-- foldr函数
foldrExample :: [Integer] -> Integer
foldrExample xs = foldr (+) 0 xs

-- foldl函数
foldlExample :: [Integer] -> Integer
foldlExample xs = foldl (+) 0 xs

-- 函数组合
compositionExample :: [Integer] -> [Integer]
compositionExample = map (*2) . filter even
```

#### 自定义高阶函数

```haskell
-- 自定义map
myMap :: (a -> b) -> [a] -> [b]
myMap _ [] = []
myMap f (x:xs) = f x : myMap f xs

-- 自定义filter
myFilter :: (a -> Bool) -> [a] -> [a]
myFilter _ [] = []
myFilter p (x:xs)
    | p x       = x : myFilter p xs
    | otherwise = myFilter p xs

-- 自定义foldr
myFoldr :: (a -> b -> b) -> b -> [a] -> b
myFoldr _ z [] = z
myFoldr f z (x:xs) = f x (myFoldr f z xs)
```

### 7. 错误处理

#### Maybe类型

```haskell
-- 安全除法
safeDivide :: Double -> Double -> Maybe Double
safeDivide _ 0 = Nothing
safeDivide x y = Just (x / y)

-- Maybe处理
handleMaybe :: Maybe Integer -> String
handleMaybe Nothing = "No value"
handleMaybe (Just x) = "Value: " ++ show x

-- Maybe链式操作
maybeChain :: Maybe Integer -> Maybe Integer
maybeChain mx = do
    x <- mx
    y <- safeDivide (fromIntegral x) 2
    return (round y)
```

#### Either类型

```haskell
-- 错误处理
safeDivideEither :: Double -> Double -> Either String Double
safeDivideEither _ 0 = Left "Division by zero"
safeDivideEither x y = Right (x / y)

-- Either处理
handleEither :: Either String Integer -> String
handleEither (Left err) = "Error: " ++ err
handleEither (Right x) = "Result: " ++ show x
```

## 语法规则

### 1. 缩进规则

```haskell
-- 正确的缩进
correctIndentation :: Integer -> String
correctIndentation x
    | x < 0     = "negative"
    | x == 0    = "zero"
    | otherwise = "positive"

-- 多行表达式
multiLineExpression :: Integer -> Integer
multiLineExpression x = 
    let y = x * 2
        z = y + 1
    in z * 3
```

### 2. 操作符优先级

```haskell
-- 操作符优先级示例
operatorPrecedence :: Integer
operatorPrecedence = 2 + 3 * 4  -- 结果为14，不是20

-- 自定义操作符
infixl 6 +:  -- 左结合，优先级6
(+:) :: Integer -> Integer -> Integer
x +: y = x + y + 1

infixr 5 *:  -- 右结合，优先级5
(*:) :: Integer -> Integer -> Integer
x *: y = x * y * 2
```

### 3. 模块系统

```haskell
-- 模块声明
module SyntaxBasics 
    ( publicFunction
    , PublicType(..)
    ) where

-- 导入语句
import Data.List (sort, nub)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

-- 导出
publicFunction :: Integer -> Integer
publicFunction x = x + 1

data PublicType = Constructor1 | Constructor2
    deriving (Show)
```

## 最佳实践

### 1. 命名约定

```haskell
-- 函数名使用小写字母和下划线
goodFunctionName :: Integer -> Integer
goodFunctionName x = x + 1

-- 类型名使用大写字母
data GoodTypeName = Constructor1 | Constructor2

-- 类型变量使用小写字母
polymorphicFunction :: a -> a -> a
polymorphicFunction x y = x
```

### 2. 类型安全

```haskell
-- 显式类型签名
explicitTypeSignature :: Integer -> Integer
explicitTypeSignature x = x + 1

-- 避免部分函数
safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x

-- 使用Maybe而不是部分函数
safeTail :: [a] -> Maybe [a]
safeTail [] = Nothing
safeTail (_:xs) = Just xs
```

### 3. 函数纯度

```haskell
-- 纯函数
pureFunction :: Integer -> Integer
pureFunction x = x * x

-- 避免副作用
-- 不好的例子：print x  -- 有副作用
-- 好的例子：返回计算结果，让调用者决定如何处理
```

## 总结

Haskell的基础语法为函数式编程提供了强大的工具。通过理解表达式、函数定义、模式匹配、数据类型等核心概念，可以开始编写类型安全、纯函数的Haskell程序。这些基础概念为学习更高级的Haskell特性奠定了坚实的基础。

---

**相关文档**:

- [函数定义与使用](02-Functions.md)
- [模式匹配](03-Pattern-Matching.md)
- [数据类型](04-Data-Types.md)

**导航**: [返回Haskell主索引](../README.md) | [下一主题: 函数定义与使用](02-Functions.md)
