# Haskell 语法基础

## 概述

Haskell是一种纯函数式编程语言，具有强类型系统和惰性求值特性。本文档介绍Haskell的基本语法结构，包括表达式、声明、模式匹配等核心概念。

## 1. 基本表达式

### 1.1 字面量

Haskell支持多种字面量类型：

```haskell
-- 整数字面量
integerLiteral :: Integer
integerLiteral = 42

-- 浮点数字面量
floatLiteral :: Double
floatLiteral = 3.14159

-- 字符字面量
charLiteral :: Char
charLiteral = 'a'

-- 字符串字面量
stringLiteral :: String
stringLiteral = "Hello, Haskell!"

-- 布尔字面量
boolLiteral :: Bool
boolLiteral = True
```

### 1.2 变量绑定

在Haskell中，变量绑定使用等号（=）：

```haskell
-- 简单变量绑定
x :: Int
x = 10

y :: Double
y = 20.5

-- 多变量绑定
(a, b) :: (Int, String)
(a, b) = (1, "hello")
```

### 1.3 函数定义

函数定义是Haskell的核心：

```haskell
-- 基本函数定义
add :: Int -> Int -> Int
add x y = x + y

-- 使用模式匹配的函数定义
factorial :: Integer -> Integer
factorial 0 = 1
factorial n = n * factorial (n - 1)

-- 使用守卫的函数定义
absolute :: Int -> Int
absolute x
  | x >= 0    = x
  | otherwise = -x
```

## 2. 类型系统

### 2.1 基本类型

Haskell的基本类型包括：

```haskell
-- 整数类型
intValue :: Int
intValue = 42

integerValue :: Integer
integerValue = 1234567890123456789

-- 浮点类型
doubleValue :: Double
doubleValue = 3.14159

floatValue :: Float
floatValue = 2.718

-- 字符和字符串
charValue :: Char
charValue = 'H'

stringValue :: String
stringValue = "Haskell"

-- 布尔类型
boolValue :: Bool
boolValue = True
```

### 2.2 复合类型

```haskell
-- 元组类型
tuple2 :: (Int, String)
tuple2 = (1, "hello")

tuple3 :: (Int, Double, Bool)
tuple3 = (1, 2.5, True)

-- 列表类型
intList :: [Int]
intList = [1, 2, 3, 4, 5]

stringList :: [String]
stringList = ["hello", "world"]

-- 函数类型
functionType :: (Int -> Int) -> Int -> Int
functionType f x = f (f x)
```

## 3. 模式匹配

### 3.1 基本模式匹配

```haskell
-- 常量模式
describeNumber :: Int -> String
describeNumber 0 = "zero"
describeNumber 1 = "one"
describeNumber _ = "other"

-- 变量模式
first :: (a, b) -> a
first (x, _) = x

-- 构造器模式
head' :: [a] -> Maybe a
head' [] = Nothing
head' (x:_) = Just x
```

### 3.2 列表模式匹配

```haskell
-- 列表构造器模式
sumList :: [Int] -> Int
sumList [] = 0
sumList (x:xs) = x + sumList xs

-- 多个元素模式
firstTwo :: [a] -> Maybe (a, a)
firstTwo (x:y:_) = Just (x, y)
firstTwo _ = Nothing
```

## 4. 高阶函数

### 4.1 函数作为参数

```haskell
-- 高阶函数定义
applyTwice :: (a -> a) -> a -> a
applyTwice f x = f (f x)

-- 使用高阶函数
double :: Int -> Int
double x = x * 2

result :: Int
result = applyTwice double 5  -- 结果为 20
```

### 4.2 函数组合

```haskell
-- 函数组合操作符
(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

-- 使用函数组合
addOne :: Int -> Int
addOne x = x + 1

multiplyByTwo :: Int -> Int
multiplyByTwo x = x * 2

composedFunction :: Int -> Int
composedFunction = addOne . multiplyByTwo
```

## 5. 类型类

### 5.1 基本类型类

```haskell
-- Eq类型类实例
data Color = Red | Green | Blue

instance Eq Color where
  Red == Red = True
  Green == Green = True
  Blue == Blue = True
  _ == _ = False

-- Show类型类实例
instance Show Color where
  show Red = "Red"
  show Green = "Green"
  show Blue = "Blue"
```

### 5.2 自定义类型类

```haskell
-- 定义类型类
class Describable a where
  describe :: a -> String

-- 为基本类型实现类型类
instance Describable Int where
  describe n = "Integer: " ++ show n

instance Describable String where
  describe s = "String: " ++ s
```

## 6. 模块系统

### 6.1 模块声明

```haskell
-- 模块声明
module SyntaxBasics 
  ( add
  , factorial
  , absolute
  , Color(..)
  ) where

-- 导入其他模块
import Data.List (sort, nub)
import qualified Data.Map as Map
```

### 6.2 导出列表

```haskell
-- 导出所有构造函数
data Tree a = Empty | Node a (Tree a) (Tree a)

-- 导出特定函数
module TreeModule 
  ( Tree(..)  -- 导出所有构造函数
  , insert
  , search
  ) where
```

## 7. 错误处理

### 7.1 Maybe类型

```haskell
-- 使用Maybe处理可能的失败
safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x

-- 处理Maybe值
processMaybe :: Maybe Int -> String
processMaybe Nothing = "No value"
processMaybe (Just x) = "Value: " ++ show x
```

### 7.2 Either类型

```haskell
-- 使用Either处理错误
divide :: Double -> Double -> Either String Double
divide _ 0 = Left "Division by zero"
divide x y = Right (x / y)

-- 处理Either值
processEither :: Either String Double -> String
processEither (Left err) = "Error: " ++ err
processEither (Right result) = "Result: " ++ show result
```

## 8. 惰性求值

### 8.1 无限列表

```haskell
-- 无限列表
infiniteList :: [Integer]
infiniteList = [1..]

-- 取前n个元素
takeFirst :: Int -> [a] -> [a]
takeFirst 0 _ = []
takeFirst _ [] = []
takeFirst n (x:xs) = x : takeFirst (n-1) xs

-- 使用无限列表
firstTen :: [Integer]
firstTen = takeFirst 10 infiniteList
```

### 8.2 惰性计算

```haskell
-- 惰性计算示例
expensiveComputation :: Int -> Int
expensiveComputation n = 
  let result = sum [1..n]  -- 只有在需要时才计算
  in result

-- 条件计算
conditionalComputation :: Bool -> Int -> Int
conditionalComputation True n = expensiveComputation n
conditionalComputation False _ = 0
```

## 9. 数学形式化定义

### 9.1 函数语义

给定函数 $f: A \rightarrow B$，在Haskell中表示为：

```haskell
f :: A -> B
```

### 9.2 类型系统

Haskell的类型系统基于Hindley-Milner类型系统，支持：

- **类型推断**：$\Gamma \vdash e : \tau$
- **类型检查**：$\Gamma \vdash e : \tau \Rightarrow \tau'$
- **类型统一**：$\tau_1 \sim \tau_2$

### 9.3 模式匹配语义

模式匹配的语义定义为：

$$\text{match}(p, v) = \begin{cases}
\text{Just } \sigma & \text{if } p \text{ matches } v \text{ with substitution } \sigma \\
\text{Nothing} & \text{otherwise}
\end{cases}$$

## 10. 实践示例

### 10.1 简单计算器

```haskell
-- 计算器数据类型
data Operation = Add | Subtract | Multiply | Divide

-- 计算函数
calculate :: Operation -> Double -> Double -> Maybe Double
calculate Add x y = Just (x + y)
calculate Subtract x y = Just (x - y)
calculate Multiply x y = Just (x * y)
calculate Divide x 0 = Nothing
calculate Divide x y = Just (x / y)

-- 使用示例
calculatorExample :: IO ()
calculatorExample = do
  putStrLn "Calculator Example:"
  print $ calculate Add 5 3      -- Just 8.0
  print $ calculate Divide 10 2  -- Just 5.0
  print $ calculate Divide 10 0  -- Nothing
```

### 10.2 列表处理

```haskell
-- 列表处理函数
filterEven :: [Int] -> [Int]
filterEven = filter even

mapSquare :: [Int] -> [Int]
mapSquare = map (^2)

sumSquares :: [Int] -> Int
sumSquares = sum . map (^2)

-- 使用示例
listProcessingExample :: IO ()
listProcessingExample = do
  let numbers = [1..10]
  putStrLn "List Processing Example:"
  print $ filterEven numbers     -- [2,4,6,8,10]
  print $ mapSquare numbers      -- [1,4,9,16,25,36,49,64,81,100]
  print $ sumSquares numbers     -- 385
```

## 总结

Haskell的语法基础包括：

1. **表达式和绑定**：变量绑定、函数定义
2. **类型系统**：基本类型、复合类型、类型类
3. **模式匹配**：常量模式、变量模式、构造器模式
4. **高阶函数**：函数作为参数、函数组合
5. **模块系统**：模块声明、导入导出
6. **错误处理**：Maybe类型、Either类型
7. **惰性求值**：无限列表、条件计算

这些基础概念为理解和使用Haskell提供了坚实的基础。

## 相关链接

- [函数式编程基础](01-Functional-Programming-Basics.md)
- [Haskell语言特性](02-Haskell-Language-Features.md)
- [类型系统](../05-Type-System/01-Basic-Types.md)
- [设计模式](../06-Design-Patterns/01-Functional-Patterns.md)

---

**最后更新**: 2024年12月  
**版本**: 1.0.0
