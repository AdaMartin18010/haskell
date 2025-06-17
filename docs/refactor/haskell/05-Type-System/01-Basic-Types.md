# Haskell 基本类型系统

## 概述

Haskell的类型系统是强类型、静态类型的，基于Hindley-Milner类型系统。本文档详细介绍Haskell的基本类型、类型推断和类型安全机制。

## 1. 基本类型

### 1.1 数值类型

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

-- 有理数类型
import Data.Ratio
rationalValue :: Rational
rationalValue = 22 % 7

-- 复数类型
import Data.Complex
complexValue :: Complex Double
complexValue = 3.0 :+ 4.0
```

### 1.2 字符和字符串

```haskell
-- 字符类型
charValue :: Char
charValue = 'H'

-- 字符串类型（字符列表）
stringValue :: String
stringValue = "Hello, Haskell!"

-- 字符串操作
stringLength :: String -> Int
stringLength = length

stringConcat :: String -> String -> String
stringConcat = (++)

-- 字符列表操作
charList :: [Char]
charList = ['H', 'e', 'l', 'l', 'o']
```

### 1.3 布尔类型

```haskell
-- 布尔值
trueValue :: Bool
trueValue = True

falseValue :: Bool
falseValue = False

-- 布尔运算
logicalAnd :: Bool -> Bool -> Bool
logicalAnd = (&&)

logicalOr :: Bool -> Bool -> Bool
logicalOr = (||)

logicalNot :: Bool -> Bool
logicalNot = not

-- 条件表达式
conditionalValue :: Int -> String
conditionalValue n = if n > 0 then "positive" else "non-positive"
```

## 2. 复合类型

### 2.1 元组类型

```haskell
-- 二元组
pair :: (Int, String)
pair = (1, "hello")

-- 三元组
triple :: (Int, Double, Bool)
triple = (1, 2.5, True)

-- 嵌套元组
nestedTuple :: ((Int, String), (Double, Bool))
nestedTuple = ((1, "hello"), (2.5, True))

-- 元组操作
first :: (a, b) -> a
first (x, _) = x

second :: (a, b) -> b
second (_, y) = y

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)
```

### 2.2 列表类型

```haskell
-- 基本列表
intList :: [Int]
intList = [1, 2, 3, 4, 5]

stringList :: [String]
stringList = ["hello", "world"]

-- 列表构造
emptyList :: [a]
emptyList = []

singletonList :: a -> [a]
singletonList x = [x]

-- 列表操作
head' :: [a] -> Maybe a
head' [] = Nothing
head' (x:_) = Just x

tail' :: [a] -> Maybe [a]
tail' [] = Nothing
tail' (_:xs) = Just xs

length' :: [a] -> Int
length' [] = 0
length' (_:xs) = 1 + length' xs
```

### 2.3 Maybe类型

```haskell
-- Maybe类型定义
data Maybe a = Nothing | Just a

-- Maybe操作
fromMaybe :: a -> Maybe a -> a
fromMaybe defaultVal Nothing = defaultVal
fromMaybe _ (Just val) = val

maybe :: b -> (a -> b) -> Maybe a -> b
maybe defaultVal f Nothing = defaultVal
maybe _ f (Just val) = f val

-- 安全除法
safeDivide :: Double -> Double -> Maybe Double
safeDivide _ 0 = Nothing
safeDivide x y = Just (x / y)

-- 列表查找
findElement :: Eq a => a -> [a] -> Maybe Int
findElement _ [] = Nothing
findElement x (y:ys)
  | x == y = Just 0
  | otherwise = fmap (+1) (findElement x ys)
```

## 3. 函数类型

### 3.1 基本函数类型

```haskell
-- 一元函数
increment :: Int -> Int
increment x = x + 1

-- 二元函数
add :: Int -> Int -> Int
add x y = x + y

-- 高阶函数
applyTwice :: (a -> a) -> a -> a
applyTwice f x = f (f x)

-- 函数组合
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

-- 部分应用
addFive :: Int -> Int
addFive = add 5

multiplyByTwo :: Int -> Int
multiplyByTwo = (*2)
```

### 3.2 多态函数

```haskell
-- 多态恒等函数
id' :: a -> a
id' x = x

-- 多态常量函数
const' :: a -> b -> a
const' x _ = x

-- 多态列表操作
map' :: (a -> b) -> [a] -> [b]
map' _ [] = []
map' f (x:xs) = f x : map' f xs

filter' :: (a -> Bool) -> [a] -> [a]
filter' _ [] = []
filter' p (x:xs)
  | p x = x : filter' p xs
  | otherwise = filter' p xs
```

## 4. 类型类

### 4.1 基本类型类

```haskell
-- Eq类型类
class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool
  x /= y = not (x == y)

-- Ord类型类
class (Eq a) => Ord a where
  compare :: a -> a -> Ordering
  (<) :: a -> a -> Bool
  (<=) :: a -> a -> Bool
  (>) :: a -> a -> Bool
  (>=) :: a -> a -> Bool
  max :: a -> a -> a
  min :: a -> a -> a

-- Show类型类
class Show a where
  show :: a -> String

-- Read类型类
class Read a where
  readsPrec :: Int -> ReadS a
```

### 4.2 数值类型类

```haskell
-- Num类型类
class (Eq a, Show a) => Num a where
  (+) :: a -> a -> a
  (-) :: a -> a -> a
  (*) :: a -> a -> a
  negate :: a -> a
  abs :: a -> a
  signum :: a -> a
  fromInteger :: Integer -> a

-- Integral类型类
class (Real a, Enum a) => Integral a where
  quot :: a -> a -> a
  rem :: a -> a -> a
  div :: a -> a -> a
  mod :: a -> a -> a
  quotRem :: a -> a -> (a, a)
  divMod :: a -> a -> (a, a)
  toInteger :: a -> Integer

-- Fractional类型类
class (Num a) => Fractional a where
  (/) :: a -> a -> a
  recip :: a -> a
  fromRational :: Rational -> a
```

## 5. 类型推断

### 5.1 基本类型推断

```haskell
-- 自动类型推断
autoInferred = 42  -- 推断为 Num a => a

-- 函数类型推断
inferredFunction x = x + 1  -- 推断为 Num a => a -> a

-- 列表类型推断
inferredList = [1, 2, 3]  -- 推断为 Num a => [a]

-- 多态类型推断
inferredMap f xs = map f xs  -- 推断为 (a -> b) -> [a] -> [b]
```

### 5.2 类型注解

```haskell
-- 显式类型注解
explicitInt :: Int
explicitInt = 42

explicitFunction :: Int -> Int -> Int
explicitFunction x y = x + y

-- 多态类型注解
polymorphicFunction :: a -> a
polymorphicFunction x = x

-- 约束类型注解
constrainedFunction :: Num a => a -> a -> a
constrainedFunction x y = x + y
```

## 6. 类型安全

### 6.1 类型检查

```haskell
-- 类型安全的函数
safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x

-- 类型安全的除法
safeDivision :: (Fractional a, Eq a) => a -> a -> Maybe a
safeDivision _ 0 = Nothing
safeDivision x y = Just (x / y)

-- 类型安全的列表操作
safeIndex :: [a] -> Int -> Maybe a
safeIndex [] _ = Nothing
safeIndex (x:_) 0 = Just x
safeIndex (_:xs) n
  | n < 0 = Nothing
  | otherwise = safeIndex xs (n - 1)
```

### 6.2 类型错误预防

```haskell
-- 使用Maybe避免错误
processMaybe :: Maybe Int -> String
processMaybe Nothing = "No value"
processMaybe (Just x) = "Value: " ++ show x

-- 使用Either处理错误
processEither :: Either String Int -> String
processEither (Left err) = "Error: " ++ err
processEither (Right val) = "Value: " ++ show val

-- 类型安全的模式匹配
safePatternMatch :: [a] -> String
safePatternMatch [] = "Empty list"
safePatternMatch [x] = "Single element"
safePatternMatch (x:y:xs) = "Multiple elements"
```

## 7. 高级类型特性

### 7.1 类型别名

```haskell
-- 类型别名
type Name = String
type Age = Int
type Person = (Name, Age)

-- 函数类型别名
type BinaryOp a = a -> a -> a
type Predicate a = a -> Bool

-- 使用类型别名
addNumbers :: BinaryOp Int
addNumbers = (+)

isPositive :: Predicate Int
isPositive = (>0)
```

### 7.2 新类型

```haskell
-- 新类型定义
newtype Celsius = Celsius Double
newtype Fahrenheit = Fahrenheit Double

-- 新类型操作
toFahrenheit :: Celsius -> Fahrenheit
toFahrenheit (Celsius c) = Fahrenheit (c * 9/5 + 32)

toCelsius :: Fahrenheit -> Celsius
toCelsius (Fahrenheit f) = Celsius ((f - 32) * 5/9)

-- 新类型实例
instance Show Celsius where
  show (Celsius c) = show c ++ "°C"

instance Show Fahrenheit where
  show (Fahrenheit f) = show f ++ "°F"
```

## 8. 形式化类型理论

### 8.1 Hindley-Milner类型系统

Haskell的类型系统基于Hindley-Milner类型系统，支持：

- **类型推断**：$\Gamma \vdash e : \tau$
- **类型检查**：$\Gamma \vdash e : \tau \Rightarrow \tau'$
- **类型统一**：$\tau_1 \sim \tau_2$

### 8.2 类型规则

**变量规则**：
$$\frac{x : \tau \in \Gamma}{\Gamma \vdash x : \tau}$$

**应用规则**：
$$\frac{\Gamma \vdash e_1 : \tau_1 \rightarrow \tau_2 \quad \Gamma \vdash e_2 : \tau_1}{\Gamma \vdash e_1 e_2 : \tau_2}$$

**抽象规则**：
$$\frac{\Gamma, x : \tau_1 \vdash e : \tau_2}{\Gamma \vdash \lambda x.e : \tau_1 \rightarrow \tau_2}$$

### 8.3 类型统一

类型统一的语义：

$$\text{unify}(\tau_1, \tau_2) = \begin{cases}
\text{Just } \sigma & \text{if } \tau_1 \text{ and } \tau_2 \text{ are unifiable} \\
\text{Nothing} & \text{otherwise}
\end{cases}$$

## 9. 实践示例

### 9.1 类型安全计算器

```haskell
-- 计算器类型
data Operation = Add | Subtract | Multiply | Divide

-- 类型安全的计算
calculate :: Operation -> Double -> Double -> Maybe Double
calculate Add x y = Just (x + y)
calculate Subtract x y = Just (x - y)
calculate Multiply x y = Just (x * y)
calculate Divide x 0 = Nothing
calculate Divide x y = Just (x / y)

-- 类型安全的计算器
calculator :: IO ()
calculator = do
  putStrLn "Enter operation (+, -, *, /):"
  opStr <- getLine
  putStrLn "Enter first number:"
  xStr <- getLine
  putStrLn "Enter second number:"
  yStr <- getLine
  
  let op = case opStr of
        "+" -> Add
        "-" -> Subtract
        "*" -> Multiply
        "/" -> Divide
        _ -> error "Invalid operation"
      x = read xStr :: Double
      y = read yStr :: Double
      result = calculate op x y
  
  case result of
    Just r -> putStrLn $ "Result: " ++ show r
    Nothing -> putStrLn "Error: Invalid operation"
```

### 9.2 类型安全数据结构

```haskell
-- 类型安全的栈
newtype Stack a = Stack [a]

-- 栈操作
empty :: Stack a
empty = Stack []

push :: a -> Stack a -> Stack a
push x (Stack xs) = Stack (x:xs)

pop :: Stack a -> Maybe (a, Stack a)
pop (Stack []) = Nothing
pop (Stack (x:xs)) = Just (x, Stack xs)

peek :: Stack a -> Maybe a
peek (Stack []) = Nothing
peek (Stack (x:_)) = Just x

-- 栈实例
instance Show a => Show (Stack a) where
  show (Stack xs) = "Stack " ++ show xs
```

## 总结

Haskell的基本类型系统包括：

1. **基本类型**：数值、字符、布尔、字符串
2. **复合类型**：元组、列表、Maybe
3. **函数类型**：一元函数、高阶函数、多态函数
4. **类型类**：Eq、Ord、Show、Num等
5. **类型推断**：自动类型推断和显式注解
6. **类型安全**：编译时类型检查和错误预防

这些特性提供了强大而安全的类型系统，确保程序的正确性和可靠性。

## 相关链接

- [语法基础](../01-Basic-Concepts/03-Syntax-Basics.md)
- [代数数据类型](02-Algebraic-Data-Types.md)
- [类型类](03-Type-Classes.md)
- [高级类型](04-Advanced-Types.md)

---

**最后更新**: 2024年12月  
**版本**: 1.0.0
