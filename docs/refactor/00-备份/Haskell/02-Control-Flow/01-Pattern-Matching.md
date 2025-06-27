# Haskell模式匹配

## 概述

模式匹配是Haskell的核心特性之一，它允许根据数据结构的形式进行分支处理。模式匹配不仅提供了清晰的数据处理方式，还是函数式编程中数据解构和条件分支的主要机制。

## 目录

- [概述](#概述)
- [基本模式匹配](#基本模式匹配)
- [列表模式匹配](#列表模式匹配)
- [元组模式匹配](#元组模式匹配)
- [记录模式匹配](#记录模式匹配)
- [守卫表达式](#守卫表达式)
- [模式匹配与类型类](#模式匹配与类型类)
- [高级模式匹配](#高级模式匹配)
- [总结](#总结)

## 基本模式匹配

### 形式化定义

**定义 2.1 (模式匹配)**
模式匹配是表达式求值的一种机制，通过模式 $p$ 与值 $v$ 的匹配来决定执行路径。

$$\text{match}(v, p) = \begin{cases}
\text{Just } \sigma & \text{if } v \text{ matches } p \text{ with substitution } \sigma \\
\text{Nothing} & \text{otherwise}
\end{cases}$$

### Haskell实现

```haskell
-- 基本模式匹配
factorial :: Integer -> Integer
factorial 0 = 1
factorial n = n * factorial (n - 1)

-- 布尔模式匹配
not :: Bool -> Bool
not True = False
not False = True

-- 数字模式匹配
sign :: Integer -> Integer
sign 0 = 0
sign n | n > 0 = 1
       | otherwise = -1

-- 字符模式匹配
isVowel :: Char -> Bool
isVowel 'a' = True
isVowel 'e' = True
isVowel 'i' = True
isVowel 'o' = True
isVowel 'u' = True
isVowel _ = False
```

### 通配符模式

```haskell
-- 通配符模式 (_)
ignoreFirst :: (a, b, c) -> (b, c)
ignoreFirst (_, b, c) = (b, c)

-- 变量模式
extractFirst :: (a, b, c) -> a
extractFirst (a, _, _) = a

-- 混合模式
complexPattern :: (Int, String, Bool) -> String
complexPattern (0, s, _) = "Zero: " ++ s
complexPattern (n, s, True) = "Positive True: " ++ s
complexPattern (n, s, False) = "Positive False: " ++ s
```

## 列表模式匹配

### 形式化定义

**定义 2.2 (列表模式)**
列表模式匹配基于列表的构造形式：
- `[]` - 空列表
- `(x:xs)` - 非空列表，其中 `x` 是头部，`xs` 是尾部

$$\text{ListPattern} = \{\text{[]}\} \cup \{(x:xs) | x \in \text{Pattern}, xs \in \text{ListPattern}\}$$

### Haskell实现

```haskell
-- 空列表模式
isEmpty :: [a] -> Bool
isEmpty [] = True
isEmpty _ = False

-- 单元素列表
isSingleton :: [a] -> Bool
isSingleton [_] = True
isSingleton _ = False

-- 多元素列表
listLength :: [a] -> Int
listLength [] = 0
listLength (_:xs) = 1 + listLength xs

-- 列表头部和尾部
head :: [a] -> a
head (x:_) = x
head [] = error "Empty list"

tail :: [a] -> [a]
tail (_:xs) = xs
tail [] = error "Empty list"

-- 安全版本
safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x
```

### 复杂列表模式

```haskell
-- 多元素模式
firstThree :: [a] -> Maybe (a, a, a)
firstThree (x:y:z:_) = Just (x, y, z)
firstThree _ = Nothing

-- 嵌套模式
nestedPattern :: [[a]] -> [a]
nestedPattern [] = []
nestedPattern ([]:xss) = nestedPattern xss
nestedPattern ((x:xs):xss) = x : nestedPattern (xs:xss)

-- 模式匹配与函数组合
processList :: [Int] -> [Int]
processList [] = []
processList (0:xs) = processList xs  -- 跳过0
processList (x:xs) = x : processList xs
```

## 元组模式匹配

### 形式化定义

**定义 2.3 (元组模式)**
元组模式匹配基于元组的构造形式：
- `(p1, p2, ..., pn)` - n元组模式

$$\text{TuplePattern} = \{(p_1, p_2, \ldots, p_n) | p_i \in \text{Pattern}\}$$

### Haskell实现

```haskell
-- 二元组模式
swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

-- 三元组模式
extractMiddle :: (a, b, c) -> b
extractMiddle (_, b, _) = b

-- 嵌套元组
nestedTuple :: ((a, b), (c, d)) -> (a, c)
nestedTuple ((a, _), (c, _)) = (a, c)

-- 元组与列表组合
tupleList :: [(a, b)] -> ([a], [b])
tupleList [] = ([], [])
tupleList ((a, b):xs) =
    let (as, bs) = tupleList xs
    in (a:as, b:bs)
```

### 高级元组模式

```haskell
-- 条件元组模式
conditionalTuple :: (Int, String) -> String
conditionalTuple (0, s) = "Zero: " ++ s
conditionalTuple (n, s) | n > 0 = "Positive: " ++ s
                        | otherwise = "Negative: " ++ s

-- 元组模式与函数
mapTuple :: (a -> b) -> (a, a) -> (b, b)
mapTuple f (x, y) = (f x, f y)

-- 复杂元组处理
complexTuple :: (Int, (String, Bool)) -> String
complexTuple (0, (s, _)) = "Zero with string: " ++ s
complexTuple (n, (s, True)) = "Positive with True: " ++ s
complexTuple (n, (s, False)) = "Positive with False: " ++ s
```

## 记录模式匹配

### 形式化定义

**定义 2.4 (记录模式)**
记录模式匹配基于记录字段的命名：
- `Record{field1 = p1, field2 = p2, ...}` - 记录模式

$$\text{RecordPattern} = \{\text{Record}\{f_1 = p_1, \ldots, f_n = p_n\} | p_i \in \text{Pattern}\}$$

### Haskell实现

```haskell
-- 定义记录类型
data Person = Person
    { name :: String
    , age :: Int
    , email :: String
    }

-- 记录模式匹配
personInfo :: Person -> String
personInfo Person{name = n, age = a} =
    n ++ " is " ++ show a ++ " years old"

-- 部分字段匹配
personName :: Person -> String
personName Person{name = n} = n

-- 嵌套记录
data Address = Address
    { street :: String
    , city :: String
    , country :: String
    }

data Employee = Employee
    { person :: Person
    , address :: Address
    , salary :: Double
    }

-- 嵌套记录模式匹配
employeeLocation :: Employee -> String
employeeLocation Employee{person = Person{name = n}, address = Address{city = c}} =
    n ++ " lives in " ++ c
```

### 记录模式的高级用法

```haskell
-- 记录更新模式
updatePerson :: Person -> Person
updatePerson p@Person{age = a} = p{age = a + 1}

-- 条件记录模式
personCategory :: Person -> String
personCategory Person{age = a}
    | a < 18 = "Minor"
    | a < 65 = "Adult"
    | otherwise = "Senior"

-- 记录模式与函数组合
personProcessor :: (String -> String) -> Person -> Person
personProcessor f Person{name = n, age = a, email = e} =
    Person{name = f n, age = a, email = e}
```

## 守卫表达式

### 形式化定义

**定义 2.5 (守卫表达式)**
守卫表达式提供基于布尔条件的模式匹配扩展：

$$\text{Guard}(e, g_1 \rightarrow e_1, \ldots, g_n \rightarrow e_n) = \begin{cases}
e_1 & \text{if } g_1 \\
e_2 & \text{if } g_2 \\
\vdots \\
e_n & \text{if } g_n \\
\text{otherwise} & \text{default case}
\end{cases}$$

### Haskell实现

```haskell
-- 基本守卫表达式
absolute :: (Num a, Ord a) => a -> a
absolute x
    | x < 0 = -x
    | otherwise = x

-- 多重条件
grade :: Int -> String
grade score
    | score >= 90 = "A"
    | score >= 80 = "B"
    | score >= 70 = "C"
    | score >= 60 = "D"
    | otherwise = "F"

-- 复杂守卫
complexGuard :: Int -> String -> String
complexGuard age name
    | age < 0 = "Invalid age"
    | age < 18 = name ++ " is a minor"
    | age < 65 = name ++ " is an adult"
    | age < 120 = name ++ " is a senior"
    | otherwise = "Invalid age"
```

### 守卫与模式匹配结合

```haskell
-- 模式匹配 + 守卫
patternGuard :: [Int] -> String
patternGuard [] = "Empty list"
patternGuard [x]
    | x > 0 = "Single positive"
    | x < 0 = "Single negative"
    | otherwise = "Single zero"
patternGuard (x:y:xs)
    | x > y = "First greater"
    | x < y = "First smaller"
    | otherwise = "First equal"

-- 记录 + 守卫
personGuard :: Person -> String
personGuard Person{name = n, age = a}
    | a < 18 = n ++ " is underage"
    | a < 65 = n ++ " is working age"
    | otherwise = n ++ " is retired"
```

## 模式匹配与类型类

### 形式化定义

**定义 2.6 (类型类模式)**
类型类模式匹配基于类型类的实例实现：

$$\text{TypeClassPattern}(C, T) = \{p | p \text{ is pattern for type } T \text{ implementing } C\}$$

### Haskell实现

```haskell
-- 类型类与模式匹配
class Show a where
    show :: a -> String

-- 为自定义类型实现Show
data Color = Red | Green | Blue

instance Show Color where
    show Red = "Red"
    show Green = "Green"
    show Blue = "Blue"

-- 模式匹配使用类型类
colorPattern :: Color -> String
colorPattern Red = "Primary color: Red"
colorPattern Green = "Primary color: Green"
colorPattern Blue = "Primary color: Blue"

-- 类型类约束与模式匹配
showPattern :: Show a => a -> String
showPattern x = "Value: " ++ show x
```

### 高级类型类模式

```haskell
-- 多参数类型类
class Eq a where
    (==) :: a -> a -> Bool
    (/=) :: a -> a -> Bool

-- 自定义类型实现Eq
data Shape = Circle Double | Rectangle Double Double

instance Eq Shape where
    Circle r1 == Circle r2 = r1 == r2
    Rectangle w1 h1 == Rectangle w2 h2 = w1 == w2 && h1 == h2
    _ == _ = False

-- 模式匹配使用Eq
shapePattern :: Shape -> String
shapePattern (Circle r)
    | r == 0 = "Point"
    | r > 0 = "Circle with radius " ++ show r
shapePattern (Rectangle w h)
    | w == h = "Square with side " ++ show w
    | otherwise = "Rectangle " ++ show w ++ "x" ++ show h
```

## 高级模式匹配

### 形式化定义

**定义 2.7 (高级模式)**
高级模式包括：
- **惰性模式**: `~(p)` - 延迟模式匹配
- **视图模式**: `(f -> p)` - 基于函数的模式
- **模式同义词**: 用户定义的模式别名

### Haskell实现

```haskell
-- 惰性模式（需要扩展）
-- {-# LANGUAGE BangPatterns #-}
-- lazyPattern :: [a] -> Bool
-- lazyPattern ~(x:xs) = True

-- 视图模式（需要扩展）
-- {-# LANGUAGE ViewPatterns #-}
-- viewPattern :: String -> Bool
-- viewPattern (words -> ws) = length ws > 1

-- 模式同义词（需要扩展）
-- {-# LANGUAGE PatternSynonyms #-}
-- pattern Empty = []
-- pattern Single x = [x]
-- pattern Multiple x xs = x:xs

-- 实际可用的高级模式
advancedPattern :: [Int] -> String
advancedPattern [] = "Empty"
advancedPattern [x] = "Single: " ++ show x
advancedPattern (x:y:xs)
    | x == y = "Repeated: " ++ show x
    | x < y = "Increasing"
    | otherwise = "Decreasing"
```

### 模式匹配优化

```haskell
-- 重叠模式处理
overlappingPattern :: Int -> String
overlappingPattern 0 = "Zero"
overlappingPattern n
    | n > 0 = "Positive"
    | n < 0 = "Negative"
    | otherwise = "Zero again"  -- 永远不会执行

-- 穷尽性检查
exhaustivePattern :: Bool -> String
exhaustivePattern True = "True"
exhaustivePattern False = "False"
-- 编译器确保所有情况都被覆盖

-- 不可达模式
unreachablePattern :: Int -> String
unreachablePattern n
    | n > 0 = "Positive"
    | n < 0 = "Negative"
    | n == 0 = "Zero"  -- 这个分支是多余的
```

## 总结

Haskell的模式匹配是一个强大而灵活的特性：

### 主要优势

1. **清晰性**: 代码意图明确，易于理解
2. **安全性**: 编译时检查穷尽性
3. **表达力**: 支持复杂的数据结构解构
4. **性能**: 编译时优化，运行时高效
5. **可读性**: 自然的数据处理方式

### 应用场景

- **数据解构**: 从复杂数据结构中提取信息
- **条件分支**: 基于数据形式进行不同处理
- **函数定义**: 通过模式匹配定义函数行为
- **错误处理**: 处理不同的数据状态
- **算法实现**: 递归算法的自然表达

### 最佳实践

1. **穷尽性**: 确保所有可能的情况都被覆盖
2. **顺序**: 将更具体的模式放在前面
3. **可读性**: 使用有意义的变量名
4. **性能**: 避免不必要的模式嵌套
5. **类型安全**: 利用类型系统保证模式匹配的正确性

### 学习建议

1. **从简单开始**: 先掌握基本模式匹配
2. **实践练习**: 通过实际编程练习
3. **理解原理**: 学习模式匹配的数学基础
4. **高级特性**: 逐步学习高级模式匹配特性
5. **性能考虑**: 了解模式匹配的性能影响

---

**相关链接**:
- [控制流基础](../README.md)
- [守卫表达式](02-Guards.md)
- [条件表达式](03-Conditionals.md)
- [返回主索引](../../README.md)
