# Haskell代数数据类型

## 概述

代数数据类型（Algebraic Data Types, ADT）是Haskell中定义数据结构的主要方式。它们基于数学中的代数概念，包括和类型（Sum Types）和积类型（Product Types），提供了强大而灵活的数据建模能力。

## 目录

- [概述](#概述)
- [数学基础](#数学基础)
- [和类型](#和类型)
- [积类型](#积类型)
- [递归类型](#递归类型)
- [类型构造器](#类型构造器)
- [模式匹配](#模式匹配)
- [类型类实例](#类型类实例)
- [高级特性](#高级特性)
- [总结](#总结)

## 数学基础

### 形式化定义

**定义 4.1 (代数数据类型)**
代数数据类型是基于集合论和范畴论的数学结构：

$$\text{ADT} = \text{Sum Types} + \text{Product Types}$$

**定义 4.2 (和类型)**
和类型表示多个可能值的联合：
$$\text{Sum}(A, B) = A + B = \{(0, a) | a \in A\} \cup \{(1, b) | b \in B\}$$

**定义 4.3 (积类型)**
积类型表示多个值的组合：
$$\text{Product}(A, B) = A \times B = \{(a, b) | a \in A, b \in B\}$$

### 代数性质

**定理 4.1 (分配律)**
$$A \times (B + C) = (A \times B) + (A \times C)$$

**定理 4.2 (单位元)**
$$A + \emptyset = A$$
$$A \times 1 = A$$

## 和类型

### 形式化定义

**定义 4.4 (和类型构造)**
和类型通过多个构造器定义，每个构造器代表一种可能的值：

$$\text{SumType} = \{\text{Constructor}_1, \text{Constructor}_2, \ldots, \text{Constructor}_n\}$$

### Haskell实现

```haskell
-- 基本和类型（枚举）
data Bool = True | False

data Direction = North | South | East | West

data Color = Red | Green | Blue | Yellow

-- 带参数的和类型
data Maybe a = Nothing | Just a

data Either a b = Left a | Right b

data Ordering = LT | EQ | GT

-- 复杂和类型
data Shape = 
    Circle Double
    | Rectangle Double Double
    | Triangle Double Double Double
    | Polygon [Point]

data Expression = 
    Literal Int
    | Variable String
    | Add Expression Expression
    | Multiply Expression Expression
    | Negate Expression
```

### 和类型的应用

```haskell
-- Maybe类型应用
safeDivide :: Double -> Double -> Maybe Double
safeDivide _ 0 = Nothing
safeDivide x y = Just (x / y)

-- Either类型应用
parseInt :: String -> Either String Int
parseInt s = case reads s of
    [(n, "")] -> Right n
    _ -> Left "Invalid integer"

-- 自定义和类型应用
area :: Shape -> Double
area (Circle r) = pi * r * r
area (Rectangle w h) = w * h
area (Triangle a b c) = 
    let s = (a + b + c) / 2
    in sqrt (s * (s - a) * (s - b) * (s - c))
area (Polygon points) = polygonArea points

-- 表达式求值
eval :: Expression -> Int
eval (Literal n) = n
eval (Variable _) = error "Unbound variable"
eval (Add e1 e2) = eval e1 + eval e2
eval (Multiply e1 e2) = eval e1 * eval e2
eval (Negate e) = -eval e
```

## 积类型

### 形式化定义

**定义 4.5 (积类型构造)**
积类型通过记录或元组定义，包含多个字段：

$$\text{ProductType} = \{(f_1: T_1, f_2: T_2, \ldots, f_n: T_n)\}$$

### Haskell实现

```haskell
-- 基本积类型（元组）
type Point = (Double, Double)
type Vector = (Double, Double, Double)

-- 记录类型
data Person = Person 
    { name :: String
    , age :: Int
    , email :: String
    , address :: Address
    }

data Address = Address 
    { street :: String
    , city :: String
    , state :: String
    , zipCode :: String
    , country :: String
    }

-- 复杂积类型
data Employee = Employee 
    { person :: Person
    , employeeId :: String
    , department :: String
    , salary :: Double
    , hireDate :: Date
    }

data Date = Date 
    { year :: Int
    , month :: Int
    , day :: Int
    }
```

### 积类型的应用

```haskell
-- 记录访问
personName :: Person -> String
personName Person{name = n} = n

personAge :: Person -> Int
personAge Person{age = a} = a

-- 记录更新
updateAge :: Person -> Int -> Person
updateAge person newAge = person{age = newAge}

updateEmail :: Person -> String -> Person
updateEmail person newEmail = person{email = newEmail}

-- 嵌套记录处理
employeeLocation :: Employee -> String
employeeLocation Employee{person = Person{address = Address{city = c}}} = c

-- 记录组合
fullAddress :: Address -> String
fullAddress Address{street = s, city = c, state = st, zipCode = z} = 
    s ++ ", " ++ c ++ ", " ++ st ++ " " ++ z
```

## 递归类型

### 形式化定义

**定义 4.6 (递归类型)**
递归类型包含对自身的引用，用于表示自相似的数据结构：

$$\text{RecursiveType} = \text{BaseCase} + \text{RecursiveCase}(\text{RecursiveType})$$

### Haskell实现

```haskell
-- 列表类型
data List a = Nil | Cons a (List a)

-- 二叉树
data Tree a = Empty | Node a (Tree a) (Tree a)

-- 表达式树
data ExprTree = 
    Leaf Int
    | Add ExprTree ExprTree
    | Multiply ExprTree ExprTree
    | Negate ExprTree

-- 链表
data LinkedList a = 
    EmptyList
    | ListNode a (LinkedList a)

-- 嵌套结构
data NestedList a = 
    Elem a
    | List [NestedList a]
```

### 递归类型的应用

```haskell
-- 列表操作
listLength :: List a -> Int
listLength Nil = 0
listLength (Cons _ xs) = 1 + listLength xs

listHead :: List a -> Maybe a
listHead Nil = Nothing
listHead (Cons x _) = Just x

listMap :: (a -> b) -> List a -> List b
listMap _ Nil = Nil
listMap f (Cons x xs) = Cons (f x) (listMap f xs)

-- 树操作
treeSize :: Tree a -> Int
treeSize Empty = 0
treeSize (Node _ left right) = 1 + treeSize left + treeSize right

treeHeight :: Tree a -> Int
treeHeight Empty = 0
treeHeight (Node _ left right) = 1 + max (treeHeight left) (treeHeight right)

treeMap :: (a -> b) -> Tree a -> Tree b
treeMap _ Empty = Empty
treeMap f (Node x left right) = Node (f x) (treeMap f left) (treeMap f right)

-- 表达式树求值
evalTree :: ExprTree -> Int
evalTree (Leaf n) = n
evalTree (Add left right) = evalTree left + evalTree right
evalTree (Multiply left right) = evalTree left * evalTree right
evalTree (Negate expr) = -evalTree expr
```

## 类型构造器

### 形式化定义

**定义 4.7 (类型构造器)**
类型构造器是接受类型参数并返回新类型的函数：

$$\text{TypeConstructor} : \text{Type} \rightarrow \text{Type}$$

### Haskell实现

```haskell
-- 基本类型构造器
data Maybe a = Nothing | Just a

data Either a b = Left a | Right b

data List a = Nil | Cons a (List a)

-- 多参数类型构造器
data Pair a b = Pair a b

data Triple a b c = Triple a b c

-- 高阶类型构造器
data HigherOrder f a = HigherOrder (f a)

-- 类型构造器组合
type MaybeList a = Maybe [a]
type EitherMaybe a b = Either a (Maybe b)
type ListOfPairs a b = [Pair a b]
```

### 类型构造器的应用

```haskell
-- Maybe构造器应用
safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x

safeTail :: [a] -> Maybe [a]
safeTail [] = Nothing
safeTail (_:xs) = Just xs

-- Either构造器应用
parseNumber :: String -> Either String Int
parseNumber s = case reads s of
    [(n, "")] -> Right n
    _ -> Left ("Cannot parse: " ++ s)

-- 类型构造器组合
complexType :: [Either String Int] -> Maybe [Int]
complexType xs = 
    case sequence (map parseNumber (map show xs)) of
        Left _ -> Nothing
        Right ns -> Just ns
```

## 模式匹配

### 形式化定义

**定义 4.8 (ADT模式匹配)**
ADT的模式匹配基于构造器的形式：

$$\text{ADTPatternMatch}(v, c) = \begin{cases}
\text{Just } \sigma & \text{if } v \text{ constructed by } c \\
\text{Nothing} & \text{otherwise}
\end{cases}$$

### Haskell实现

```haskell
-- 和类型模式匹配
shapeArea :: Shape -> Double
shapeArea (Circle r) = pi * r * r
shapeArea (Rectangle w h) = w * h
shapeArea (Triangle a b c) =
    let s = (a + b + c) / 2
    in sqrt (s * (s - a) * (s - b) * (s - c))
shapeArea (Polygon points) = polygonArea points

-- 积类型模式匹配
personInfo :: Person -> String
personInfo Person{name = n, age = a, email = e} =
    n ++ " (" ++ show a ++ ") - " ++ e

-- 递归类型模式匹配
listSum :: Num a => List a -> a
listSum Nil = 0
listSum (Cons x xs) = x + listSum xs

-- 嵌套模式匹配
complexPattern :: Employee -> String
complexPattern Employee{person = Person{name = n, address = Address{city = c}}} =
    n ++ " works in " ++ c
```

### 高级模式匹配

```haskell
-- 守卫表达式与模式匹配
shapeCategory :: Shape -> String
shapeCategory (Circle r)
    | r == 0 = "Point"
    | r < 1 = "Small circle"
    | r < 10 = "Medium circle"
    | otherwise = "Large circle"
shapeCategory (Rectangle w h)
    | w == h = "Square"
    | w > h = "Wide rectangle"
    | otherwise = "Tall rectangle"
shapeCategory _ = "Other shape"

-- 模式匹配与函数组合
processShapes :: [Shape] -> [Double]
processShapes = map shapeArea . filter isCircle
  where
    isCircle (Circle _) = True
    isCircle _ = False
```

## 类型类实例

### 形式化定义

**定义 4.9 (ADT类型类)**
为ADT实现类型类提供标准化的操作接口：

$$\text{TypeClassInstance}(C, T) = \{f | f: C \rightarrow T \text{ and } T \text{ implements } C\}$$

### Haskell实现

```haskell
-- 基本类型类实例
instance Eq Bool where
    True == True = True
    False == False = True
    _ == _ = False

instance Show Bool where
    show True = "True"
    show False = "False"

-- 参数化类型类实例
instance Eq a => Eq (Maybe a) where
    Nothing == Nothing = True
    Just x == Just y = x == y
    _ == _ = False

instance Show a => Show (Maybe a) where
    show Nothing = "Nothing"
    show (Just x) = "Just " ++ show x

-- 递归类型类实例
instance Eq a => Eq (List a) where
    Nil == Nil = True
    Cons x xs == Cons y ys = x == y && xs == ys
    _ == _ = False

instance Show a => Show (List a) where
    show Nil = "[]"
    show (Cons x xs) = show x ++ " : " ++ show xs
```

### 高级类型类实例

```haskell
-- Functor实例
instance Functor Maybe where
    fmap _ Nothing = Nothing
    fmap f (Just x) = Just (f x)

instance Functor List where
    fmap _ Nil = Nil
    fmap f (Cons x xs) = Cons (f x) (fmap f xs)

-- Monad实例
instance Monad Maybe where
    return = Just
    Nothing >>= _ = Nothing
    Just x >>= f = f x

instance Monad List where
    return x = Cons x Nil
    Nil >>= _ = Nil
    Cons x xs >>= f = append (f x) (xs >>= f)
      where
        append Nil ys = ys
        append (Cons x xs) ys = Cons x (append xs ys)
```

## 高级特性

### 形式化定义

**定义 4.10 (高级ADT特性)**
高级ADT特性包括：
- **GADT**: 广义代数数据类型
- **类型族**: 类型级函数
- **数据族**: 参数化数据类型族

### Haskell实现

```haskell
-- GADT示例（需要扩展）
-- {-# LANGUAGE GADTs #-}
-- data Expr a where
--     Lit :: Int -> Expr Int
--     Add :: Expr Int -> Expr Int -> Expr Int
--     Bool :: Bool -> Expr Bool
--     If :: Expr Bool -> Expr a -> Expr a -> Expr a

-- 类型族示例（需要扩展）
-- {-# LANGUAGE TypeFamilies #-}
-- type family ElementType c
-- type instance ElementType [a] = a
-- type instance ElementType (Maybe a) = a

-- 数据族示例（需要扩展）
-- {-# LANGUAGE TypeFamilies #-}
-- data family Array a
-- data instance Array Int = IntArray [Int]
-- data instance Array Bool = BoolArray [Bool]
```

### 实际可用的高级特性

```haskell
-- 类型别名
type String = [Char]
type Point = (Double, Double)
type Matrix a = [[a]]

-- 新类型
newtype Age = Age Int
newtype Name = Name String
newtype Email = Email String

-- 类型约束
data ConstrainedList a =
    EmptyList
    | ConstrainedCons a (ConstrainedList a)
    deriving (Show, Eq)

-- 派生实例
data Color = Red | Green | Blue
    deriving (Show, Eq, Ord, Enum, Bounded)

data Person = Person String Int
    deriving (Show, Eq)
```

## 总结

Haskell的代数数据类型提供了强大而灵活的数据建模能力：

### 主要优势

1. **类型安全**: 编译时保证数据结构的正确性
2. **表达力**: 支持复杂的数据结构建模
3. **模式匹配**: 自然的数据处理方式
4. **组合性**: 类型可以组合和重用
5. **数学基础**: 基于坚实的数学理论

### 应用场景

- **数据结构**: 定义各种复杂的数据结构
- **领域建模**: 建模业务领域的概念
- **错误处理**: 使用Maybe和Either处理错误
- **状态管理**: 表示程序的不同状态
- **算法实现**: 实现各种算法和数据结构

### 最佳实践

1. **语义清晰**: 选择有意义的构造器名称
2. **类型安全**: 利用类型系统防止错误
3. **模式匹配**: 充分利用模式匹配处理数据
4. **类型类**: 为ADT实现适当的类型类
5. **文档化**: 为ADT提供清晰的文档

### 学习建议

1. **理解基础**: 掌握和类型与积类型的概念
2. **实践练习**: 通过实际编程练习
3. **模式匹配**: 深入学习模式匹配技巧
4. **类型类**: 学习为ADT实现类型类
5. **高级特性**: 逐步学习GADT等高级特性

---

**相关链接**:
- [类型系统基础](../README.md)
- [类型类](02-Type-Classes.md)
- [高级类型特性](03-Advanced-Type-Features.md)
- [返回主索引](../../README.md)
