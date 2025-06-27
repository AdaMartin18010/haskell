# Haskell模式匹配

## 📚 快速导航

### 相关理论

- [函数式编程基础](./001-Functional-Programming-Foundation.md)
- [类型理论基础](./03-Theory/04-Type-Theory/001-Simple-Type-Theory.md)
- [形式语言理论](./03-Theory/01-Programming-Language-Theory/001-Syntax-Theory.md)

### 实现示例

- [递归和列表](./003-Recursion-and-Lists.md)
- [高阶函数](./004-Higher-Order-Functions.md)
- [类型系统基础](./04-Type-System/001-Type-System-Foundation.md)

### 应用领域

- [数据结构](./06-Data-Structures/001-Basic-Data-Structures.md)
- [算法实现](./07-Algorithms/001-Sorting-Algorithms.md)
- [Web开发](./11-Web-Development/001-Web-Development-Foundation.md)

## 🎯 概述

模式匹配是Haskell的核心特性之一，它允许根据数据的结构来分解和匹配值。模式匹配不仅提供了强大的数据解构能力，还支持守卫表达式和视图模式等高级功能。

## 📖 1. 基础模式匹配

### 1.1 变量模式

**定义 1.1 (变量模式)**
变量模式匹配任何值并将其绑定到变量名。

**数学基础：**
$$\text{VarPattern} : \text{Value} \rightarrow \text{Environment}$$

**Haskell实现：**

```haskell
-- 变量模式匹配
simpleMatch :: Int -> String
simpleMatch x = "Value is: " ++ show x

-- 多个变量模式
addTwo :: Int -> Int -> Int
addTwo x y = x + y

-- 忽略模式（下划线）
ignoreFirst :: a -> b -> b
ignoreFirst _ y = y

-- 部分忽略
getFirst :: (a, b, c) -> a
getFirst (x, _, _) = x
```

### 1.2 常量模式

**定义 1.2 (常量模式)**
常量模式匹配特定的字面量值。

**数学定义：**
$$\text{ConstPattern}(c) : \text{Value} \rightarrow \text{Bool}$$

**Haskell实现：**

```haskell
-- 数字常量模式
isZero :: Int -> Bool
isZero 0 = True
isZero _ = False

-- 布尔常量模式
negateBool :: Bool -> Bool
negateBool True = False
negateBool False = True

-- 字符常量模式
isVowel :: Char -> Bool
isVowel 'a' = True
isVowel 'e' = True
isVowel 'i' = True
isVowel 'o' = True
isVowel 'u' = True
isVowel _ = False

-- 字符串常量模式
greet :: String -> String
greet "Alice" = "Hello, Alice!"
greet "Bob" = "Hi, Bob!"
greet name = "Hello, " ++ name ++ "!"
```

### 1.3 构造函数模式

**定义 1.3 (构造函数模式)**
构造函数模式匹配代数数据类型的构造器。

**数学基础：**
$$\text{ConstructorPattern}(C, p_1, p_2, \ldots, p_n) : \text{Value} \rightarrow \text{MatchResult}$$

**Haskell实现：**

```haskell
-- Maybe类型模式匹配
safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x

-- Either类型模式匹配
handleResult :: Either String Int -> String
handleResult (Left error) = "Error: " ++ error
handleResult (Right value) = "Success: " ++ show value

-- 自定义数据类型
data Shape
  = Circle Double
  | Rectangle Double Double
  | Triangle Double Double Double
  deriving (Show, Eq)

-- 形状面积计算
area :: Shape -> Double
area (Circle r) = pi * r * r
area (Rectangle w h) = w * h
area (Triangle a b c) = 
  let s = (a + b + c) / 2
  in sqrt (s * (s - a) * (s - b) * (s - c))

-- 列表模式匹配
listLength :: [a] -> Int
listLength [] = 0
listLength (_:xs) = 1 + listLength xs

-- 元组模式匹配
swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

-- 嵌套模式匹配
nestedMatch :: Maybe (Either String Int) -> String
nestedMatch Nothing = "No value"
nestedMatch (Just (Left error)) = "Error: " ++ error
nestedMatch (Just (Right value)) = "Value: " ++ show value
```

## 🔧 2. 高级模式匹配

### 2.1 列表模式

**定义 2.1 (列表模式)**
列表模式匹配列表的结构，包括空列表和cons模式。

**数学定义：**
$$\text{ListPattern} ::= [] \mid (x:xs) \mid [x_1, x_2, \ldots, x_n]$$

**Haskell实现：**

```haskell
-- 空列表模式
isEmpty :: [a] -> Bool
isEmpty [] = True
isEmpty _ = False

-- Cons模式
head' :: [a] -> Maybe a
head' [] = Nothing
head' (x:_) = Just x

tail' :: [a] -> Maybe [a]
tail' [] = Nothing
tail' (_:xs) = Just xs

-- 多元素模式
firstTwo :: [a] -> Maybe (a, a)
firstTwo [] = Nothing
firstTwo [_] = Nothing
firstTwo (x:y:_) = Just (x, y)

-- 列表解构
sumList :: [Int] -> Int
sumList [] = 0
sumList (x:xs) = x + sumList xs

-- 模式匹配与递归
reverse' :: [a] -> [a]
reverse' [] = []
reverse' (x:xs) = reverse' xs ++ [x]

-- 列表推导式中的模式匹配
extractPairs :: [(a, b)] -> [a]
extractPairs [] = []
extractPairs ((x, _):xs) = x : extractPairs xs
```

### 2.2 记录模式

**定义 2.2 (记录模式)**
记录模式匹配记录类型的字段。

**数学基础：**
$$\text{RecordPattern} : \text{Record} \rightarrow \text{FieldValues}$$

**Haskell实现：**

```haskell
-- 记录类型定义
data Person = Person
  { name :: String
  , age :: Int
  , email :: String
  } deriving (Show, Eq)

-- 记录模式匹配
getName :: Person -> String
getName Person{name = n} = n

getAge :: Person -> Int
getAge Person{age = a} = a

-- 部分字段匹配
getContact :: Person -> String
getContact Person{name = n, email = e} = n ++ " <" ++ e ++ ">"

-- 更新记录
updateAge :: Person -> Int -> Person
updateAge person newAge = person { age = newAge }

-- 嵌套记录
data Address = Address
  { street :: String
  , city :: String
  , country :: String
  } deriving (Show, Eq)

data Employee = Employee
  { person :: Person
  , address :: Address
  , salary :: Double
  } deriving (Show, Eq)

-- 嵌套记录模式匹配
getEmployeeCity :: Employee -> String
getEmployeeCity Employee{address = Address{city = c}} = c

getEmployeeInfo :: Employee -> (String, String, Double)
getEmployeeInfo Employee{person = Person{name = n}, address = Address{city = c}, salary = s} = (n, c, s)
```

### 2.3 守卫表达式

**定义 2.3 (守卫表达式)**
守卫表达式使用布尔条件来扩展模式匹配的能力。

**数学定义：**
$$\text{Guard} ::= \text{Pattern} \mid \text{Pattern} \mid \text{Guard} \text{ where } \text{Expression}$$

**Haskell实现：**

```haskell
-- 基本守卫表达式
absolute :: Int -> Int
absolute x
  | x < 0 = -x
  | otherwise = x

-- 多重守卫
grade :: Int -> String
grade score
  | score >= 90 = "A"
  | score >= 80 = "B"
  | score >= 70 = "C"
  | score >= 60 = "D"
  | otherwise = "F"

-- 复杂守卫条件
isValidTriangle :: Double -> Double -> Double -> Bool
isValidTriangle a b c
  | a <= 0 || b <= 0 || c <= 0 = False
  | a + b <= c = False
  | b + c <= a = False
  | a + c <= b = False
  | otherwise = True

-- 守卫与模式匹配结合
analyzeList :: [Int] -> String
analyzeList []
  | True = "Empty list"
analyzeList [x]
  | x > 0 = "Single positive element"
  | x < 0 = "Single negative element"
  | otherwise = "Single zero"
analyzeList (x:y:xs)
  | x < y = "First element is smaller"
  | x > y = "First element is larger"
  | otherwise = "First two elements are equal"

-- 使用where子句
calculateTax :: Double -> Double
calculateTax income
  | income <= 50000 = tax
  | income <= 100000 = tax + additionalTax
  | otherwise = tax + additionalTax + extraTax
  where
    tax = income * 0.15
    additionalTax = (income - 50000) * 0.25
    extraTax = (income - 100000) * 0.35
```

## 📊 3. 视图模式

### 3.1 视图模式基础

**定义 3.1 (视图模式)**
视图模式允许在模式匹配中使用函数转换。

**数学基础：**
$$\text{ViewPattern} : \text{Function} \rightarrow \text{Pattern} \rightarrow \text{MatchResult}$$

**Haskell实现：**

```haskell
{-# LANGUAGE ViewPatterns #-}

-- 基本视图模式
isEven :: Int -> Bool
isEven (mod 2 -> 0) = True
isEven _ = False

isOdd :: Int -> Bool
isOdd (mod 2 -> 1) = True
isOdd _ = False

-- 字符串视图模式
startsWith :: String -> String -> Bool
startsWith prefix (take (length prefix) -> start) = start == prefix

endsWith :: String -> String -> Bool
endsWith suffix str = drop (length str - length suffix) str == suffix

-- 列表视图模式
hasAtLeast :: Int -> [a] -> Bool
hasAtLeast n (take n -> xs) = length xs == n

-- 自定义视图函数
data Complex = Complex Double Double deriving (Show, Eq)

magnitude :: Complex -> Double
magnitude (Complex r i) = sqrt (r*r + i*i)

phase :: Complex -> Double
phase (Complex r i) = atan2 i r

-- 使用视图模式匹配复数
isReal :: Complex -> Bool
isReal (phase -> 0) = True
isReal (phase -> pi) = True
isReal _ = False

isImaginary :: Complex -> Bool
isImaginary (phase -> p) = abs (p - pi/2) < 1e-10 || abs (p + pi/2) < 1e-10
```

### 3.2 模式同义词

**定义 3.2 (模式同义词)**
模式同义词为复杂的模式提供简化的名称。

**Haskell实现：**

```haskell
{-# LANGUAGE PatternSynonyms #-}

-- 基本模式同义词
pattern Empty = []
pattern Single x = [x]
pattern Double x y = [x, y]

-- 使用模式同义词
isEmpty' :: [a] -> Bool
isEmpty' Empty = True
isEmpty' _ = False

getFirstTwo :: [a] -> Maybe (a, a)
getFirstTwo Double x y = Just (x, y)
getFirstTwo _ = Nothing

-- 双向模式同义词
pattern Head x <- (head -> x)
pattern Head x = [x]

-- 记录模式同义词
data Point = Point { x :: Double, y :: Double } deriving (Show, Eq)

pattern Origin = Point 0 0
pattern OnXAxis y = Point 0 y
pattern OnYAxis x = Point x 0

-- 使用记录模式同义词
distanceFromOrigin :: Point -> Double
distanceFromOrigin Origin = 0
distanceFromOrigin (Point x y) = sqrt (x*x + y*y)

isOnAxis :: Point -> Bool
isOnAxis Origin = True
isOnAxis OnXAxis{} = True
isOnAxis OnYAxis{} = True
isOnAxis _ = False
```

## 🎯 4. 实际应用

### 4.1 数据结构操作

```haskell
-- 二叉树模式匹配
data Tree a
  = Leaf
  | Node a (Tree a) (Tree a)
  deriving (Show, Eq)

-- 树的高度
treeHeight :: Tree a -> Int
treeHeight Leaf = 0
treeHeight (Node _ left right) = 1 + max (treeHeight left) (treeHeight right)

-- 树的节点数
treeSize :: Tree a -> Int
treeSize Leaf = 0
treeSize (Node _ left right) = 1 + treeSize left + treeSize right

-- 树的遍历
inorder :: Tree a -> [a]
inorder Leaf = []
inorder (Node x left right) = inorder left ++ [x] ++ inorder right

preorder :: Tree a -> [a]
preorder Leaf = []
preorder (Node x left right) = [x] ++ preorder left ++ preorder right

postorder :: Tree a -> [a]
postorder Leaf = []
postorder (Node x left right) = postorder left ++ postorder right ++ [x]

-- 查找元素
treeContains :: Eq a => a -> Tree a -> Bool
treeContains _ Leaf = False
treeContains x (Node y left right)
  | x == y = True
  | x < y = treeContains x left
  | otherwise = treeContains x right
```

### 4.2 状态机实现

```haskell
-- 状态机数据类型
data State = Idle | Running | Paused | Stopped deriving (Show, Eq)
data Event = Start | Pause | Resume | Stop deriving (Show, Eq)

-- 状态转换函数
transition :: State -> Event -> Maybe State
transition Idle Start = Just Running
transition Running Pause = Just Paused
transition Running Stop = Just Stopped
transition Paused Resume = Just Running
transition Paused Stop = Just Stopped
transition _ _ = Nothing

-- 状态机执行
executeStateMachine :: [Event] -> State -> [State]
executeStateMachine [] state = [state]
executeStateMachine (event:events) state = 
  case transition state event of
    Just newState -> state : executeStateMachine events newState
    Nothing -> [state]  -- 无效转换，停止执行

-- 状态验证
isValidTransition :: State -> Event -> Bool
isValidTransition state event = 
  case transition state event of
    Just _ -> True
    Nothing -> False
```

### 4.3 解析器实现

```haskell
-- 简单表达式解析
data Expr
  = Number Int
  | Add Expr Expr
  | Sub Expr Expr
  | Mul Expr Expr
  deriving (Show, Eq)

-- 表达式求值
eval :: Expr -> Int
eval (Number n) = n
eval (Add e1 e2) = eval e1 + eval e2
eval (Sub e1 e2) = eval e1 - eval e2
eval (Mul e1 e2) = eval e1 * eval e2

-- 表达式优化
optimize :: Expr -> Expr
optimize (Add (Number 0) e) = optimize e
optimize (Add e (Number 0)) = optimize e
optimize (Mul (Number 1) e) = optimize e
optimize (Mul e (Number 1)) = optimize e
optimize (Mul (Number 0) _) = Number 0
optimize (Mul _ (Number 0)) = Number 0
optimize (Add e1 e2) = Add (optimize e1) (optimize e2)
optimize (Sub e1 e2) = Sub (optimize e1) (optimize e2)
optimize (Mul e1 e2) = Mul (optimize e1) (optimize e2)
optimize e = e
```

## 📈 5. 性能优化

### 5.1 模式匹配优化

```haskell
-- 模式匹配顺序优化
optimizedMatch :: Int -> String
optimizedMatch 0 = "Zero"  -- 最常见的情况放在前面
optimizedMatch 1 = "One"
optimizedMatch 2 = "Two"
optimizedMatch n = "Other: " ++ show n

-- 使用模式同义词优化
pattern Zero = 0
pattern One = 1
pattern Two = 2

optimizedMatch' :: Int -> String
optimizedMatch' Zero = "Zero"
optimizedMatch' One = "One"
optimizedMatch' Two = "Two"
optimizedMatch' n = "Other: " ++ show n

-- 避免重复计算
efficientMatch :: [Int] -> Int
efficientMatch [] = 0
efficientMatch [x] = x
efficientMatch (x:y:xs) = x + y + sum xs  -- 避免重复计算sum
```

### 5.2 编译时优化

```haskell
-- 使用GHC优化
{-# OPTIONS_GHC -O2 #-}

-- 严格模式匹配
{-# LANGUAGE BangPatterns #-}

strictMatch :: [Int] -> Int
strictMatch [] = 0
strictMatch (!x:xs) = x + strictMatch xs

-- 内联模式匹配
{-# INLINE inlineMatch #-}
inlineMatch :: Int -> Bool
inlineMatch 0 = True
inlineMatch _ = False
```

## 🎯 总结

Haskell的模式匹配提供了：

1. **强大的数据解构**：轻松分解复杂数据结构
2. **类型安全**：编译时检查模式完整性
3. **可读性**：代码意图清晰明确
4. **性能优化**：编译器可以优化模式匹配
5. **扩展性**：支持视图模式和模式同义词

模式匹配是Haskell函数式编程的核心，它使得代码更加简洁、安全和高效。

---

**相关文档**:

- [函数式编程基础](./001-Functional-Programming-Foundation.md)
- [递归和列表](./003-Recursion-and-Lists.md)
- [高阶函数](./004-Higher-Order-Functions.md)

**实现示例**:

- [数据结构](./06-Data-Structures/001-Basic-Data-Structures.md)
- [算法实现](./07-Algorithms/001-Sorting-Algorithms.md)
