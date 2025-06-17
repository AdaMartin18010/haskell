# Haskell 条件表达式

## 概述

条件表达式是Haskell中控制程序执行流程的基础构造，基于模式匹配和守卫表达式实现。

## 数学定义

### 条件表达式形式化定义

给定类型 $A$ 和 $B$，条件表达式定义为：

$$\text{if} : \text{Bool} \times A \times A \rightarrow A$$

其中：
- $\text{Bool}$ 是布尔类型
- $A$ 是任意类型
- 满足：$\text{if}(b, x, y) = \begin{cases} x & \text{if } b = \text{True} \\ y & \text{if } b = \text{False} \end{cases}$

### 守卫表达式形式化定义

守卫表达式定义为：

$$\text{guard} : (A \rightarrow \text{Bool}) \times A \rightarrow A$$

## Haskell实现

### 基础条件表达式

```haskell
-- 基础if-then-else表达式
module ControlFlow.Conditional where

-- 简单条件表达式
absoluteValue :: Num a => a -> a
absoluteValue x = if x >= 0 then x else -x

-- 多条件表达式
grade :: Int -> String
grade score = if score >= 90 then "A"
              else if score >= 80 then "B"
              else if score >= 70 then "C"
              else if score >= 60 then "D"
              else "F"

-- 条件表达式的类型安全
safeDivide :: (Fractional a, Eq a) => a -> a -> Maybe a
safeDivide x y = if y == 0 then Nothing else Just (x / y)
```

### 守卫表达式

```haskell
-- 使用守卫表达式的函数
absoluteValue' :: Num a => a -> a
absoluteValue' x
  | x >= 0    = x
  | otherwise = -x

-- 多条件守卫
grade' :: Int -> String
grade' score
  | score >= 90 = "A"
  | score >= 80 = "B"
  | score >= 70 = "C"
  | score >= 60 = "D"
  | otherwise   = "F"

-- 复杂条件守卫
classifyNumber :: (Ord a, Num a) => a -> String
classifyNumber x
  | x < 0     = "Negative"
  | x == 0    = "Zero"
  | x < 10    = "Small positive"
  | x < 100   = "Medium positive"
  | otherwise = "Large positive"
```

### 模式匹配条件

```haskell
-- 基于模式匹配的条件
data Shape = Circle Double | Rectangle Double Double | Triangle Double Double Double

area :: Shape -> Double
area (Circle r) = pi * r * r
area (Rectangle w h) = w * h
area (Triangle a b c) = 
  let s = (a + b + c) / 2
  in sqrt (s * (s - a) * (s - b) * (s - c))

-- 列表模式匹配
safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x

-- 元组模式匹配
processTuple :: (Int, String) -> String
processTuple (0, msg) = "Zero: " ++ msg
processTuple (n, msg) = "Number " ++ show n ++ ": " ++ msg
```

### 高级条件表达式

```haskell
-- 条件表达式与高阶函数结合
conditionalMap :: (a -> Bool) -> (a -> b) -> (a -> b) -> [a] -> [b]
conditionalMap pred f1 f2 = map (\x -> if pred x then f1 x else f2 x)

-- 使用示例
processNumbers :: [Int] -> [String]
processNumbers = conditionalMap 
  (> 0) 
  (\x -> "Positive: " ++ show x)
  (\x -> "Non-positive: " ++ show x)

-- 条件表达式与单子结合
conditionalIO :: Bool -> IO String
conditionalIO b = if b 
  then putStrLn "True branch" >> return "True"
  else putStrLn "False branch" >> return "False"

-- 条件表达式与Applicative结合
conditionalApply :: Bool -> (a -> b) -> a -> Maybe b
conditionalApply b f x = if b then Just (f x) else Nothing
```

## 形式化语义

### 条件表达式的语义

```haskell
-- 条件表达式的语义定义
data ConditionalSemantics a = 
  ConditionalSemantics 
    { condition :: Bool
    , trueBranch :: a
    , falseBranch :: a
    , result :: a
    }

-- 语义解释函数
interpretConditional :: ConditionalSemantics a -> a
interpretConditional (ConditionalSemantics c t f _) = 
  if c then t else f

-- 条件表达式的代数性质
class ConditionalAlgebra a where
  -- 单位元
  unit :: a
  -- 条件组合
  conditional :: Bool -> a -> a -> a
  -- 分配律
  distribute :: (a -> b) -> a -> a -> Bool -> b
```

### 守卫表达式的语义

```haskell
-- 守卫表达式的语义
data GuardSemantics a = 
  GuardSemantics 
    { predicates :: [a -> Bool]
    , expressions :: [a -> a]
    , defaultExpr :: a -> a
    }

-- 守卫表达式解释器
interpretGuard :: GuardSemantics a -> a -> a
interpretGuard (GuardSemantics preds exprs def) x =
  case findIndex (\p -> p x) preds of
    Just i -> (exprs !! i) x
    Nothing -> def x
```

## 类型安全保证

### 条件表达式的类型系统

```haskell
-- 条件表达式的类型检查
class TypeSafeConditional a where
  type ConditionType a
  type ResultType a
  
  -- 类型安全的条件表达式
  typeSafeIf :: ConditionType a -> ResultType a -> ResultType a -> ResultType a
  
  -- 类型安全的守卫
  typeSafeGuard :: (a -> ConditionType a) -> (a -> ResultType a) -> a -> ResultType a

-- 实例化
instance TypeSafeConditional Int where
  type ConditionType Int = Bool
  type ResultType Int = Int
  
  typeSafeIf c t f = if c then t else f
  typeSafeGuard p f x = if p x then f x else x
```

## 性能优化

### 惰性求值优化

```haskell
-- 利用惰性求值优化条件表达式
lazyConditional :: Bool -> a -> a -> a
lazyConditional b t f = 
  -- 只有被选择的分支会被求值
  if b then t else f

-- 避免不必要的计算
expensiveComputation :: Int -> Int
expensiveComputation n = 
  if n <= 0 
    then 0  -- 避免计算
    else sum [1..n]  -- 只在需要时计算

-- 条件表达式的记忆化
memoizedConditional :: (Int -> Bool) -> (Int -> Int) -> (Int -> Int) -> Int -> Int
memoizedConditional pred f1 f2 = 
  let memo = \n -> if pred n then f1 n else f2 n
  in memo
```

## 实际应用

### 业务逻辑中的条件表达式

```haskell
-- 用户权限检查
data User = User 
  { userId :: Int
  , userRole :: String
  , userPermissions :: [String]
  }

checkPermission :: User -> String -> Bool
checkPermission user permission
  | userRole user == "admin" = True
  | permission `elem` userPermissions user = True
  | otherwise = False

-- 订单处理逻辑
data Order = Order 
  { orderId :: Int
  , orderAmount :: Double
  , orderStatus :: String
  }

processOrder :: Order -> String
processOrder order
  | orderAmount order > 1000 = "High value order - manual review required"
  | orderStatus order == "pending" = "Order is pending"
  | orderAmount order > 100 = "Standard order processing"
  | otherwise = "Fast track processing"
```

### 算法中的条件表达式

```haskell
-- 二分查找中的条件表达式
binarySearch :: Ord a => [a] -> a -> Maybe Int
binarySearch [] _ = Nothing
binarySearch xs target = go 0 (length xs - 1)
  where
    go left right
      | left > right = Nothing
      | otherwise = 
          let mid = (left + right) `div` 2
              midVal = xs !! mid
          in if target == midVal
             then Just mid
             else if target < midVal
                  then go left (mid - 1)
                  else go (mid + 1) right

-- 快速排序中的条件表达式
quicksort :: Ord a => [a] -> [a]
quicksort [] = []
quicksort (x:xs) = 
  let smaller = [a | a <- xs, a <= x]
      larger = [a | a <- xs, a > x]
  in quicksort smaller ++ [x] ++ quicksort larger
```

## 总结

Haskell的条件表达式提供了：

1. **类型安全**：编译时检查确保类型正确性
2. **函数式风格**：基于表达式而非语句
3. **模式匹配**：强大的模式匹配能力
4. **惰性求值**：避免不必要的计算
5. **组合性**：易于与其他函数式构造组合

这些特性使得Haskell的条件表达式既安全又高效，是函数式编程中控制流程的核心工具。

---

**相关链接**：
- [函数式编程基础](../01-Basic-Concepts/函数式编程基础.md)
- [模式匹配](../01-Basic-Concepts/模式匹配.md)
- [高阶函数](../02-Control-Flow/高阶函数.md) 