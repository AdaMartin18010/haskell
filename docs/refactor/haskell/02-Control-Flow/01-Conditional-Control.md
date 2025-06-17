# Haskell 条件控制

## 概述

Haskell中的条件控制主要通过守卫（guards）、if-then-else表达式和模式匹配实现。本文档详细介绍这些条件控制机制及其形式化语义。

## 1. 守卫（Guards）

### 1.1 基本守卫语法

```haskell
-- 基本守卫语法
absolute :: Int -> Int
absolute x
  | x >= 0    = x
  | otherwise = -x

-- 多条件守卫
grade :: Int -> String
grade score
  | score >= 90 = "A"
  | score >= 80 = "B"
  | score >= 70 = "C"
  | score >= 60 = "D"
  | otherwise   = "F"
```

### 1.2 复杂守卫条件

```haskell
-- 使用逻辑运算符的守卫
isValidTriangle :: Double -> Double -> Double -> Bool
isValidTriangle a b c
  | a <= 0 || b <= 0 || c <= 0 = False
  | a + b <= c = False
  | a + c <= b = False
  | b + c <= a = False
  | otherwise = True

-- 使用函数调用的守卫
isPrime :: Int -> Bool
isPrime n
  | n < 2 = False
  | n == 2 = True
  | even n = False
  | otherwise = not $ any (\x -> n `mod` x == 0) [3,5..floor $ sqrt $ fromIntegral n]
```

## 2. if-then-else表达式

### 2.1 基本if表达式

```haskell
-- 基本if表达式
max' :: Ord a => a -> a -> a
max' x y = if x > y then x else y

-- 嵌套if表达式
sign :: Int -> String
sign x = if x > 0 
         then "positive" 
         else if x < 0 
              then "negative" 
              else "zero"
```

### 2.2 函数式if表达式

```haskell
-- 使用if表达式的函数组合
processNumber :: Int -> String
processNumber n = 
  if even n 
  then "even: " ++ show (n `div` 2)
  else "odd: " ++ show (n * 3 + 1)

-- 条件函数选择
conditionalFunction :: Bool -> (Int -> Int) -> (Int -> Int) -> Int -> Int
conditionalFunction b f g x = if b then f x else g x
```

## 3. 模式匹配条件控制

### 3.1 数据类型模式匹配

```haskell
-- 代数数据类型的模式匹配
data Shape = Circle Double | Rectangle Double Double | Triangle Double Double Double

area :: Shape -> Double
area (Circle r) = pi * r * r
area (Rectangle w h) = w * h
area (Triangle a b c) = 
  let s = (a + b + c) / 2
  in sqrt (s * (s - a) * (s - b) * (s - c))

-- Maybe类型的模式匹配
safeDivide :: Double -> Double -> Maybe Double
safeDivide _ 0 = Nothing
safeDivide x y = Just (x / y)

processResult :: Maybe Double -> String
processResult Nothing = "Division by zero"
processResult (Just result) = "Result: " ++ show result
```

### 3.2 列表模式匹配

```haskell
-- 列表长度检查
isEmpty :: [a] -> Bool
isEmpty [] = True
isEmpty _ = False

-- 列表元素处理
processList :: [Int] -> String
processList [] = "Empty list"
processList [x] = "Single element: " ++ show x
processList (x:y:xs) = "Multiple elements starting with: " ++ show x ++ ", " ++ show y
```

## 4. case表达式

### 4.1 基本case表达式

```haskell
-- 基本case表达式
describeNumber :: Int -> String
describeNumber n = case n of
  0 -> "zero"
  1 -> "one"
  2 -> "two"
  _ -> "other"

-- 模式匹配case表达式
analyzeList :: [a] -> String
analyzeList xs = case xs of
  [] -> "Empty list"
  [x] -> "Single element list"
  (x:y:[]) -> "Two element list"
  (x:y:z:_) -> "List with at least three elements"
```

### 4.2 复杂case表达式

```haskell
-- 嵌套case表达式
complexAnalysis :: Either String (Maybe Int) -> String
complexAnalysis value = case value of
  Left err -> "Error: " ++ err
  Right maybeVal -> case maybeVal of
    Nothing -> "No value"
    Just n -> "Value: " ++ show n

-- 使用where子句的case表达式
processData :: [Int] -> String
processData xs = case xs of
  [] -> "Empty"
  (x:xs') -> 
    let sum = x + total xs'
        count = 1 + length xs'
    in "Sum: " ++ show sum ++ ", Count: " ++ show count
  where
    total = sum
```

## 5. 条件控制的形式化语义

### 5.1 守卫语义

守卫的语义可以形式化为：

$$\text{guard}(e, [(p_1, e_1), (p_2, e_2), \ldots, (p_n, e_n)]) = \begin{cases}
e_1 & \text{if } p_1(e) \\
e_2 & \text{if } p_2(e) \\
\vdots \\
e_n & \text{if } p_n(e) \\
\bot & \text{otherwise}
\end{cases}$$

### 5.2 if表达式语义

if表达式的语义定义为：

$$\text{if}(c, e_1, e_2) = \begin{cases}
e_1 & \text{if } c = \text{True} \\
e_2 & \text{if } c = \text{False} \\
\bot & \text{otherwise}
\end{cases}$$

### 5.3 模式匹配语义

模式匹配的语义：

$$\text{match}(v, p) = \begin{cases}
\text{Just } \sigma & \text{if } v \text{ matches } p \text{ with substitution } \sigma \\
\text{Nothing} & \text{otherwise}
\end{cases}$$

## 6. 高级条件控制技术

### 6.1 条件函数组合

```haskell
-- 条件函数管道
conditionalPipeline :: Int -> String
conditionalPipeline n =
  (if n > 0 then ("positive: " ++) else ("negative: " ++)) .
  (if even n then ("even: " ++) else ("odd: " ++)) $
  show n

-- 条件函数选择器
type Condition a = a -> Bool
type Action a b = a -> b

conditionalAction :: Condition a -> Action a b -> Action a b -> Action a b
conditionalAction cond action1 action2 x =
  if cond x then action1 x else action2 x
```

### 6.2 条件数据结构

```haskell
-- 条件数据结构
data Conditional a =
  When Bool a |
  Otherwise a

evaluate :: Conditional a -> a
evaluate (When True a) = a
evaluate (When False _) = error "Condition not met"
evaluate (Otherwise a) = a

-- 条件列表处理
conditionalMap :: (a -> Bool) -> (a -> b) -> (a -> b) -> [a] -> [b]
conditionalMap cond f1 f2 = map (\x -> if cond x then f1 x else f2 x)
```

## 7. 实践示例

### 7.1 简单计算器

```haskell
-- 计算器操作
data Operation = Add | Subtract | Multiply | Divide

calculate :: Operation -> Double -> Double -> Maybe Double
calculate op x y = case op of
  Add -> Just (x + y)
  Subtract -> Just (x - y)
  Multiply -> Just (x * y)
  Divide -> if y /= 0 then Just (x / y) else Nothing

-- 计算器界面
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

### 7.2 数据验证系统

```haskell
-- 数据验证类型
data ValidationResult = Valid | Invalid String

-- 验证函数
validateAge :: Int -> ValidationResult
validateAge age
  | age < 0 = Invalid "Age cannot be negative"
  | age > 150 = Invalid "Age seems unrealistic"
  | otherwise = Valid

validateEmail :: String -> ValidationResult
validateEmail email
  | '@' `notElem` email = Invalid "Email must contain @"
  | '.' `notElem` email = Invalid "Email must contain ."
  | length email < 5 = Invalid "Email too short"
  | otherwise = Valid

-- 组合验证
validateUser :: Int -> String -> ValidationResult
validateUser age email = case (validateAge age, validateEmail email) of
  (Valid, Valid) -> Valid
  (Invalid msg, _) -> Invalid $ "Age: " ++ msg
  (_, Invalid msg) -> Invalid $ "Email: " ++ msg
```

## 8. 性能考虑

### 8.1 守卫vs if表达式

```haskell
-- 守卫通常更清晰
gradeGuard :: Int -> String
gradeGuard score
  | score >= 90 = "A"
  | score >= 80 = "B"
  | score >= 70 = "C"
  | score >= 60 = "D"
  | otherwise = "F"

-- if表达式在某些情况下更合适
gradeIf :: Int -> String
gradeIf score = if score >= 90 then "A"
                else if score >= 80 then "B"
                else if score >= 70 then "C"
                else if score >= 60 then "D"
                else "F"
```

### 8.2 模式匹配优化

```haskell
-- 优化的模式匹配
efficientProcess :: [Int] -> Int
efficientProcess [] = 0
efficientProcess [x] = x
efficientProcess (x:y:xs) = x + y + sum xs

-- 避免重复计算
optimizedAnalysis :: [Int] -> String
optimizedAnalysis xs =
  let len = length xs
      sum = sum xs
      avg = fromIntegral sum / fromIntegral len
  in case len of
       0 -> "Empty list"
       1 -> "Single element: " ++ show sum
       _ -> "Average: " ++ show avg
```

## 总结

Haskell的条件控制机制包括：

1. **守卫**：清晰的多条件分支
2. **if表达式**：简单的二元选择
3. **模式匹配**：基于数据结构的条件控制
4. **case表达式**：复杂的模式匹配控制

这些机制提供了强大而灵活的条件控制能力，支持函数式编程的纯函数特性。

## 相关链接

- [语法基础](../01-Basic-Concepts/03-Syntax-Basics.md)
- [执行流](../03-Execution-Flow/01-Function-Execution.md)
- [类型系统](../05-Type-System/01-Basic-Types.md)
- [设计模式](../06-Design-Patterns/01-Functional-Patterns.md)

---

**最后更新**: 2024年12月  
**版本**: 1.0.0
