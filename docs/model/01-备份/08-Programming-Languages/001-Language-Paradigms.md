# 编程语言范式

## 概述

编程语言范式是编程语言设计和使用的理论基础，不同的范式反映了不同的计算模型和思维方式。

## 1. 函数式编程范式

### 1.1 核心概念

函数式编程将计算过程视为数学函数的求值，避免状态和可变数据。

```haskell
-- 纯函数示例
add :: Num a => a -> a -> a
add x y = x + y

-- 高阶函数
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs
```

### 1.2 类型系统

```haskell
-- 代数数据类型
data Maybe a = Nothing | Just a
data Either a b = Left a | Right b

-- 类型类
class Eq a where
  (==) :: a -> a -> Bool
```

## 2. 命令式编程范式

基于可变状态和顺序执行的编程范式。

## 3. 逻辑编程范式

基于逻辑推理的声明式编程。

## 4. 面向对象编程范式

基于对象、封装和继承的编程范式。

---

**相关链接**：

- [Haskell深度解析](./003-Haskell-Deep-Dive.md)
- [语言对比](./002-Language-Comparison.md)

## 5. 并发编程范式

### 5.1 函数式并发

```haskell
-- Software Transactional Memory (STM)
import Control.Concurrent.STM

type Account = TVar Double

transfer :: Account -> Account -> Double -> STM ()
transfer from to amount = do
  fromBalance <- readTVar from
  when (fromBalance >= amount) $ do
    writeTVar from (fromBalance - amount)
    toBalance <- readTVar to
    writeTVar to (toBalance + amount)

-- 使用
main :: IO ()
main = do
  account1 <- newTVarIO 100.0
  account2 <- newTVarIO 50.0
  atomically $ transfer account1 account2 30.0
```

### 5.2 异步编程

```haskell
-- 使用async库
import Control.Concurrent.Async

parallelMap :: (a -> b) -> [a] -> IO [b]
parallelMap f xs = mapConcurrently f xs

-- 示例
main :: IO ()
main = do
  results <- parallelMap (\x -> x * x) [1..1000]
  print $ sum results
```

## 6. 领域特定语言（DSL）

### 6.1 嵌入式DSL

```haskell
-- 简单的查询DSL
data Query a = Select [String] (Table a)
             | Where (Query a) (Condition a)
             | Join (Query a) (Query a) (JoinCondition a)

data Table a = Table String
data Condition a = Eq String String
data JoinCondition a = On String String

-- 使用
query :: Query User
query = Select ["name", "email"] (Table "users")
     `Where` (Eq "age" "25")
```

## 7. 形式化语义

### 7.1 操作语义

```haskell
-- 简单的表达式语言
data Expr = Lit Int
          | Add Expr Expr
          | Mul Expr Expr

-- 求值函数
eval :: Expr -> Int
eval (Lit n) = n
eval (Add e1 e2) = eval e1 + eval e2
eval (Mul e1 e2) = eval e1 * eval e2
```

### 7.2 指称语义

```haskell
-- 环境
type Env = [(String, Int)]

-- 指称语义
evalDenot :: Expr -> Env -> Int
evalDenot (Lit n) _ = n
evalDenot (Var x) env = case lookup x env of
  Just v -> v
  Nothing -> error $ "Undefined variable: " ++ x
evalDenot (Add e1 e2) env = evalDenot e1 env + evalDenot e2 env
```

## 8. 类型理论

### 8.1 简单类型λ演算

```haskell
-- 类型定义
data Type = TInt | TBool | TArrow Type Type

-- 项定义
data Term = Var String
          | Lam String Type Term
          | App Term Term
          | LitInt Int
          | LitBool Bool

-- 类型检查
type Context = [(String, Type)]

typeCheck :: Context -> Term -> Maybe Type
typeCheck ctx (Var x) = lookup x ctx
typeCheck ctx (Lam x t body) = do
  bodyType <- typeCheck ((x, t) : ctx) body
  return $ TArrow t bodyType
typeCheck ctx (App f arg) = do
  fType <- typeCheck ctx f
  argType <- typeCheck ctx arg
  case fType of
    TArrow t1 t2 | t1 == argType -> Just t2
    _ -> Nothing
```

## 9. 总结

编程语言范式反映了不同的计算模型和思维方式：

1. **函数式编程**：强调纯函数、不可变性和高阶函数
2. **命令式编程**：基于状态变化和顺序执行
3. **逻辑编程**：基于逻辑推理和声明式编程
4. **面向对象编程**：基于对象、封装和继承

Haskell作为纯函数式编程语言的代表，提供了强大的类型系统、惰性求值和函数式编程特性，使其成为研究编程语言理论和实践的重要工具。

## 10. 进一步阅读

- [Haskell 98 Language Report](https://www.haskell.org/onlinereport/)
- [Type Theory and Functional Programming](https://www.cs.kent.ac.uk/people/staff/sjt/TTFP/)
- [Category Theory in Context](https://math.jhu.edu/~eriehl/context.pdf)

---

**相关链接**：

- [Haskell深度解析](./003-Haskell-Deep-Dive.md)
- [语言对比](./002-Language-Comparison.md)
- [类型理论](./../03-Theory/002-Linear-Type-Theory.md)
