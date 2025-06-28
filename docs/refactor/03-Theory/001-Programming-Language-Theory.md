# 编程语言理论

## 概述

编程语言理论研究编程语言的设计、语义和实现。

## 形式语义

### 操作语义

```haskell
-- 简单表达式语言
data Expr = Lit Int
          | Add Expr Expr
          | Mul Expr Expr

-- 求值函数
eval :: Expr -> Int
eval (Lit n) = n
eval (Add e1 e2) = eval e1 + eval e2
eval (Mul e1 e2) = eval e1 * eval e2
```

### 指称语义

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

## 类型理论

### 简单类型λ演算

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

## 编译原理

### 词法分析

```haskell
-- 词法单元
data Token = TInt Int
           | TPlus
           | TMinus
           | TTimes
           | TLParen
           | TRParen
           | TEOF

-- 词法分析器
lexer :: String -> [Token]
lexer = undefined -- 实现词法分析
```

### 语法分析

```haskell
-- 抽象语法树
data AST = Num Int
         | BinOp AST Op AST

data Op = Add | Sub | Mul

-- 递归下降解析器
parse :: [Token] -> Maybe AST
parse = undefined -- 实现语法分析
```

## 应用

- 语言设计
- 编译器实现
- 程序分析
- 形式化验证

---

**相关链接**：

- [线性类型理论](./002-Linear-Type-Theory.md)
- [仿射类型理论](./003-Affine-Type-Theory.md)
