# 简单类型理论基础

## 📋 概述

简单类型理论（Simple Type Theory）是类型理论的基础，它提供了最基本的类型系统框架。简单类型理论将类型和项分离，为函数式编程语言提供了理论基础。

## 🎯 核心概念

### 类型和项

在简单类型理论中，我们区分类型（Types）和项（Terms）：

- **类型**：描述数据的结构
- **项**：具有特定类型的值

### 基本类型

```haskell
-- 基本类型定义
data Type = 
    Unit           -- 单位类型
  | Bool           -- 布尔类型
  | Nat            -- 自然数类型
  | Arrow Type Type -- 函数类型
  | Product Type Type -- 积类型
  | Sum Type Type     -- 和类型
  deriving (Show, Eq)
```

### 类型环境

类型环境（Type Environment）记录变量到类型的映射：

```haskell
-- 类型环境
type TypeEnv = [(String, Type)]

-- 查找变量类型
lookupType :: String -> TypeEnv -> Maybe Type
lookupType var env = lookup var env

-- 扩展类型环境
extendEnv :: String -> Type -> TypeEnv -> TypeEnv
extendEnv var ty env = (var, ty) : env
```

## 🔧 类型规则

### 变量规则

$$
\frac{x : \tau \in \Gamma}{\Gamma \vdash x : \tau} \text{ (Var)}
$$

```haskell
-- 变量类型检查
typeCheckVar :: String -> TypeEnv -> Maybe Type
typeCheckVar var env = lookupType var env
```

### 函数抽象规则

$$
\frac{\Gamma, x : \tau_1 \vdash e : \tau_2}{\Gamma \vdash \lambda x : \tau_1. e : \tau_1 \rightarrow \tau_2} \text{ (Abs)}
$$

```haskell
-- 函数抽象类型检查
typeCheckAbs :: String -> Type -> Expr -> TypeEnv -> Maybe Type
typeCheckAbs var paramType body env = do
  let newEnv = extendEnv var paramType env
  bodyType <- typeCheck body newEnv
  return $ Arrow paramType bodyType
```

### 函数应用规则

$$
\frac{\Gamma \vdash e_1 : \tau_1 \rightarrow \tau_2 \quad \Gamma \vdash e_2 : \tau_1}{\Gamma \vdash e_1 e_2 : \tau_2} \text{ (App)}
$$

```haskell
-- 函数应用类型检查
typeCheckApp :: Expr -> Expr -> TypeEnv -> Maybe Type
typeCheckApp fun arg env = do
  funType <- typeCheck fun env
  argType <- typeCheck arg env
  case funType of
    Arrow paramType resultType
      | paramType == argType -> return resultType
      | otherwise -> Nothing
    _ -> Nothing
```

## 📊 表达式语法

### 表达式定义

```haskell
-- 表达式语法
data Expr = 
    Var String                    -- 变量
  | Lambda String Type Expr       -- 函数抽象
  | App Expr Expr                 -- 函数应用
  | Unit                          -- 单位值
  | Bool Bool                     -- 布尔值
  | Nat Integer                   -- 自然数
  | Pair Expr Expr                -- 有序对
  | Fst Expr                      -- 第一投影
  | Snd Expr                      -- 第二投影
  | Inl Expr                      -- 左注入
  | Inr Expr                      -- 右注入
  | Case Expr String Expr String Expr -- 模式匹配
  deriving (Show, Eq)
```

### 类型检查器

```haskell
-- 类型检查器
typeCheck :: Expr -> TypeEnv -> Maybe Type
typeCheck (Var x) env = typeCheckVar x env
typeCheck (Lambda x ty body) env = typeCheckAbs x ty body env
typeCheck (App fun arg) env = typeCheckApp fun arg env
typeCheck Unit _ = return Unit
typeCheck (Bool _) _ = return Bool
typeCheck (Nat _) _ = return Nat
typeCheck (Pair e1 e2) env = do
  ty1 <- typeCheck e1 env
  ty2 <- typeCheck e2 env
  return $ Product ty1 ty2
typeCheck (Fst e) env = do
  ty <- typeCheck e env
  case ty of
    Product ty1 _ -> return ty1
    _ -> Nothing
typeCheck (Snd e) env = do
  ty <- typeCheck e env
  case ty of
    Product _ ty2 -> return ty2
    _ -> Nothing
typeCheck (Inl e) env = do
  ty <- typeCheck e env
  -- 需要上下文来确定和类型的另一个分支
  return ty
typeCheck (Inr e) env = do
  ty <- typeCheck e env
  -- 需要上下文来确定和类型的另一个分支
  return ty
typeCheck (Case e x1 e1 x2 e2) env = do
  sumType <- typeCheck e env
  -- 简化的实现，实际需要更复杂的类型推导
  ty1 <- typeCheck e1 env
  ty2 <- typeCheck e2 env
  if ty1 == ty2 then return ty1 else Nothing
```

## 🔍 类型安全性和进展性

### 类型安全性定理

**定理**（类型安全性）：如果 $\Gamma \vdash e : \tau$ 且 $e \rightarrow e'$，那么 $\Gamma \vdash e' : \tau$。

**证明**：通过结构归纳法证明。

```haskell
-- 类型安全性检查
typeSafety :: Expr -> TypeEnv -> Bool
typeSafety e env = case typeCheck e env of
  Just _ -> True
  Nothing -> False
```

### 进展性定理

**定理**（进展性）：如果 $\emptyset \vdash e : \tau$，那么 $e$ 要么是一个值，要么可以继续求值。

**证明**：通过结构归纳法证明。

```haskell
-- 进展性检查
isValue :: Expr -> Bool
isValue Unit = True
isValue (Bool _) = True
isValue (Nat _) = True
isValue (Lambda _ _ _) = True
isValue (Pair e1 e2) = isValue e1 && isValue e2
isValue (Inl e) = isValue e
isValue (Inr e) = isValue e
isValue _ = False

canStep :: Expr -> Bool
canStep e = not (isValue e)
```

## 🎯 求值语义

### 小步语义

```haskell
-- 小步求值
step :: Expr -> Maybe Expr
step (App (Lambda x _ body) arg) = 
  if isValue arg then Just (substitute x arg body) else Nothing
step (App fun arg) = 
  if isValue fun then 
    case step arg of
      Just arg' -> Just (App fun arg')
      Nothing -> Nothing
  else
    case step fun of
      Just fun' -> Just (App fun' arg)
      Nothing -> Nothing
step (Fst (Pair e1 e2)) = 
  if isValue e1 && isValue e2 then Just e1 else Nothing
step (Snd (Pair e1 e2)) = 
  if isValue e1 && isValue e2 then Just e2 else Nothing
step (Case (Inl e) x1 e1 x2 e2) = 
  if isValue e then Just (substitute x1 e e1) else Nothing
step (Case (Inr e) x1 e1 x2 e2) = 
  if isValue e then Just (substitute x2 e e2) else Nothing
step _ = Nothing

-- 替换操作
substitute :: String -> Expr -> Expr -> Expr
substitute x v (Var y) = if x == y then v else Var y
substitute x v (Lambda y ty body) = 
  if x == y then Lambda y ty body 
  else Lambda y ty (substitute x v body)
substitute x v (App fun arg) = 
  App (substitute x v fun) (substitute x v arg)
substitute x v (Pair e1 e2) = 
  Pair (substitute x v e1) (substitute x v e2)
substitute x v (Fst e) = Fst (substitute x v e)
substitute x v (Snd e) = Snd (substitute x v e)
substitute x v (Inl e) = Inl (substitute x v e)
substitute x v (Inr e) = Inr (substitute x v e)
substitute x v (Case e y1 e1 y2 e2) = 
  Case (substitute x v e) y1 e1' y2 e2'
  where
    e1' = if x == y1 then e1 else substitute x v e1
    e2' = if x == y2 then e2 else substitute x v e2
substitute _ _ e = e
```

## 📈 示例

### 基本示例

```haskell
-- 示例1：恒等函数
idFunc :: Expr
idFunc = Lambda "x" (Arrow Unit Unit) (Var "x")

-- 示例2：函数应用
example1 :: Expr
example1 = App idFunc Unit

-- 示例3：有序对
example2 :: Expr
example2 = Pair (Nat 1) (Bool True)

-- 示例4：模式匹配
example3 :: Expr
example3 = Case (Inl (Nat 1)) "x" (Var "x") "y" (Var "y")
```

### 类型检查示例

```haskell
-- 类型检查测试
testTypeCheck :: IO ()
testTypeCheck = do
  let env = [("x", Nat)]
  
  putStrLn "=== 类型检查测试 ==="
  
  -- 测试变量
  print $ typeCheck (Var "x") env
  
  -- 测试函数抽象
  print $ typeCheck idFunc []
  
  -- 测试函数应用
  print $ typeCheck example1 []
  
  -- 测试有序对
  print $ typeCheck example2 []
```

## 🔗 相关概念

### 与Haskell的关系

简单类型理论是Haskell类型系统的基础：

```haskell
-- Haskell中的对应概念
-- 函数类型
f :: Int -> Int
f x = x + 1

-- 积类型（元组）
pair :: (Int, Bool)
pair = (1, True)

-- 和类型（Either）
sumType :: Either Int Bool
sumType = Left 1
```

### 与形式逻辑的关系

简单类型理论对应直觉主义逻辑：

- **函数类型** ↔ **蕴含**
- **积类型** ↔ **合取**
- **和类型** ↔ **析取**
- **单位类型** ↔ **真**

## 📚 扩展阅读

- [依赖类型理论](../02-Dependent-Type-Theory/依赖类型理论基础.md)
- [同伦类型理论](../03-Homotopy-Type-Theory/同伦类型理论基础.md)
- [构造类型理论](../04-Constructive-Type-Theory/构造类型理论基础.md)
- [编程语言理论](../../03-Theory/01-Programming-Language-Theory/README.md)

## 🎯 应用

### 编程语言设计

简单类型理论为编程语言设计提供了理论基础：

- **类型安全**：防止运行时类型错误
- **类型推导**：自动推断表达式类型
- **模块化**：通过类型接口实现模块化

### 程序验证

通过类型系统进行程序验证：

- **静态分析**：编译时发现潜在错误
- **形式化验证**：证明程序正确性
- **重构安全**：确保重构不破坏类型安全

---

*简单类型理论为现代函数式编程语言提供了坚实的理论基础，是理解类型系统和程序语义的重要起点。*
