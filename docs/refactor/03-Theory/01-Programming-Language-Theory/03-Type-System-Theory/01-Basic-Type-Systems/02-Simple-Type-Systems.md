# 简单类型系统 (Simple Type Systems)

## 📚 概述

简单类型系统是类型理论的基础，为编程语言提供了基本的类型安全保障。我们研究简单类型λ演算（Simply Typed Lambda Calculus, STLC）及其扩展，建立类型安全的形式化基础。

## 🏗️ 形式化定义

### 简单类型λ演算 (STLC)

#### 语法定义

```haskell
-- 类型语法
data Type = 
    TUnit                    -- 单位类型
  | TBool                    -- 布尔类型
  | TInt                     -- 整数类型
  | TFloat                   -- 浮点类型
  | TArrow Type Type         -- 函数类型 τ₁ → τ₂
  | TProduct Type Type       -- 积类型 τ₁ × τ₂
  | TSum Type Type           -- 和类型 τ₁ + τ₂
  deriving (Eq, Show)

-- 项语法
data Term = 
    Unit                     -- 单位值
  | True | False             -- 布尔值
  | LitInt Int               -- 整数字面量
  | LitFloat Double          -- 浮点字面量
  | Var String               -- 变量
  | Lam String Type Term     -- λ抽象 λx:τ.t
  | App Term Term            -- 应用 t₁ t₂
  | Pair Term Term           -- 序对 (t₁, t₂)
  | Fst Term                 -- 第一投影 fst t
  | Snd Term                 -- 第二投影 snd t
  | Inl Term Type            -- 左注入 inl t : τ₁ + τ₂
  | Inr Type Term            -- 右注入 inr τ₁ t : τ₁ + τ₂
  | Case Term String Term String Term -- case分析
  | If Term Term Term        -- 条件语句
  deriving (Eq, Show)
```

#### 类型环境

```haskell
-- 类型环境：变量到类型的映射
type TypeEnv = [(String, Type)]

-- 空环境
emptyEnv :: TypeEnv
emptyEnv = []

-- 扩展环境
extendEnv :: TypeEnv -> String -> Type -> TypeEnv
extendEnv env x t = (x, t) : env

-- 查找变量类型
lookupType :: TypeEnv -> String -> Maybe Type
lookupType [] _ = Nothing
lookupType ((x', t) : env) x 
  | x == x' = Just t
  | otherwise = lookupType env x
```

#### 类型检查规则

```haskell
-- 类型检查函数
typeCheck :: TypeEnv -> Term -> Maybe Type

-- 单位类型规则
typeCheck _ Unit = Just TUnit

-- 布尔类型规则
typeCheck _ True = Just TBool
typeCheck _ False = Just TBool

-- 整数类型规则
typeCheck _ (LitInt _) = Just TInt

-- 浮点类型规则
typeCheck _ (LitFloat _) = Just TFloat

-- 变量规则
typeCheck env (Var x) = lookupType env x

-- λ抽象规则
typeCheck env (Lam x t1 t2) = do
  t2' <- typeCheck (extendEnv env x t1) t2
  return (TArrow t1 t2')

-- 应用规则
typeCheck env (App t1 t2) = do
  t1' <- typeCheck env t1
  t2' <- typeCheck env t2
  case t1' of
    TArrow t11 t12 | t11 == t2' -> Just t12
    _ -> Nothing

-- 序对规则
typeCheck env (Pair t1 t2) = do
  t1' <- typeCheck env t1
  t2' <- typeCheck env t2
  return (TProduct t1' t2')

-- 第一投影规则
typeCheck env (Fst t) = do
  t' <- typeCheck env t
  case t' of
    TProduct t1 _ -> Just t1
    _ -> Nothing

-- 第二投影规则
typeCheck env (Snd t) = do
  t' <- typeCheck env t
  case t' of
    TProduct _ t2 -> Just t2
    _ -> Nothing

-- 左注入规则
typeCheck env (Inl t t2) = do
  t1 <- typeCheck env t
  return (TSum t1 t2)

-- 右注入规则
typeCheck env (Inr t1 t) = do
  t2 <- typeCheck env t
  return (TSum t1 t2)

-- Case分析规则
typeCheck env (Case t x1 t1 x2 t2) = do
  t' <- typeCheck env t
  case t' of
    TSum t1' t2' -> do
      t1'' <- typeCheck (extendEnv env x1 t1') t1
      t2'' <- typeCheck (extendEnv env x2 t2') t2
      if t1'' == t2'' then Just t1'' else Nothing
    _ -> Nothing

-- 条件语句规则
typeCheck env (If t1 t2 t3) = do
  t1' <- typeCheck env t1
  t2' <- typeCheck env t2
  t3' <- typeCheck env t3
  case t1' of
    TBool | t2' == t3' -> Just t2'
    _ -> Nothing
```

## 🔄 操作语义

### 求值规则

```haskell
-- 求值函数
eval :: Term -> Maybe Term

-- 单位值
eval Unit = Just Unit

-- 布尔值
eval True = Just True
eval False = Just False

-- 整数字面量
eval (LitInt n) = Just (LitInt n)

-- 浮点字面量
eval (LitFloat f) = Just (LitFloat f)

-- 变量（在闭包中求值）
eval (Var _) = Nothing

-- λ抽象
eval (Lam x t body) = Just (Lam x t body)

-- 应用（β归约）
eval (App t1 t2) = do
  t1' <- eval t1
  case t1' of
    Lam x _ body -> eval (subst body x t2)
    _ -> Nothing

-- 序对
eval (Pair t1 t2) = do
  t1' <- eval t1
  t2' <- eval t2
  return (Pair t1' t2')

-- 第一投影
eval (Fst t) = do
  t' <- eval t
  case t' of
    Pair t1 _ -> Just t1
    _ -> Nothing

-- 第二投影
eval (Snd t) = do
  t' <- eval t
  case t' of
    Pair _ t2 -> Just t2
    _ -> Nothing

-- 左注入
eval (Inl t t2) = do
  t' <- eval t
  return (Inl t' t2)

-- 右注入
eval (Inr t1 t) = do
  t' <- eval t
  return (Inr t1 t')

-- Case分析
eval (Case t x1 t1 x2 t2) = do
  t' <- eval t
  case t' of
    Inl v _ -> eval (subst t1 x1 v)
    Inr _ v -> eval (subst t2 x2 v)
    _ -> Nothing

-- 条件语句
eval (If t1 t2 t3) = do
  t1' <- eval t1
  case t1' of
    True -> eval t2
    False -> eval t3
    _ -> Nothing

-- 替换函数
subst :: Term -> String -> Term -> Term
subst (Var x) y v 
  | x == y = v
  | otherwise = Var x
subst (Lam x t body) y v
  | x == y = Lam x t body
  | otherwise = Lam x t (subst body y v)
subst (App t1 t2) y v = App (subst t1 y v) (subst t2 y v)
subst (Pair t1 t2) y v = Pair (subst t1 y v) (subst t2 y v)
subst (Fst t) y v = Fst (subst t y v)
subst (Snd t) y v = Snd (subst t y v)
subst (Inl t t2) y v = Inl (subst t y v) t2
subst (Inr t1 t) y v = Inr t1 (subst t y v)
subst (Case t x1 t1 x2 t2) y v = 
  Case (subst t y v) x1 (subst t1 y v) x2 (subst t2 y v)
subst (If t1 t2 t3) y v = If (subst t1 y v) (subst t2 y v) (subst t3 y v)
subst t _ _ = t
```

## 📊 类型安全定理

### 进展定理 (Progress)

**定理**：如果 $\emptyset \vdash t : \tau$，那么要么 $t$ 是一个值，要么存在 $t'$ 使得 $t \rightarrow t'$。

**证明**：通过对项 $t$ 的结构归纳。

```haskell
-- 进展定理的Haskell实现
progress :: Term -> Type -> Bool
progress t tau = 
  isValue t || hasReduction t
  where
    isValue Unit = True
    isValue True = True
    isValue False = True
    isValue (LitInt _) = True
    isValue (LitFloat _) = True
    isValue (Lam _ _ _) = True
    isValue (Pair t1 t2) = isValue t1 && isValue t2
    isValue (Inl t _) = isValue t
    isValue (Inr _ t) = isValue t
    isValue _ = False
    
    hasReduction t = case eval t of
      Just _ -> True
      Nothing -> False
```

### 保持定理 (Preservation)

**定理**：如果 $\Gamma \vdash t : \tau$ 且 $t \rightarrow t'$，那么 $\Gamma \vdash t' : \tau$。

**证明**：通过对归约规则的结构归纳。

```haskell
-- 保持定理的Haskell实现
preservation :: TypeEnv -> Term -> Term -> Type -> Bool
preservation env t t' tau = 
  case (typeCheck env t, typeCheck env t') of
    (Just tau1, Just tau2) -> tau1 == tau2
    _ -> False
```

## 🎯 类型推导算法

### 合一算法

```haskell
-- 类型变量
data TypeVar = TVar String deriving (Eq, Show)

-- 扩展类型语法包含类型变量
data Type' = 
    TUnit'
  | TBool'
  | TInt'
  | TFloat'
  | TArrow' Type' Type'
  | TProduct' Type' Type'
  | TSum' Type' Type'
  | TVar' TypeVar
  deriving (Eq, Show)

-- 替换
type Substitution = [(TypeVar, Type')]

-- 应用替换
applySubst :: Substitution -> Type' -> Type'
applySubst s (TVar' v) = 
  case lookup v s of
    Just t -> t
    Nothing -> TVar' v
applySubst s (TArrow' t1 t2) = TArrow' (applySubst s t1) (applySubst s t2)
applySubst s (TProduct' t1 t2) = TProduct' (applySubst s t1) (applySubst s t2)
applySubst s (TSum' t1 t2) = TSum' (applySubst s t1) (applySubst s t2)
applySubst _ t = t

-- 合一算法
unify :: Type' -> Type' -> Maybe Substitution
unify (TVar' v) t = Just [(v, t)]
unify t (TVar' v) = Just [(v, t)]
unify TUnit' TUnit' = Just []
unify TBool' TBool' = Just []
unify TInt' TInt' = Just []
unify TFloat' TFloat' = Just []
unify (TArrow' t1 t2) (TArrow' t1' t2') = do
  s1 <- unify t1 t1'
  s2 <- unify (applySubst s1 t2) (applySubst s1 t2')
  return (s2 ++ s1)
unify (TProduct' t1 t2) (TProduct' t1' t2') = do
  s1 <- unify t1 t1'
  s2 <- unify (applySubst s1 t2) (applySubst s1 t2')
  return (s2 ++ s1)
unify (TSum' t1 t2) (TSum' t1' t2') = do
  s1 <- unify t1 t1'
  s2 <- unify (applySubst s1 t2) (applySubst s1 t2')
  return (s2 ++ s1)
unify _ _ = Nothing
```

## 🔧 实际应用

### 类型检查器实现

```haskell
-- 完整的类型检查器
class TypeChecker a where
  inferType :: TypeEnv -> a -> Maybe Type
  checkType :: TypeEnv -> a -> Type -> Bool

instance TypeChecker Term where
  inferType = typeCheck
  checkType env t tau = 
    case typeCheck env t of
      Just tau' -> tau == tau'
      Nothing -> False

-- 类型错误处理
data TypeError = 
    UnboundVariable String
  | TypeMismatch Type Type
  | ExpectedArrow Type
  | ExpectedProduct Type
  | ExpectedSum Type
  | ExpectedBool Type
  deriving (Show)

-- 带错误信息的类型检查
typeCheckWithError :: TypeEnv -> Term -> Either TypeError Type
typeCheckWithError env t = 
  case typeCheck env t of
    Just tau -> Right tau
    Nothing -> Left (TypeMismatch TUnit TUnit) -- 简化的错误处理
```

### 示例程序

```haskell
-- 示例：恒等函数
idFunction :: Term
idFunction = Lam "x" (TVar "a") (Var "x")

-- 示例：应用恒等函数
idApp :: Term
idApp = App idFunction (LitInt 42)

-- 示例：序对操作
pairExample :: Term
pairExample = Pair (LitInt 1) (LitInt 2)

-- 示例：条件语句
ifExample :: Term
ifExample = If True (LitInt 1) (LitInt 2)

-- 测试类型检查
testTypeChecking :: IO ()
testTypeChecking = do
  putStrLn "Testing type checking..."
  
  -- 测试恒等函数
  case typeCheck emptyEnv idFunction of
    Just tau -> putStrLn $ "idFunction: " ++ show tau
    Nothing -> putStrLn "idFunction: type error"
  
  -- 测试应用
  case typeCheck emptyEnv idApp of
    Just tau -> putStrLn $ "idApp: " ++ show tau
    Nothing -> putStrLn "idApp: type error"
  
  -- 测试序对
  case typeCheck emptyEnv pairExample of
    Just tau -> putStrLn $ "pairExample: " ++ show tau
    Nothing -> putStrLn "pairExample: type error"
  
  -- 测试条件语句
  case typeCheck emptyEnv ifExample of
    Just tau -> putStrLn $ "ifExample: " ++ show tau
    Nothing -> putStrLn "ifExample: type error"
```

## 📈 扩展与变体

### 递归类型

```haskell
-- 递归类型定义
data RecType = 
    TRec String Type          -- μX.τ
  | TVarRec String            -- X
  deriving (Eq, Show)

-- 递归类型展开
unfoldRecType :: RecType -> RecType
unfoldRecType (TRec x tau) = substRecType tau x (TRec x tau)
unfoldRecType t = t

-- 递归类型替换
substRecType :: Type -> String -> RecType -> Type
-- 实现递归类型替换逻辑
```

### 子类型系统

```haskell
-- 子类型关系
isSubtype :: Type -> Type -> Bool
isSubtype t1 t2 = t1 == t2  -- 基本实现

-- 子类型检查
subtypeCheck :: TypeEnv -> Term -> Type -> Bool
subtypeCheck env t tau = 
  case typeCheck env t of
    Just tau' -> isSubtype tau' tau
    Nothing -> False
```

## 🎯 总结

简单类型系统为编程语言提供了基础的类型安全保障：

1. **类型安全**：通过类型检查防止运行时错误
2. **抽象能力**：支持函数抽象和数据结构抽象
3. **可扩展性**：为更复杂的类型系统提供基础
4. **形式化基础**：建立严格的数学理论基础

简单类型系统是理解更高级类型系统（如多态类型、依赖类型）的重要基础，为现代编程语言的设计和实现提供了理论指导。

---

**相关链接**：
- [类型系统理论总览](../README.md)
- [多态类型系统](03-Polymorphic-Type-Systems.md)
- [依赖类型系统](04-Dependent-Type-Systems.md)
- [语义理论](../02-Semantics-Theory/语义理论.md) 