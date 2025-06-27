# 简单类型理论基础

## 📋 概述

简单类型理论是类型系统的基础，为编程语言提供了形式化的类型检查机制。本文档介绍简单类型λ演算（Simply Typed Lambda Calculus, STLC）的完整理论体系，包含类型系统、类型检查算法和语义解释。

## 🎯 基础概念

### 定义 1.1 (类型)

简单类型由以下语法定义：
$$\tau ::= \text{Bool} \mid \text{Nat} \mid \tau_1 \rightarrow \tau_2$$

其中：

- $\text{Bool}$ 是布尔类型
- $\text{Nat}$ 是自然数类型
- $\tau_1 \rightarrow \tau_2$ 是函数类型

```haskell
-- 简单类型定义
data Type = 
    TBool
    | TNat
    | TArrow Type Type
    deriving (Show, Eq)

-- 类型示例
boolType :: Type
boolType = TBool

natType :: Type
natType = TNat

functionType :: Type
functionType = TArrow TBool TNat  -- Bool -> Nat
```

### 定义 1.2 (类型上下文)

类型上下文 $\Gamma$ 是变量到类型的映射：
$$\Gamma : \text{Var} \rightarrow \text{Type}$$

```haskell
-- 类型上下文
type Context = [(String, Type)]

-- 空上下文
emptyContext :: Context
emptyContext = []

-- 添加上下文
addBinding :: Context -> String -> Type -> Context
addBinding ctx x t = (x, t) : ctx

-- 查找类型
lookupType :: Context -> String -> Maybe Type
lookupType [] _ = Nothing
lookupType ((x', t) : ctx) x
    | x' == x = Just t
    | otherwise = lookupType ctx x
```

### 定义 1.3 (表达式)

简单类型λ演算的表达式：
$$e ::= x \mid \lambda x : \tau.e \mid e_1 e_2 \mid \text{true} \mid \text{false} \mid 0 \mid \text{succ } e \mid \text{pred } e \mid \text{iszero } e$$

```haskell
-- 表达式定义
data Expr = 
    Var String
    | Lambda String Type Expr
    | App Expr Expr
    | Bool Bool
    | Zero
    | Succ Expr
    | Pred Expr
    | IsZero Expr
    deriving (Show, Eq)

-- 表达式示例
identity :: Expr
identity = Lambda "x" TBool (Var "x")

apply :: Expr
apply = App (Lambda "f" (TArrow TBool TNat) (Var "f")) (Bool True)
```

## 🔧 类型系统

### 定义 1.4 (类型判断)

类型判断形如 $\Gamma \vdash e : \tau$，表示在上下文 $\Gamma$ 中，表达式 $e$ 具有类型 $\tau$。

### 公理 1.1 (变量规则)

$$\frac{x : \tau \in \Gamma}{\Gamma \vdash x : \tau}$$

### 公理 1.2 (函数抽象)

$$\frac{\Gamma, x : \tau_1 \vdash e : \tau_2}{\Gamma \vdash \lambda x : \tau_1.e : \tau_1 \rightarrow \tau_2}$$

### 公理 1.3 (函数应用)

$$\frac{\Gamma \vdash e_1 : \tau_1 \rightarrow \tau_2 \quad \Gamma \vdash e_2 : \tau_1}{\Gamma \vdash e_1 e_2 : \tau_2}$$

### 公理 1.4 (布尔值)

$$\frac{}{\Gamma \vdash \text{true} : \text{Bool}} \quad \frac{}{\Gamma \vdash \text{false} : \text{Bool}}$$

### 公理 1.5 (自然数)

$$\frac{}{\Gamma \vdash 0 : \text{Nat}} \quad \frac{\Gamma \vdash e : \text{Nat}}{\Gamma \vdash \text{succ } e : \text{Nat}} \quad \frac{\Gamma \vdash e : \text{Nat}}{\Gamma \vdash \text{pred } e : \text{Nat}}$$

### 公理 1.6 (零值判断)

$$\frac{\Gamma \vdash e : \text{Nat}}{\Gamma \vdash \text{iszero } e : \text{Bool}}$$

```haskell
-- 类型检查器
typeCheck :: Context -> Expr -> Either String Type
typeCheck ctx (Var x) = case lookupType ctx x of
    Just t -> Right t
    Nothing -> Left ("Unbound variable: " ++ x)

typeCheck ctx (Lambda x t1 e) = do
    t2 <- typeCheck (addBinding ctx x t1) e
    return (TArrow t1 t2)

typeCheck ctx (App e1 e2) = do
    t1 <- typeCheck ctx e1
    t2 <- typeCheck ctx e2
    case t1 of
        TArrow t1' t2' | t1' == t2 -> Right t2'
        _ -> Left "Type mismatch in function application"

typeCheck ctx (Bool _) = Right TBool
typeCheck ctx Zero = Right TNat
typeCheck ctx (Succ e) = do
    t <- typeCheck ctx e
    case t of
        TNat -> Right TNat
        _ -> Left "Succ expects Nat"

typeCheck ctx (Pred e) = do
    t <- typeCheck ctx e
    case t of
        TNat -> Right TNat
        _ -> Left "Pred expects Nat"

typeCheck ctx (IsZero e) = do
    t <- typeCheck ctx e
    case t of
        TNat -> Right TBool
        _ -> Left "IsZero expects Nat"
```

## 📊 类型安全性

### 定理 1.1 (类型保持性 - Type Preservation)

如果 $\Gamma \vdash e : \tau$ 且 $e \rightarrow e'$，则 $\Gamma \vdash e' : \tau$。

**证明：** 通过结构归纳法证明。对于每个归约规则，需要证明类型在归约后保持不变。

### 定理 1.2 (进展性 - Progress)

如果 $\emptyset \vdash e : \tau$，则要么 $e$ 是值，要么存在 $e'$ 使得 $e \rightarrow e'$。

**证明：** 通过结构归纳法证明。对于每个语法构造，证明要么是值，要么可以继续归约。

```haskell
-- 值定义
isValue :: Expr -> Bool
isValue (Bool _) = True
isValue Zero = True
isValue (Succ e) = isValue e
isValue (Lambda _ _ _) = True
isValue _ = False

-- 归约关系
data Step = Step Expr Expr deriving Show

-- 归约规则
step :: Expr -> Maybe Expr
step (App (Lambda x _ e1) e2) = Just (substitute x e2 e1)
step (App e1 e2) = case step e1 of
    Just e1' -> Just (App e1' e2)
    Nothing -> case step e2 of
        Just e2' -> Just (App e1 e2')
        Nothing -> Nothing
step (Succ e) = case step e of
    Just e' -> Just (Succ e')
    Nothing -> Nothing
step (Pred Zero) = Just Zero
step (Pred (Succ e)) = Just e
step (Pred e) = case step e of
    Just e' -> Just (Pred e')
    Nothing -> Nothing
step (IsZero Zero) = Just (Bool True)
step (IsZero (Succ _)) = Just (Bool False)
step (IsZero e) = case step e of
    Just e' -> Just (IsZero e')
    Nothing -> Nothing
step _ = Nothing

-- 替换函数
substitute :: String -> Expr -> Expr -> Expr
substitute x e (Var y)
    | x == y = e
    | otherwise = Var y
substitute x e (Lambda y t e1)
    | x == y = Lambda y t e1
    | otherwise = Lambda y t (substitute x e e1)
substitute x e (App e1 e2) = App (substitute x e e1) (substitute x e e2)
substitute x e (Succ e1) = Succ (substitute x e e1)
substitute x e (Pred e1) = Pred (substitute x e e1)
substitute x e (IsZero e1) = IsZero (substitute x e e1)
substitute _ _ e = e
```

## 🔍 类型推断

### 定义 1.5 (类型变量)

为了支持类型推断，我们引入类型变量：
$$\tau ::= \alpha \mid \text{Bool} \mid \text{Nat} \mid \tau_1 \rightarrow \tau_2$$

其中 $\alpha$ 是类型变量。

```haskell
-- 带类型变量的类型
data TypeVar = TypeVar String deriving (Show, Eq, Ord)

data PolyType = 
    TVar TypeVar
    | TBool
    | TNat
    | TArrow PolyType PolyType
    deriving (Show, Eq)

-- 类型替换
type Substitution = [(TypeVar, PolyType)]

applySubst :: Substitution -> PolyType -> PolyType
applySubst s (TVar a) = case lookup a s of
    Just t -> t
    Nothing -> TVar a
applySubst s (TArrow t1 t2) = TArrow (applySubst s t1) (applySubst s t2)
applySubst _ t = t

-- 自由类型变量
freeTypeVars :: PolyType -> Set TypeVar
freeTypeVars (TVar a) = Set.singleton a
freeTypeVars (TArrow t1 t2) = Set.union (freeTypeVars t1) (freeTypeVars t2)
freeTypeVars _ = Set.empty
```

### 算法 W (Robinson's Unification)

```haskell
-- 合一算法
unify :: PolyType -> PolyType -> Either String Substitution
unify (TVar a) t = 
    if a `Set.member` freeTypeVars t 
    then Left "Occurs check failed"
    else Right [(a, t)]
unify t (TVar a) = unify (TVar a) t
unify (TArrow t1 t2) (TArrow t1' t2') = do
    s1 <- unify t1 t1'
    s2 <- unify (applySubst s1 t2) (applySubst s1 t2')
    return (compose s2 s1)
unify TBool TBool = Right []
unify TNat TNat = Right []
unify t1 t2 = Left ("Cannot unify " ++ show t1 ++ " with " ++ show t2)

-- 替换组合
compose :: Substitution -> Substitution -> Substitution
compose s2 s1 = [(a, applySubst s2 t) | (a, t) <- s1] ++ s2
```

### 定理 1.3 (算法W的正确性)

如果算法W成功，则返回的替换是最一般的一致替换。

**证明：** 通过归纳法证明算法的正确性和最一般性。

## 📈 语义解释

### 定义 1.6 (指称语义)

类型 $\tau$ 的语义域：
$$\llbracket \text{Bool} \rrbracket = \{\text{true}, \text{false}\}$$
$$\llbracket \text{Nat} \rrbracket = \mathbb{N}$$
$$\llbracket \tau_1 \rightarrow \tau_2 \rrbracket = \llbracket \tau_1 \rrbracket \rightarrow \llbracket \tau_2 \rrbracket$$

```haskell
-- 语义域
data Value = 
    VBool Bool
    | VNat Int
    | VClosure String Expr Context
    deriving Show

-- 语义解释
eval :: Context -> Expr -> Either String Value
eval ctx (Bool b) = Right (VBool b)
eval ctx Zero = Right (VNat 0)
eval ctx (Succ e) = do
    v <- eval ctx e
    case v of
        VNat n -> Right (VNat (n + 1))
        _ -> Left "Type error in evaluation"
eval ctx (Pred e) = do
    v <- eval ctx e
    case v of
        VNat n -> Right (VNat (max 0 (n - 1)))
        _ -> Left "Type error in evaluation"
eval ctx (IsZero e) = do
    v <- eval ctx e
    case v of
        VNat n -> Right (VBool (n == 0))
        _ -> Left "Type error in evaluation"
eval ctx (Var x) = case lookupType ctx x of
    Just _ -> Left "Cannot evaluate variable"
    Nothing -> Left "Unbound variable"
eval ctx (Lambda x t e) = Right (VClosure x e ctx)
eval ctx (App e1 e2) = do
    v1 <- eval ctx e1
    v2 <- eval ctx e2
    case v1 of
        VClosure x e ctx' -> eval (addBinding ctx' x (getType v2)) e
        _ -> Left "Type error in application"
  where
    getType (VBool _) = TBool
    getType (VNat _) = TNat
    getType (VClosure _ _ _) = error "Cannot get type of closure"
```

## 🔗 相关链接

### 理论基础

- [形式语言理论](../07-Formal-Language-Theory/001-Formal-Language-Foundation.md)
- [自动机理论](../06-Automata-Theory/001-Automata-Foundation.md)
- [范畴论](../03-Category-Theory/001-Basic-Concepts.md)

### 高级类型理论

- [依赖类型理论](./002-Dependent-Type-Theory.md)
- [同伦类型理论](./003-Homotopy-Type-Theory.md)
- [构造类型理论](./004-Constructive-Type-Theory.md)

### 实际应用

- [类型系统实现](../haskell/04-Type-System/001-Type-Definitions.md)
- [类型检查器](../haskell/13-Formal-Verification/001-Theorem-Proving.md)
- [编译器设计](../07-Implementation/01-Compiler-Design/001-Lexical-Analysis.md)

---

**最后更新**: 2024年12月
**版本**: 1.0
**状态**: ✅ 完成
**维护者**: 形式化知识体系团队
