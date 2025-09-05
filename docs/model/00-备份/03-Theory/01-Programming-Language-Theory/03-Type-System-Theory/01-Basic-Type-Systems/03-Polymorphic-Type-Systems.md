# 多态类型系统 (Polymorphic Type Systems)

## 📚 概述

多态类型系统扩展了简单类型系统，引入了类型参数和类型抽象，使程序能够以统一的方式处理不同类型的值。我们研究System F（二阶λ演算）、参数多态、类型抽象等核心概念。

## 🏗️ 形式化定义

### System F (二阶λ演算)

#### 语法定义

```haskell
-- 扩展类型语法
data PolyType = 
    TUnit                    -- 单位类型
  | TBool                    -- 布尔类型
  | TInt                     -- 整数类型
  | TFloat                   -- 浮点类型
  | TArrow PolyType PolyType -- 函数类型 τ₁ → τ₂
  | TProduct PolyType PolyType -- 积类型 τ₁ × τ₂
  | TSum PolyType PolyType   -- 和类型 τ₁ + τ₂
  | TVar String              -- 类型变量 α
  | TForall String PolyType  -- 全称类型 ∀α.τ
  deriving (Eq, Show)

-- 扩展项语法
data PolyTerm = 
    Unit                     -- 单位值
  | True | False             -- 布尔值
  | LitInt Int               -- 整数字面量
  | LitFloat Double          -- 浮点字面量
  | Var String               -- 变量
  | Lam String PolyType PolyTerm -- λ抽象 λx:τ.t
  | App PolyTerm PolyTerm    -- 应用 t₁ t₂
  | TLam String PolyTerm     -- 类型抽象 Λα.t
  | TApp PolyTerm PolyType   -- 类型应用 t[τ]
  | Pair PolyTerm PolyTerm   -- 序对 (t₁, t₂)
  | Fst PolyTerm             -- 第一投影 fst t
  | Snd PolyTerm             -- 第二投影 snd t
  | Inl PolyTerm PolyType    -- 左注入 inl t : τ₁ + τ₂
  | Inr PolyType PolyTerm    -- 右注入 inr τ₁ t : τ₁ + τ₂
  | Case PolyTerm String PolyTerm String PolyTerm -- case分析
  | If PolyTerm PolyTerm PolyTerm -- 条件语句
  deriving (Eq, Show)
```

#### 类型环境

```haskell
-- 类型环境：变量到类型的映射
type PolyTypeEnv = [(String, PolyType)]

-- 类型变量环境
type TypeVarEnv = [String]

-- 空环境
emptyPolyEnv :: PolyTypeEnv
emptyPolyEnv = []

emptyTypeVarEnv :: TypeVarEnv
emptyTypeVarEnv = []

-- 扩展环境
extendPolyEnv :: PolyTypeEnv -> String -> PolyType -> PolyTypeEnv
extendPolyEnv env x t = (x, t) : env

extendTypeVarEnv :: TypeVarEnv -> String -> TypeVarEnv
extendTypeVarEnv env a = a : env

-- 查找变量类型
lookupPolyType :: PolyTypeEnv -> String -> Maybe PolyType
lookupPolyType [] _ = Nothing
lookupPolyType ((x', t) : env) x 
  | x == x' = Just t
  | otherwise = lookupPolyType env x

-- 检查类型变量是否绑定
isTypeVarBound :: TypeVarEnv -> String -> Bool
isTypeVarBound env a = a `elem` env
```

#### 类型检查规则

```haskell
-- 多态类型检查函数
polyTypeCheck :: PolyTypeEnv -> TypeVarEnv -> PolyTerm -> Maybe PolyType

-- 单位类型规则
polyTypeCheck _ _ Unit = Just TUnit

-- 布尔类型规则
polyTypeCheck _ _ True = Just TBool
polyTypeCheck _ _ False = Just TBool

-- 整数类型规则
polyTypeCheck _ _ (LitInt _) = Just TInt

-- 浮点类型规则
polyTypeCheck _ _ (LitFloat _) = Just TFloat

-- 变量规则
polyTypeCheck env _ (Var x) = lookupPolyType env x

-- λ抽象规则
polyTypeCheck env tvEnv (Lam x t1 t2) = do
  t2' <- polyTypeCheck (extendPolyEnv env x t1) tvEnv t2
  return (TArrow t1 t2')

-- 应用规则
polyTypeCheck env tvEnv (App t1 t2) = do
  t1' <- polyTypeCheck env tvEnv t1
  t2' <- polyTypeCheck env tvEnv t2
  case t1' of
    TArrow t11 t12 | t11 == t2' -> Just t12
    _ -> Nothing

-- 类型抽象规则
polyTypeCheck env tvEnv (TLam a t) = do
  t' <- polyTypeCheck env (extendTypeVarEnv tvEnv a) t
  return (TForall a t')

-- 类型应用规则
polyTypeCheck env tvEnv (TApp t1 t2) = do
  t1' <- polyTypeCheck env tvEnv t1
  case t1' of
    TForall a t -> Just (substType t a t2)
    _ -> Nothing

-- 序对规则
polyTypeCheck env tvEnv (Pair t1 t2) = do
  t1' <- polyTypeCheck env tvEnv t1
  t2' <- polyTypeCheck env tvEnv t2
  return (TProduct t1' t2')

-- 第一投影规则
polyTypeCheck env tvEnv (Fst t) = do
  t' <- polyTypeCheck env tvEnv t
  case t' of
    TProduct t1 _ -> Just t1
    _ -> Nothing

-- 第二投影规则
polyTypeCheck env tvEnv (Snd t) = do
  t' <- polyTypeCheck env tvEnv t
  case t' of
    TProduct _ t2 -> Just t2
    _ -> Nothing

-- 左注入规则
polyTypeCheck env tvEnv (Inl t t2) = do
  t1 <- polyTypeCheck env tvEnv t
  return (TSum t1 t2)

-- 右注入规则
polyTypeCheck env tvEnv (Inr t1 t) = do
  t2 <- polyTypeCheck env tvEnv t
  return (TSum t1 t2)

-- Case分析规则
polyTypeCheck env tvEnv (Case t x1 t1 x2 t2) = do
  t' <- polyTypeCheck env tvEnv t
  case t' of
    TSum t1' t2' -> do
      t1'' <- polyTypeCheck (extendPolyEnv env x1 t1') tvEnv t1
      t2'' <- polyTypeCheck (extendPolyEnv env x2 t2') tvEnv t2
      if t1'' == t2'' then Just t1'' else Nothing
    _ -> Nothing

-- 条件语句规则
polyTypeCheck env tvEnv (If t1 t2 t3) = do
  t1' <- polyTypeCheck env tvEnv t1
  t2' <- polyTypeCheck env tvEnv t2
  t3' <- polyTypeCheck env tvEnv t3
  case t1' of
    TBool | t2' == t3' -> Just t2'
    _ -> Nothing
```

#### 类型替换

```haskell
-- 类型替换函数
substType :: PolyType -> String -> PolyType -> PolyType
substType (TVar a) b t 
  | a == b = t
  | otherwise = TVar a
substType (TArrow t1 t2) a t = 
  TArrow (substType t1 a t) (substType t2 a t)
substType (TProduct t1 t2) a t = 
  TProduct (substType t1 a t) (substType t2 a t)
substType (TSum t1 t2) a t = 
  TSum (substType t1 a t) (substType t2 a t)
substType (TForall b t1) a t
  | a == b = TForall b t1
  | otherwise = TForall b (substType t1 a t)
substType t _ _ = t
```

## 🔄 操作语义

### 求值规则

```haskell
-- 多态求值函数
polyEval :: PolyTerm -> Maybe PolyTerm

-- 单位值
polyEval Unit = Just Unit

-- 布尔值
polyEval True = Just True
polyEval False = Just False

-- 整数字面量
polyEval (LitInt n) = Just (LitInt n)

-- 浮点字面量
polyEval (LitFloat f) = Just (LitFloat f)

-- 变量（在闭包中求值）
polyEval (Var _) = Nothing

-- λ抽象
polyEval (Lam x t body) = Just (Lam x t body)

-- 应用（β归约）
polyEval (App t1 t2) = do
  t1' <- polyEval t1
  case t1' of
    Lam x _ body -> polyEval (polySubst body x t2)
    _ -> Nothing

-- 类型抽象
polyEval (TLam a t) = Just (TLam a t)

-- 类型应用（类型β归约）
polyEval (TApp t1 t2) = do
  t1' <- polyEval t1
  case t1' of
    TLam a body -> polyEval (polyTypeSubst body a t2)
    _ -> Nothing

-- 序对
polyEval (Pair t1 t2) = do
  t1' <- polyEval t1
  t2' <- polyEval t2
  return (Pair t1' t2')

-- 第一投影
polyEval (Fst t) = do
  t' <- polyEval t
  case t' of
    Pair t1 _ -> Just t1
    _ -> Nothing

-- 第二投影
polyEval (Snd t) = do
  t' <- polyEval t
  case t' of
    Pair _ t2 -> Just t2
    _ -> Nothing

-- 左注入
polyEval (Inl t t2) = do
  t' <- polyEval t
  return (Inl t' t2)

-- 右注入
polyEval (Inr t1 t) = do
  t' <- polyEval t
  return (Inr t1 t')

-- Case分析
polyEval (Case t x1 t1 x2 t2) = do
  t' <- polyEval t
  case t' of
    Inl v _ -> polyEval (polySubst t1 x1 v)
    Inr _ v -> polyEval (polySubst t2 x2 v)
    _ -> Nothing

-- 条件语句
polyEval (If t1 t2 t3) = do
  t1' <- polyEval t1
  case t1' of
    True -> polyEval t2
    False -> polyEval t3
    _ -> Nothing

-- 多态替换函数
polySubst :: PolyTerm -> String -> PolyTerm -> PolyTerm
polySubst (Var x) y v 
  | x == y = v
  | otherwise = Var x
polySubst (Lam x t body) y v
  | x == y = Lam x t body
  | otherwise = Lam x t (polySubst body y v)
polySubst (App t1 t2) y v = App (polySubst t1 y v) (polySubst t2 y v)
polySubst (TLam a t) y v = TLam a (polySubst t y v)
polySubst (TApp t1 t2) y v = TApp (polySubst t1 y v) t2
polySubst (Pair t1 t2) y v = Pair (polySubst t1 y v) (polySubst t2 y v)
polySubst (Fst t) y v = Fst (polySubst t y v)
polySubst (Snd t) y v = Snd (polySubst t y v)
polySubst (Inl t t2) y v = Inl (polySubst t y v) t2
polySubst (Inr t1 t) y v = Inr t1 (polySubst t y v)
polySubst (Case t x1 t1 x2 t2) y v = 
  Case (polySubst t y v) x1 (polySubst t1 y v) x2 (polySubst t2 y v)
polySubst (If t1 t2 t3) y v = If (polySubst t1 y v) (polySubst t2 y v) (polySubst t3 y v)
polySubst t _ _ = t

-- 类型替换函数
polyTypeSubst :: PolyTerm -> String -> PolyType -> PolyTerm
polyTypeSubst (Var x) a t = Var x
polyTypeSubst (Lam x t1 body) a t = Lam x (substType t1 a t) (polyTypeSubst body a t)
polyTypeSubst (App t1 t2) a t = App (polyTypeSubst t1 a t) (polyTypeSubst t2 a t)
polyTypeSubst (TLam b body) a t
  | a == b = TLam b body
  | otherwise = TLam b (polyTypeSubst body a t)
polyTypeSubst (TApp t1 t2) a t = TApp (polyTypeSubst t1 a t) (substType t2 a t)
polyTypeSubst (Pair t1 t2) a t = Pair (polyTypeSubst t1 a t) (polyTypeSubst t2 a t)
polyTypeSubst (Fst t1) a t = Fst (polyTypeSubst t1 a t)
polyTypeSubst (Snd t1) a t = Snd (polyTypeSubst t1 a t)
polyTypeSubst (Inl t1 t2) a t = Inl (polyTypeSubst t1 a t) (substType t2 a t)
polyTypeSubst (Inr t1 t2) a t = Inr (substType t1 a t) (polyTypeSubst t2 a t)
polyTypeSubst (Case t x1 t1 x2 t2) a t' = 
  Case (polyTypeSubst t a t') x1 (polyTypeSubst t1 a t') x2 (polyTypeSubst t2 a t')
polyTypeSubst (If t1 t2 t3) a t = If (polyTypeSubst t1 a t) (polyTypeSubst t2 a t) (polyTypeSubst t3 a t)
polyTypeSubst term _ _ = term
```

## 📊 类型安全定理

### 进展定理 (Progress)

**定理**：如果 $\emptyset \vdash t : \tau$，那么要么 $t$ 是一个值，要么存在 $t'$ 使得 $t \rightarrow t'$。

**证明**：通过对项 $t$ 的结构归纳，包括类型抽象和类型应用的情况。

```haskell
-- 进展定理的Haskell实现
polyProgress :: PolyTerm -> PolyType -> Bool
polyProgress t tau = 
  isPolyValue t || hasPolyReduction t
  where
    isPolyValue Unit = True
    isPolyValue True = True
    isPolyValue False = True
    isPolyValue (LitInt _) = True
    isPolyValue (LitFloat _) = True
    isPolyValue (Lam _ _ _) = True
    isPolyValue (TLam _ _) = True
    isPolyValue (Pair t1 t2) = isPolyValue t1 && isPolyValue t2
    isPolyValue (Inl t _) = isPolyValue t
    isPolyValue (Inr _ t) = isPolyValue t
    isPolyValue _ = False
    
    hasPolyReduction t = case polyEval t of
      Just _ -> True
      Nothing -> False
```

### 保持定理 (Preservation)

**定理**：如果 $\Gamma \vdash t : \tau$ 且 $t \rightarrow t'$，那么 $\Gamma \vdash t' : \tau$。

**证明**：通过对归约规则的结构归纳，包括类型β归约。

```haskell
-- 保持定理的Haskell实现
polyPreservation :: PolyTypeEnv -> TypeVarEnv -> PolyTerm -> PolyTerm -> PolyType -> Bool
polyPreservation env tvEnv t t' tau = 
  case (polyTypeCheck env tvEnv t, polyTypeCheck env tvEnv t') of
    (Just tau1, Just tau2) -> tau1 == tau2
    _ -> False
```

## 🎯 参数多态

### 参数多态定义

参数多态允许函数和数据结构以统一的方式处理不同类型的值，而不需要为每种类型编写专门的代码。

```haskell
-- 参数多态示例：恒等函数
idPoly :: PolyTerm
idPoly = TLam "a" (Lam "x" (TVar "a") (Var "x"))

-- 参数多态示例：列表类型
data ListType = 
    TNil PolyType              -- 空列表
  | TCons PolyType ListType    -- 非空列表
  deriving (Eq, Show)

-- 参数多态示例：map函数
mapPoly :: PolyTerm
mapPoly = TLam "a" $ TLam "b" $ 
  Lam "f" (TArrow (TVar "a") (TVar "b")) $
  Lam "xs" (TVar "a") $ 
  -- 简化的map实现
  Var "xs"
```

### 类型推导算法

```haskell
-- Hindley-Milner类型推导
data TypeScheme = 
    TScheme [String] PolyType  -- ∀α₁...αₙ.τ
  deriving (Eq, Show)

-- 类型环境扩展
type HMTypeEnv = [(String, TypeScheme)]

-- 类型推导函数
inferType :: HMTypeEnv -> PolyTerm -> Maybe (Substitution, PolyType)
inferType env (Var x) = 
  case lookup x env of
    Just (TScheme vars t) -> 
      let freshVars = map (\v -> (v, freshTypeVar v)) vars
          t' = foldr (\(v, tv) t -> substType t v tv) t freshVars
      in Just ([], t')
    Nothing -> Nothing

inferType env (Lam x t1 t2) = do
  (s1, t2') <- inferType (extendHMEnv env x (TScheme [] t1)) t2
  return (s1, TArrow (applySubst s1 t1) t2')

inferType env (App t1 t2) = do
  (s1, t1') <- inferType env t1
  (s2, t2') <- inferType (applySubstEnv s1 env) t2
  tv <- freshTypeVar "result"
  s3 <- unify (applySubst s2 t1') (TArrow t2' tv)
  return (s3 `compose` s2 `compose` s1, applySubst s3 tv)

-- 辅助函数
freshTypeVar :: String -> PolyType
freshTypeVar name = TVar (name ++ "_" ++ show (hash name))

applySubstEnv :: Substitution -> HMTypeEnv -> HMTypeEnv
applySubstEnv s env = map (\(x, scheme) -> (x, applySubstScheme s scheme)) env

applySubstScheme :: Substitution -> TypeScheme -> TypeScheme
applySubstScheme s (TScheme vars t) = TScheme vars (applySubst s t)

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = s1 ++ s2  -- 简化的组合
```

## 🔧 实际应用

### Haskell中的多态

```haskell
-- Haskell中的参数多态示例
class PolymorphicExamples where
  -- 恒等函数
  id' :: a -> a
  id' x = x
  
  -- 常量函数
  const' :: a -> b -> a
  const' x _ = x
  
  -- 函数组合
  compose' :: (b -> c) -> (a -> b) -> a -> c
  compose' f g x = f (g x)
  
  -- 列表操作
  map' :: (a -> b) -> [a] -> [b]
  map' _ [] = []
  map' f (x:xs) = f x : map' f xs
  
  -- 折叠操作
  foldr' :: (a -> b -> b) -> b -> [a] -> b
  foldr' _ z [] = z
  foldr' f z (x:xs) = f x (foldr' f z xs)

-- 类型类多态
class Show a where
  show' :: a -> String

instance Show Int where
  show' = show

instance Show Bool where
  show' True = "True"
  show' False = "False"

-- 高阶多态
class Functor f where
  fmap :: (a -> b) -> f a -> f b

instance Functor Maybe where
  fmap _ Nothing = Nothing
  fmap f (Just x) = Just (f x)

instance Functor [] where
  fmap = map
```

### 类型抽象

```haskell
-- 类型抽象示例：抽象数据类型
class AbstractDataType a where
  empty :: a
  insert :: Int -> a -> a
  member :: Int -> a -> Bool
  size :: a -> Int

-- 列表实现
instance AbstractDataType [Int] where
  empty = []
  insert x xs = x : xs
  member x xs = x `elem` xs
  size xs = length xs

-- 集合实现
instance AbstractDataType (Set Int) where
  empty = Set.empty
  insert x s = Set.insert x s
  member x s = Set.member x s
  size s = Set.size s

-- 使用类型抽象
processData :: AbstractDataType a => [Int] -> a -> a
processData [] acc = acc
processData (x:xs) acc = processData xs (insert x acc)
```

## 📈 高级多态特性

### 存在类型

```haskell
-- 存在类型：∃α.τ
data Exists f = forall a. Exists (f a)

-- 存在类型示例：异构列表
data HeterogeneousList = 
    HNil
  | HCons (Exists Show) HeterogeneousList

-- 使用存在类型
heterogeneousList :: HeterogeneousList
heterogeneousList = HCons (Exists (42 :: Int)) 
                   (HCons (Exists True) 
                   (HCons (Exists "hello") HNil))

-- 处理异构列表
showHeterogeneous :: HeterogeneousList -> [String]
showHeterogeneous HNil = []
showHeterogeneous (HCons (Exists x) xs) = 
  show' x : showHeterogeneous xs
```

### 高阶类型

```haskell
-- 高阶类型：类型构造函数
class HigherOrderType f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b

-- 应用函子实例
instance HigherOrderType Maybe where
  pure = Just
  Nothing <*> _ = Nothing
  Just f <*> x = fmap f x

instance HigherOrderType [] where
  pure x = [x]
  fs <*> xs = concatMap (\f -> map f xs) fs

-- 单子类型类
class Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b

instance Monad Maybe where
  return = Just
  Nothing >>= _ = Nothing
  Just x >>= f = f x
```

## 🎯 总结

多态类型系统为编程语言提供了强大的抽象能力：

1. **代码复用**：通过参数多态实现代码的通用性
2. **类型安全**：在保持类型安全的同时提供灵活性
3. **抽象能力**：支持高级抽象和类型抽象
4. **表达能力**：支持复杂的类型构造和操作

多态类型系统是现代编程语言的核心特性，为函数式编程、泛型编程和类型安全编程提供了理论基础。

---

**相关链接**：

- [类型系统理论总览](../README.md)
- [简单类型系统](02-Simple-Type-Systems.md)
- [依赖类型系统](04-Dependent-Type-Systems.md)
- [语义理论](../02-Semantics-Theory/语义理论.md)
