# 线性逻辑连接词 (Linear Logic Connectives)

## 1. 概述

线性逻辑连接词是线性类型系统的核心组成部分，它们定义了资源的使用方式和组合规则。与经典逻辑不同，线性逻辑强调资源的精确使用，每个资源必须被使用恰好一次。

## 2. 基本连接词

### 2.1 乘法连接词 (Multiplicative Connectives)

#### 2.1.1 张量积 (Tensor Product) ⊗

张量积表示两个资源的并行组合，两个资源都必须被使用。

**形式化定义：**

```haskell
-- 张量积的类型定义
data Tensor a b = Tensor a b

-- 张量积的引入规则
tensorIntro :: a -> b -> Tensor a b
tensorIntro x y = Tensor x y

-- 张量积的消除规则
tensorElim :: Tensor a b -> (a -> b -> c) -> c
tensorElim (Tensor x y) f = f x y

-- 张量积的交换律
tensorComm :: Tensor a b -> Tensor b a
tensorComm (Tensor x y) = Tensor y x

-- 张量积的结合律
tensorAssoc :: Tensor (Tensor a b) c -> Tensor a (Tensor b c)
tensorAssoc (Tensor (Tensor x y) z) = Tensor x (Tensor y z)
```

**线性逻辑规则：**

```latex
Γ ⊢ A    Δ ⊢ B
─────────────── (⊗R)
Γ,Δ ⊢ A ⊗ B

Γ,A,B ⊢ C
─────────── (⊗L)
Γ,A⊗B ⊢ C
```

#### 2.1.2 线性蕴含 (Linear Implication) ⊸

线性蕴含表示资源的转换，使用一个资源来产生另一个资源。

**形式化定义：**

```haskell
-- 线性函数类型
newtype LinearFunction a b = LinearFunction { 
  applyLinear :: a -> b 
}

-- 线性函数的构造
linearFunction :: (a -> b) -> LinearFunction a b
linearFunction f = LinearFunction f

-- 线性函数的应用
applyLinear :: LinearFunction a b -> a -> b
applyLinear (LinearFunction f) x = f x

-- 线性函数的组合
composeLinear :: LinearFunction b c -> LinearFunction a b -> LinearFunction a c
composeLinear (LinearFunction g) (LinearFunction f) = 
  LinearFunction (g . f)

-- Curry化
curryLinear :: LinearFunction (Tensor a b) c -> LinearFunction a (LinearFunction b c)
curryLinear (LinearFunction f) = LinearFunction $ \a ->
  LinearFunction $ \b -> f (Tensor a b)

-- 反Curry化
uncurryLinear :: LinearFunction a (LinearFunction b c) -> LinearFunction (Tensor a b) c
uncurryLinear (LinearFunction f) = LinearFunction $ \(Tensor a b) ->
  applyLinear (f a) b
```

**线性逻辑规则：**

```latex
Γ,A ⊢ B
───────── (⊸R)
Γ ⊢ A ⊸ B

Γ ⊢ A    Δ,B ⊢ C
───────────────── (⊸L)
Γ,Δ,A⊸B ⊢ C
```

### 2.2 加法连接词 (Additive Connectives)

#### 2.2.1 乘积 (Product) &

乘积表示两个资源的共享，可以选择使用其中一个。

**形式化定义：**

```haskell
-- 乘积类型
data Product a b = Product a b

-- 乘积的构造
productIntro :: a -> b -> Product a b
productIntro x y = Product x y

-- 乘积的投影
fstProduct :: Product a b -> a
fstProduct (Product x _) = x

sndProduct :: Product a b -> b
sndProduct (Product _ y) = y

-- 乘积的配对
pairProduct :: (c -> a) -> (c -> b) -> c -> Product a b
pairProduct f g c = Product (f c) (g c)
```

**线性逻辑规则：**

```latex
Γ ⊢ A    Γ ⊢ B
─────────────── (&R)
Γ ⊢ A & B

Γ,A ⊢ C
─────────── (&L₁)
Γ,A&B ⊢ C

Γ,B ⊢ C
─────────── (&L₂)
Γ,A&B ⊢ C
```

#### 2.2.2 和 (Sum) ⊕

和表示两个资源的独占选择，必须选择其中一个。

**形式化定义：**

```haskell
-- 和类型
data Sum a b = InL a | InR b

-- 和的构造
inl :: a -> Sum a b
inl = InL

inr :: b -> Sum a b
inr = InR

-- 和的消除
caseSum :: Sum a b -> (a -> c) -> (b -> c) -> c
caseSum (InL x) f _ = f x
caseSum (InR y) _ g = g y

-- 和的映射
mapSum :: (a -> c) -> (b -> d) -> Sum a b -> Sum c d
mapSum f _ (InL x) = InL (f x)
mapSum _ g (InR y) = InR (g y)
```

**线性逻辑规则：**

```latex
Γ ⊢ A
───────── (⊕R₁)
Γ ⊢ A ⊕ B

Γ ⊢ B
───────── (⊕R₂)
Γ ⊢ A ⊕ B

Γ,A ⊢ C    Γ,B ⊢ C
─────────────────── (⊕L)
Γ,A⊕B ⊢ C
```

## 3. 指数连接词 (Exponential Connectives)

### 3.1 必然性 (Of Course)

 !

必然性表示资源的可重用性，可以将线性资源转换为经典资源。

**形式化定义：**

```haskell
-- 必然性类型
newtype OfCourse a = OfCourse { 
  unOfCourse :: a 
}

-- 必然性的构造
ofCourse :: a -> OfCourse a
ofCourse = OfCourse

-- 必然性的消除
unOfCourse :: OfCourse a -> a
unOfCourse (OfCourse x) = x

-- 必然性的弱化
weaken :: OfCourse a -> OfCourse b -> OfCourse a
weaken (OfCourse x) _ = OfCourse x

-- 必然性的收缩
contract :: OfCourse a -> OfCourse (OfCourse a)
contract (OfCourse x) = OfCourse (OfCourse x)

-- 必然性的交换
exchange :: OfCourse a -> OfCourse b -> OfCourse b -> OfCourse a
exchange (OfCourse x) _ _ = OfCourse x
```

**线性逻辑规则：**

```latex
!Γ ⊢ A
───────── (!R)
!Γ ⊢ !A

Γ,A ⊢ B
─────────── (!L)
Γ,!A ⊢ B

Γ ⊢ B
─────────── (Weak)
Γ,!A ⊢ B

Γ,!A,!A ⊢ B
───────────── (Contr)
Γ,!A ⊢ B
```

### 3.2 可能性 (Why Not) ?

可能性是必然性的对偶，表示资源的潜在可用性。

**形式化定义：**

```haskell
-- 可能性类型
newtype WhyNot a = WhyNot { 
  unWhyNot :: a 
}

-- 可能性的构造
whyNot :: a -> WhyNot a
whyNot = WhyNot

-- 可能性的消除
unWhyNot :: WhyNot a -> a
unWhyNot (WhyNot x) = x

-- 可能性的对偶性
dualOfCourse :: OfCourse a -> WhyNot (LinearFunction a ())
dualOfCourse (OfCourse x) = WhyNot $ LinearFunction $ \_ -> ()

dualWhyNot :: WhyNot a -> OfCourse (LinearFunction () a)
dualWhyNot (WhyNot x) = OfCourse $ LinearFunction $ \_ -> x
```

## 4. 线性逻辑的完整系统

### 4.1 公理和规则

```haskell
-- 线性逻辑的完整类型系统
class LinearLogic a where
  -- 恒等公理
  identity :: a ⊸ a
  
  -- 交换规则
  exchange :: (a ⊗ b) ⊸ (b ⊗ a)
  
  -- 结合规则
  associate :: ((a ⊗ b) ⊗ c) ⊸ (a ⊗ (b ⊗ c))
  
  -- 分配规则
  distribute :: (a ⊗ (b ⊕ c)) ⊸ ((a ⊗ b) ⊕ (a ⊗ c))

-- 线性逻辑的证明系统
data LinearProof a b where
  -- 恒等证明
  Id :: LinearProof a a
  
  -- 张量积证明
  Tensor :: LinearProof a b -> LinearProof c d -> LinearProof (a ⊗ c) (b ⊗ d)
  
  -- 线性蕴含证明
  Impl :: LinearProof (a ⊗ b) c -> LinearProof a (b ⊸ c)
  
  -- 乘积证明
  Product :: LinearProof a b -> LinearProof a c -> LinearProof a (b & c)
  
  -- 和证明
  Sum :: LinearProof a c -> LinearProof b c -> LinearProof (a ⊕ b) c
```

### 4.2 线性逻辑的语义

```haskell
-- 线性逻辑的语义解释
class LinearSemantics a where
  -- 解释函数
  interpret :: a -> LinearValue a
  
  -- 语义等价
  semanticEquiv :: a -> b -> Bool

-- 线性值
data LinearValue a where
  -- 原子值
  Atom :: String -> LinearValue a
  
  -- 复合值
  Composite :: [LinearValue a] -> LinearValue a
  
  -- 函数值
  Function :: (LinearValue a -> LinearValue b) -> LinearValue (a ⊸ b)
```

## 5. Haskell中的线性类型系统实现

### 5.1 线性类型检查器

```haskell
-- 线性类型检查器
class LinearTypeChecker a where
  -- 类型检查
  typeCheck :: a -> Either String Type
  
  -- 线性性检查
  linearityCheck :: a -> Bool
  
  -- 资源使用检查
  resourceCheck :: a -> ResourceUsage

-- 资源使用信息
data ResourceUsage = ResourceUsage
  { used :: Set String
  , unused :: Set String
  , duplicated :: Set String
  } deriving (Show, Eq)

-- 线性类型检查的实现
instance LinearTypeChecker LinearTerm where
  typeCheck term = case term of
    Var x -> Right (varType x)
    App f x -> do
      tf <- typeCheck f
      tx <- typeCheck x
      case tf of
        LinearFunction a b | a == tx -> Right b
        _ -> Left "Type mismatch in application"
    Lambda x body -> do
      tbody <- typeCheck body
      Right (LinearFunction (varType x) tbody)
  
  linearityCheck term = case term of
    Var _ -> True
    App f x -> linearityCheck f && linearityCheck x
    Lambda x body -> linearityCheck body && not (duplicated x body)
  
  resourceCheck term = ResourceUsage
    { used = usedVars term
    , unused = unusedVars term
    , duplicated = duplicatedVars term
    }
```

### 5.2 线性类型系统的扩展

```haskell
-- 线性类型系统的扩展
class LinearTypeSystem a where
  -- 类型推导
  typeInference :: a -> Maybe Type
  
  -- 类型统一
  typeUnification :: Type -> Type -> Maybe Substitution
  
  -- 类型重构
  typeReconstruction :: a -> Maybe (a, Type)

-- 类型替换
type Substitution = Map String Type

-- 类型统一算法
unify :: Type -> Type -> Maybe Substitution
unify t1 t2 = case (t1, t2) of
  (Var x, t) -> Just (Map.singleton x t)
  (t, Var x) -> Just (Map.singleton x t)
  (LinearFunction a1 b1, LinearFunction a2 b2) -> do
    s1 <- unify a1 a2
    s2 <- unify (applySubst s1 b1) (applySubst s1 b2)
    return (composeSubst s1 s2)
  (Tensor a1 b1, Tensor a2 b2) -> do
    s1 <- unify a1 a2
    s2 <- unify (applySubst s1 b1) (applySubst s1 b2)
    return (composeSubst s1 s2)
  _ -> Nothing
```

## 6. 应用示例

### 6.1 线性数据结构

```haskell
-- 线性列表
data LinearList a = Nil | Cons a (LinearList a)

-- 线性列表的操作
linearMap :: (a ⊸ b) -> LinearList a ⊸ LinearList b
linearMap f Nil = Nil
linearMap f (Cons x xs) = Cons (f x) (linearMap f xs)

linearFold :: (b ⊸ a ⊸ b) -> b -> LinearList a ⊸ b
linearFold f z Nil = z
linearFold f z (Cons x xs) = linearFold f (f z x) xs

-- 线性树
data LinearTree a = Leaf a | Node (LinearTree a) (LinearTree a)

-- 线性树的操作
linearTreeMap :: (a ⊸ b) -> LinearTree a ⊸ LinearTree b
linearTreeMap f (Leaf x) = Leaf (f x)
linearTreeMap f (Node l r) = Node (linearTreeMap f l) (linearTreeMap f r)
```

### 6.2 线性协议

```haskell
-- 线性协议定义
data Protocol a b = Protocol
  { send :: a ⊸ Protocol b a
  , receive :: Protocol a b ⊸ (b, Protocol b a)
  }

-- 简单的消息传递协议
messageProtocol :: Protocol String String
messageProtocol = Protocol
  { send = \msg -> Protocol
      { send = \_ -> error "Protocol violation"
      , receive = \_ -> (msg, messageProtocol)
      }
  , receive = \_ -> ("", messageProtocol)
  }
```

## 7. 总结

线性逻辑连接词为资源管理提供了强大的理论基础：

1. **乘法连接词** (⊗, ⊸) 处理资源的精确使用
2. **加法连接词** (&, ⊕) 处理资源的选择和共享
3. **指数连接词** (!, ?) 处理资源的可重用性
4. **Haskell实现** 提供了实用的线性类型系统

这些连接词构成了完整的线性逻辑系统，为并发编程、资源管理和类型安全提供了坚实的理论基础。
