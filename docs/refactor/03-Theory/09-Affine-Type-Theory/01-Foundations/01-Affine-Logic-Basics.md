# 仿射逻辑基础 (Affine Logic Basics)

## 1. 概述

仿射逻辑是线性逻辑的弱化版本，它允许资源的丢弃（弱化），但不允许重复使用（收缩）。在仿射逻辑中，每个资源最多只能被使用一次，这与线性逻辑的"恰好使用一次"不同。

## 2. 仿射逻辑的基本概念

### 2.1 仿射性 (Affinity)

仿射性是指资源可以被丢弃但不能重复使用的性质。

**形式化定义：**

```haskell
-- 仿射类型类
class Affine a where
  -- 弱化：丢弃资源
  weaken :: a -> ()
  
  -- 检查是否已被使用
  isUsed :: a -> Bool
  
  -- 获取资源（如果未使用）
  consume :: a -> Maybe a

-- 仿射值的包装
newtype AffineValue a = AffineValue
  { unAffineValue :: Maybe a
  }

-- 仿射值的实例
instance Affine (AffineValue a) where
  weaken (AffineValue _) = ()
  
  isUsed (AffineValue Nothing) = True
  isUsed (AffineValue (Just _)) = False
  
  consume (AffineValue Nothing) = Nothing
  consume (AffineValue (Just x)) = Just (AffineValue (Just x))

-- 创建仿射值
affine :: a -> AffineValue a
affine x = AffineValue (Just x)

-- 使用仿射值
useAffine :: AffineValue a -> (a -> b) -> Maybe b
useAffine (AffineValue Nothing) _ = Nothing
useAffine (AffineValue (Just x)) f = Just (f x)
```

### 2.2 仿射逻辑规则

**形式化定义：**

```haskell
-- 仿射逻辑的证明系统
data AffineProof a b where
  -- 恒等公理
  AffineId :: AffineProof a a
  
  -- 弱化规则
  AffineWeaken :: AffineProof a b -> AffineProof a b
  
  -- 张量积规则
  AffineTensor :: AffineProof a b -> AffineProof c d -> AffineProof (a ⊗ c) (b ⊗ d)
  
  -- 仿射蕴含规则
  AffineImpl :: AffineProof (a ⊗ b) c -> AffineProof a (b ⊸ c)
  
  -- 乘积规则
  AffineProduct :: AffineProof a b -> AffineProof a c -> AffineProof a (b & c)
  
  -- 和规则
  AffineSum :: AffineProof a c -> AffineProof b c -> AffineProof (a ⊕ b) c

-- 仿射逻辑的规则
affineIdentity :: AffineProof a a
affineIdentity = AffineId

affineWeakening :: AffineProof a b -> AffineProof a b
affineWeakening = AffineWeaken

affineTensor :: AffineProof a b -> AffineProof c d -> AffineProof (a ⊗ c) (b ⊗ d)
affineTensor = AffineTensor

affineImpl :: AffineProof (a ⊗ b) c -> AffineProof a (b ⊸ c)
affineImpl = AffineImpl
```

## 3. 仿射连接词

### 3.1 乘法连接词

#### 3.1.1 张量积 (Tensor Product) ⊗

**形式化定义：**

```haskell
-- 仿射张量积
data AffineTensor a b = AffineTensor
  { first :: AffineValue a
  , second :: AffineValue b
  }

-- 仿射张量积的构造
affineTensor :: AffineValue a -> AffineValue b -> AffineTensor a b
affineTensor x y = AffineTensor x y

-- 仿射张量积的消除
affineTensorElim :: AffineTensor a b -> (AffineValue a -> AffineValue b -> c) -> c
affineTensorElim (AffineTensor x y) f = f x y

-- 仿射张量积的交换
affineTensorComm :: AffineTensor a b -> AffineTensor b a
affineTensorComm (AffineTensor x y) = AffineTensor y x

-- 仿射张量积的结合
affineTensorAssoc :: AffineTensor (AffineTensor a b) c -> AffineTensor a (AffineTensor b c)
affineTensorAssoc (AffineTensor (AffineTensor x y) z) = AffineTensor x (AffineTensor y z)
```

#### 3.1.2 仿射蕴含 (Affine Implication) ⊸

**形式化定义：**

```haskell
-- 仿射函数类型
newtype AffineFunction a b = AffineFunction
  { applyAffine :: AffineValue a -> AffineValue b
  }

-- 仿射函数的构造
affineFunction :: (AffineValue a -> AffineValue b) -> AffineFunction a b
affineFunction f = AffineFunction f

-- 仿射函数的应用
applyAffine :: AffineFunction a b -> AffineValue a -> AffineValue b
applyAffine (AffineFunction f) x = f x

-- 仿射函数的组合
composeAffine :: AffineFunction b c -> AffineFunction a b -> AffineFunction a c
composeAffine (AffineFunction g) (AffineFunction f) = AffineFunction (g . f)

-- 仿射函数的Curry化
curryAffine :: AffineFunction (AffineTensor a b) c -> AffineFunction a (AffineFunction b c)
curryAffine (AffineFunction f) = AffineFunction $ \a ->
  AffineFunction $ \b -> f (AffineTensor a b)

-- 仿射函数的反Curry化
uncurryAffine :: AffineFunction a (AffineFunction b c) -> AffineFunction (AffineTensor a b) c
uncurryAffine (AffineFunction f) = AffineFunction $ \(AffineTensor a b) ->
  applyAffine (f a) b
```

### 3.2 加法连接词

#### 3.2.1 乘积 (Product) &

**形式化定义：**

```haskell
-- 仿射乘积类型
data AffineProduct a b = AffineProduct
  { left :: AffineValue a
  , right :: AffineValue b
  }

-- 仿射乘积的构造
affineProduct :: AffineValue a -> AffineValue b -> AffineProduct a b
affineProduct x y = AffineProduct x y

-- 仿射乘积的投影
fstAffine :: AffineProduct a b -> AffineValue a
fstAffine (AffineProduct x _) = x

sndAffine :: AffineProduct a b -> AffineValue b
sndAffine (AffineProduct _ y) = y

-- 仿射乘积的配对
pairAffine :: (c -> AffineValue a) -> (c -> AffineValue b) -> c -> AffineProduct a b
pairAffine f g c = AffineProduct (f c) (g c)
```

#### 3.2.2 和 (Sum) ⊕

**形式化定义：**

```haskell
-- 仿射和类型
data AffineSum a b = AffineInL (AffineValue a) | AffineInR (AffineValue b)

-- 仿射和的构造
affineInL :: AffineValue a -> AffineSum a b
affineInL = AffineInL

affineInR :: AffineValue b -> AffineSum a b
affineInR = AffineInR

-- 仿射和的消除
caseAffineSum :: AffineSum a b -> (AffineValue a -> c) -> (AffineValue b -> c) -> c
caseAffineSum (AffineInL x) f _ = f x
caseAffineSum (AffineInR y) _ g = g y

-- 仿射和的映射
mapAffineSum :: (AffineValue a -> AffineValue c) -> (AffineValue b -> AffineValue d) -> AffineSum a b -> AffineSum c d
mapAffineSum f _ (AffineInL x) = AffineInL (f x)
mapAffineSum _ g (AffineInR y) = AffineInR (g y)
```

## 4. 仿射指数连接词

### 4.1 必然性 (Of Course)

!

**形式化定义：**

```haskell
-- 仿射必然性类型
newtype AffineOfCourse a = AffineOfCourse
  { unAffineOfCourse :: AffineValue a
  }

-- 仿射必然性的构造
affineOfCourse :: AffineValue a -> AffineOfCourse a
affineOfCourse = AffineOfCourse

-- 仿射必然性的消除
unAffineOfCourse :: AffineOfCourse a -> AffineValue a
unAffineOfCourse (AffineOfCourse x) = x

-- 仿射必然性的弱化
affineWeaken :: AffineOfCourse a -> AffineOfCourse b -> AffineOfCourse a
affineWeaken (AffineOfCourse x) _ = AffineOfCourse x

-- 仿射必然性的交换
affineExchange :: AffineOfCourse a -> AffineOfCourse b -> AffineOfCourse b -> AffineOfCourse a
affineExchange (AffineOfCourse x) _ _ = AffineOfCourse x
```

### 4.2 可能性 (Why Not) ?

**形式化定义：**

```haskell
-- 仿射可能性类型
newtype AffineWhyNot a = AffineWhyNot
  { unAffineWhyNot :: AffineValue a
  }

-- 仿射可能性的构造
affineWhyNot :: AffineValue a -> AffineWhyNot a
affineWhyNot = AffineWhyNot

-- 仿射可能性的消除
unAffineWhyNot :: AffineWhyNot a -> AffineValue a
unAffineWhyNot (AffineWhyNot x) = x

-- 仿射可能性的对偶性
affineDualOfCourse :: AffineOfCourse a -> AffineWhyNot (AffineFunction a ())
affineDualOfCourse (AffineOfCourse x) = AffineWhyNot $ AffineFunction $ \_ -> ()

affineDualWhyNot :: AffineWhyNot a -> AffineOfCourse (AffineFunction () a)
affineDualWhyNot (AffineWhyNot x) = AffineOfCourse $ AffineFunction $ \_ -> x
```

## 5. 仿射逻辑的语义

### 5.1 仿射语义解释

**形式化定义：**

```haskell
-- 仿射逻辑的语义解释
class AffineSemantics a where
  -- 解释函数
  interpret :: a -> AffineValue a
  
  -- 语义等价
  semanticEquiv :: a -> b -> Bool
  
  -- 资源使用分析
  resourceUsage :: a -> ResourceUsage

-- 仿射值
data AffineValue a where
  -- 原子值
  AffineAtom :: String -> AffineValue a
  
  -- 复合值
  AffineComposite :: [AffineValue a] -> AffineValue a
  
  -- 函数值
  AffineFunction :: (AffineValue a -> AffineValue b) -> AffineValue (a ⊸ b)
  
  -- 未使用值
  AffineUnused :: AffineValue a

-- 资源使用信息
data ResourceUsage = ResourceUsage
  { used :: Set String
  , unused :: Set String
  , discarded :: Set String
  } deriving (Show, Eq)
```

### 5.2 仿射逻辑的模型

**形式化定义：**

```haskell
-- 仿射逻辑的模型
class AffineModel a where
  -- 模型解释
  modelInterpret :: a -> AffineModel a
  
  -- 模型验证
  modelValidate :: a -> Bool
  
  -- 模型转换
  modelTransform :: a -> b -> AffineModel b

-- 仿射逻辑的Kripke模型
data AffineKripkeModel = AffineKripkeModel
  { worlds :: Set World
  , accessibility :: World -> Set World
  , valuation :: World -> Prop -> Bool
  }

-- 世界
type World = Int

-- 命题
type Prop = String

-- 仿射Kripke模型的解释
interpretAffineKripke :: AffineKripkeModel -> AffineFormula -> World -> Bool
interpretAffineKripke model formula world = case formula of
  AffineAtom p -> valuation model world p
  AffineAnd f1 f2 -> interpretAffineKripke model f1 world && interpretAffineKripke model f2 world
  AffineOr f1 f2 -> interpretAffineKripke model f1 world || interpretAffineKripke model f2 world
  AffineImpl f1 f2 -> all (\w -> not (interpretAffineKripke model f1 w) || interpretAffineKripke model f2 w) (accessibility model world)
  AffineOfCourse f -> all (\w -> interpretAffineKripke model f w) (accessibility model world)
```

## 6. Haskell中的仿射类型系统

### 6.1 仿射类型检查器

**形式化定义：**

```haskell
-- 仿射类型检查器
class AffineTypeChecker a where
  -- 类型检查
  typeCheck :: a -> Either String Type
  
  -- 仿射性检查
  affinityCheck :: a -> Bool
  
  -- 资源使用检查
  resourceCheck :: a -> ResourceUsage

-- 仿射类型检查的实现
instance AffineTypeChecker AffineTerm where
  typeCheck term = case term of
    AffineVar x -> Right (varType x)
    AffineApp f x -> do
      tf <- typeCheck f
      tx <- typeCheck x
      case tf of
        AffineFunction a b | a == tx -> Right b
        _ -> Left "Type mismatch in application"
    AffineLambda x body -> do
      tbody <- typeCheck body
      Right (AffineFunction (varType x) tbody)
  
  affinityCheck term = case term of
    AffineVar _ -> True
    AffineApp f x -> affinityCheck f && affinityCheck x
    AffineLambda x body -> affinityCheck body && not (duplicated x body)
  
  resourceCheck term = ResourceUsage
    { used = usedVars term
    , unused = unusedVars term
    , discarded = discardedVars term
    }
```

### 6.2 仿射类型系统的扩展

**形式化定义：**

```haskell
-- 仿射类型系统的扩展
class AffineTypeSystem a where
  -- 类型推导
  typeInference :: a -> Maybe Type
  
  -- 类型统一
  typeUnification :: Type -> Type -> Maybe Substitution
  
  -- 类型重构
  typeReconstruction :: a -> Maybe (a, Type)

-- 类型替换
type Substitution = Map String Type

-- 仿射类型统一算法
unifyAffine :: Type -> Type -> Maybe Substitution
unifyAffine t1 t2 = case (t1, t2) of
  (Var x, t) -> Just (Map.singleton x t)
  (t, Var x) -> Just (Map.singleton x t)
  (AffineFunction a1 b1, AffineFunction a2 b2) -> do
    s1 <- unifyAffine a1 a2
    s2 <- unifyAffine (applySubst s1 b1) (applySubst s1 b2)
    return (composeSubst s1 s2)
  (AffineTensor a1 b1, AffineTensor a2 b2) -> do
    s1 <- unifyAffine a1 a2
    s2 <- unifyAffine (applySubst s1 b1) (applySubst s1 b2)
    return (composeSubst s1 s2)
  _ -> Nothing
```

## 7. 应用示例

### 7.1 仿射数据结构

```haskell
-- 仿射列表
data AffineList a = AffineNil | AffineCons (AffineValue a) (AffineList a)

-- 仿射列表的操作
affineMap :: (AffineValue a -> AffineValue b) -> AffineList a -> AffineList b
affineMap _ AffineNil = AffineNil
affineMap f (AffineCons x xs) = AffineCons (f x) (affineMap f xs)

affineFold :: (b -> AffineValue a -> b) -> b -> AffineList a -> b
affineFold f z AffineNil = z
affineFold f z (AffineCons x xs) = affineFold f (f z x) xs

-- 仿射树
data AffineTree a = AffineLeaf (AffineValue a) | AffineNode (AffineTree a) (AffineTree a)

-- 仿射树的操作
affineTreeMap :: (AffineValue a -> AffineValue b) -> AffineTree a -> AffineTree b
affineTreeMap f (AffineLeaf x) = AffineLeaf (f x)
affineTreeMap f (AffineNode l r) = AffineNode (affineTreeMap f l) (affineTreeMap f r)
```

### 7.2 仿射协议

```haskell
-- 仿射协议定义
data AffineProtocol a b = AffineProtocol
  { affineSend :: AffineValue a -> AffineProtocol b a
  , affineReceive :: AffineProtocol a b -> (AffineValue b, AffineProtocol b a)
  }

-- 简单的消息传递协议
affineMessageProtocol :: AffineProtocol String String
affineMessageProtocol = AffineProtocol
  { affineSend = \msg -> AffineProtocol
      { affineSend = \_ -> error "Protocol violation"
      , affineReceive = \_ -> (affine "", affineMessageProtocol)
      }
  , affineReceive = \_ -> (affine "", affineMessageProtocol)
  }
```

## 8. 总结

仿射逻辑基础为资源管理提供了重要的理论基础：

1. **仿射性** - 资源可以被丢弃但不能重复使用
2. **弱化规则** - 允许资源的丢弃
3. **连接词** - 乘法、加法、指数连接词
4. **语义解释** - 完整的语义模型
5. **Haskell实现** - 实用的类型系统

仿射逻辑为Rust等语言的借用检查器提供了理论基础，是现代编程语言设计的重要工具。
