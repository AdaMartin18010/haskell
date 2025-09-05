# 谓词逻辑 (Predicate Logic)

## 概述

谓词逻辑是形式逻辑的核心分支，扩展了命题逻辑，引入了量词和谓词，能够表达更复杂的逻辑关系。

## 基本概念

### 谓词 (Predicates)

谓词是描述对象性质或关系的函数，返回真值。

```haskell
-- 谓词类型定义
type Predicate a = a -> Bool

-- 一元谓词示例
isEven :: Predicate Integer
isEven n = n `mod` 2 == 0

isPositive :: Predicate Integer
isPositive n = n > 0

-- 二元谓词示例
type BinaryPredicate a b = a -> b -> Bool

divides :: BinaryPredicate Integer Integer
divides a b = b `mod` a == 0

greaterThan :: BinaryPredicate Integer Integer
greaterThan a b = a > b
```

### 量词 (Quantifiers)

#### 全称量词 (Universal Quantifier)

全称量词 ∀ 表示"对所有"。

```haskell
-- 全称量词的类型定义
type UniversalQuantifier a = (a -> Bool) -> Bool

-- 全称量词的实现
forall :: [a] -> (a -> Bool) -> Bool
forall xs p = all p xs

-- 示例：所有偶数都是整数
allEvenAreIntegers :: [Integer] -> Bool
allEvenAreIntegers xs = forall xs (\x -> isEven x ==> isInteger x)
  where
    isInteger :: Integer -> Bool
    isInteger _ = True
    
    (==>) :: Bool -> Bool -> Bool
    True ==> False = False
    _ ==> _ = True
```

#### 存在量词 (Existential Quantifier)

存在量词 ∃ 表示"存在"。

```haskell
-- 存在量词的类型定义
type ExistentialQuantifier a = (a -> Bool) -> Bool

-- 存在量词的实现
exists :: [a] -> (a -> Bool) -> Bool
exists xs p = any p xs

-- 示例：存在一个正偶数
existsPositiveEven :: [Integer] -> Bool
existsPositiveEven xs = exists xs (\x -> isEven x && isPositive x)
```

### 自由变量和约束变量

```haskell
-- 自由变量和约束变量的表示
data Term a = Variable String
            | Constant a
            | Function String [Term a]

data Formula a = Atomic (Predicate a) [Term a]
               | Not (Formula a)
               | And (Formula a) (Formula a)
               | Or (Formula a) (Formula a)
               | Implies (Formula a) (Formula a)
               | ForAll String (Formula a)
               | Exists String (Formula a)

-- 自由变量计算
freeVariables :: Formula a -> [String]
freeVariables (Atomic _ _) = []
freeVariables (Not phi) = freeVariables phi
freeVariables (And phi psi) = freeVariables phi ++ freeVariables psi
freeVariables (Or phi psi) = freeVariables phi ++ freeVariables psi
freeVariables (Implies phi psi) = freeVariables phi ++ freeVariables psi
freeVariables (ForAll x phi) = filter (/= x) (freeVariables phi)
freeVariables (Exists x phi) = filter (/= x) (freeVariables phi)
```

## 形式化语义

### 解释 (Interpretation)

```haskell
-- 解释的定义
data Interpretation a = Interpretation
  { domain :: [a]
  , constants :: [(String, a)]
  , functions :: [(String, [a] -> a)]
  , predicates :: [(String, [a] -> Bool)]
  }

-- 项的解释
interpretTerm :: Interpretation a -> [(String, a)] -> Term a -> a
interpretTerm _ env (Variable x) = 
  case lookup x env of
    Just v -> v
    Nothing -> error $ "Unbound variable: " ++ x
interpretTerm interp _ (Constant c) = c
interpretTerm interp env (Function f args) =
  case lookup f (functions interp) of
    Just func -> func (map (interpretTerm interp env) args)
    Nothing -> error $ "Undefined function: " ++ f

-- 公式的解释
interpretFormula :: Interpretation a -> [(String, a)] -> Formula a -> Bool
interpretFormula interp env (Atomic p args) =
  case lookup (predicateName p) (predicates interp) of
    Just pred -> pred (map (interpretTerm interp env) args)
    Nothing -> error $ "Undefined predicate: " ++ predicateName p
  where
    predicateName :: Predicate a -> String
    predicateName _ = "pred" -- 简化处理

interpretFormula interp env (Not phi) = not (interpretFormula interp env phi)
interpretFormula interp env (And phi psi) = 
  interpretFormula interp env phi && interpretFormula interp env psi
interpretFormula interp env (Or phi psi) = 
  interpretFormula interp env phi || interpretFormula interp env psi
interpretFormula interp env (Implies phi psi) = 
  not (interpretFormula interp env phi) || interpretFormula interp env psi

interpretFormula interp env (ForAll x phi) =
  all (\val -> interpretFormula interp ((x, val) : env) phi) (domain interp)

interpretFormula interp env (Exists x phi) =
  any (\val -> interpretFormula interp ((x, val) : env) phi) (domain interp)
```

## 推理规则

### 全称量词规则

```haskell
-- 全称引入规则
universalIntroduction :: (a -> Bool) -> (a -> Formula b) -> Formula b
universalIntroduction domain prop = ForAll "x" (prop (undefined :: a))

-- 全称消除规则
universalElimination :: Formula a -> a -> Formula a
universalElimination (ForAll x phi) t = substitute x t phi
  where
    substitute :: String -> a -> Formula a -> Formula a
    substitute _ _ phi = phi -- 简化实现
```

### 存在量词规则

```haskell
-- 存在引入规则
existentialIntroduction :: Formula a -> a -> Formula a
existentialIntroduction phi t = Exists "x" (substitute "x" t phi)
  where
    substitute :: String -> a -> Formula a -> Formula a
    substitute _ _ phi = phi -- 简化实现

-- 存在消除规则
existentialElimination :: Formula a -> (a -> Formula a) -> Formula a
existentialElimination (Exists x phi) psi = psi (undefined :: a)
```

## 形式化证明

### 自然演绎系统

```haskell
-- 证明树的数据结构
data Proof a = Axiom (Formula a)
             | Assumption (Formula a)
             | AndIntro (Proof a) (Proof a)
             | AndElim1 (Proof a)
             | AndElim2 (Proof a)
             | OrIntro1 (Formula a) (Proof a)
             | OrIntro2 (Formula a) (Proof a)
             | OrElim (Proof a) (Proof a) (Proof a)
             | ImpliesIntro (Formula a) (Proof a)
             | ImpliesElim (Proof a) (Proof a)
             | NotIntro (Formula a) (Proof a)
             | NotElim (Proof a) (Proof a)
             | ForAllIntro (Proof a)
             | ForAllElim (Proof a) (Term a)
             | ExistsIntro (Term a) (Proof a)
             | ExistsElim (Proof a) (Proof a)

-- 证明的有效性检查
isValidProof :: Proof a -> Bool
isValidProof (Axiom _) = True
isValidProof (Assumption _) = True
isValidProof (AndIntro p1 p2) = isValidProof p1 && isValidProof p2
isValidProof (AndElim1 p) = isValidProof p
isValidProof (AndElim2 p) = isValidProof p
isValidProof (OrIntro1 _ p) = isValidProof p
isValidProof (OrIntro2 _ p) = isValidProof p
isValidProof (OrElim p1 p2 p3) = 
  isValidProof p1 && isValidProof p2 && isValidProof p3
isValidProof (ImpliesIntro _ p) = isValidProof p
isValidProof (ImpliesElim p1 p2) = isValidProof p1 && isValidProof p2
isValidProof (NotIntro _ p) = isValidProof p
isValidProof (NotElim p1 p2) = isValidProof p1 && isValidProof p2
isValidProof (ForAllIntro p) = isValidProof p
isValidProof (ForAllElim p _) = isValidProof p
isValidProof (ExistsIntro _ p) = isValidProof p
isValidProof (ExistsElim p1 p2) = isValidProof p1 && isValidProof p2

-- 证明的结论
conclusion :: Proof a -> Formula a
conclusion (Axiom phi) = phi
conclusion (Assumption phi) = phi
conclusion (AndIntro _ _) = And (conclusion undefined) (conclusion undefined)
conclusion (AndElim1 p) = undefined -- 需要根据具体证明确定
conclusion (AndElim2 p) = undefined
conclusion (OrIntro1 phi _) = Or phi (conclusion undefined)
conclusion (OrIntro2 phi _) = Or (conclusion undefined) phi
conclusion (OrElim _ _ _) = undefined
conclusion (ImpliesIntro phi _) = Implies phi (conclusion undefined)
conclusion (ImpliesElim _ _) = undefined
conclusion (NotIntro phi _) = Not phi
conclusion (NotElim _ _) = undefined
conclusion (ForAllIntro _) = ForAll "x" (conclusion undefined)
conclusion (ForAllElim _ _) = undefined
conclusion (ExistsIntro _ _) = Exists "x" (conclusion undefined)
conclusion (ExistsElim _ _) = undefined
```

## 应用示例

### 数学定理的形式化

```haskell
-- 示例：所有自然数都是非负的
naturalNumbersNonNegative :: [Integer] -> Bool
naturalNumbersNonNegative domain = 
  forall domain (\n -> n >= 0)

-- 示例：存在一个最小的自然数
existsSmallestNatural :: [Integer] -> Bool
existsSmallestNatural domain = 
  exists domain (\n -> 
    n >= 0 && forall domain (\m -> m >= 0 ==> m >= n))

-- 示例：对于所有x，如果x是偶数，那么x²也是偶数
evenSquareTheorem :: [Integer] -> Bool
evenSquareTheorem domain = 
  forall domain (\x -> 
    isEven x ==> isEven (x * x))
```

### 逻辑推理示例

```haskell
-- 三段论推理
-- 前提1：所有人都是动物
-- 前提2：苏格拉底是人
-- 结论：苏格拉底是动物

data Entity = Socrates | Plato | Aristotle deriving (Eq, Show)

isHuman :: Entity -> Bool
isHuman Socrates = True
isHuman Plato = True
isHuman Aristotle = True

isAnimal :: Entity -> Bool
isAnimal e = isHuman e -- 简化假设

-- 形式化三段论
syllogism :: [Entity] -> Bool
syllogism entities = 
  forall entities (\e -> isHuman e ==> isAnimal e) && -- 前提1
  isHuman Socrates && -- 前提2
  isAnimal Socrates   -- 结论
```

## 元理论性质

### 可靠性 (Soundness)

```haskell
-- 可靠性定理：如果从Γ可以证明φ，那么Γ语义蕴涵φ
soundness :: [Formula a] -> Formula a -> Proof a -> Bool
soundness gamma phi proof = 
  isValidProof proof && 
  conclusion proof == phi &&
  semanticEntailment gamma phi
  where
    semanticEntailment :: [Formula a] -> Formula a -> Bool
    semanticEntailment _ _ = True -- 简化实现
```

### 完备性 (Completeness)

```haskell
-- 完备性定理：如果Γ语义蕴涵φ，那么从Γ可以证明φ
completeness :: [Formula a] -> Formula a -> Bool
completeness gamma phi = 
  semanticEntailment gamma phi ==> 
  hasProof gamma phi
  where
    semanticEntailment :: [Formula a] -> Formula a -> Bool
    semanticEntailment _ _ = True
    
    hasProof :: [Formula a] -> Formula a -> Bool
    hasProof _ _ = True
    
    (==>) :: Bool -> Bool -> Bool
    True ==> False = False
    _ ==> _ = True
```

## 扩展和变体

### 多排序逻辑

```haskell
-- 多排序逻辑的类型定义
data Sort = Individual | Set | Function deriving (Eq, Show)

data MultiSortedTerm = 
  MSVariable String Sort
  | MSConstant String Sort
  | MSFunction String [Sort] Sort [MultiSortedTerm]

data MultiSortedFormula =
  MSAtomic String [MultiSortedTerm]
  | MSNegation MultiSortedFormula
  | MSConjunction MultiSortedFormula MultiSortedFormula
  | MSDisjunction MultiSortedFormula MultiSortedFormula
  | MSImplication MultiSortedFormula MultiSortedFormula
  | MSForAll String Sort MultiSortedFormula
  | MSExists String Sort MultiSortedFormula
```

### 高阶逻辑

```haskell
-- 高阶逻辑的类型定义
data HigherOrderTerm = 
  HOVariable String Type
  | HOConstant String Type
  | HOApplication HigherOrderTerm HigherOrderTerm
  | HOLambda String Type HigherOrderTerm

data Type = BaseType String
          | FunctionType Type Type
          | ProductType [Type]
          | SumType [Type]

data HigherOrderFormula =
  HOAtomic HigherOrderTerm
  | HONegation HigherOrderFormula
  | HOConjunction HigherOrderFormula HigherOrderFormula
  | HODisjunction HigherOrderFormula HigherOrderFormula
  | HOImplication HigherOrderFormula HigherOrderFormula
  | HOForAll String Type HigherOrderFormula
  | HOExists String Type HigherOrderFormula
```

## 总结

谓词逻辑为形式化推理提供了强大的基础，通过引入量词和谓词，能够表达复杂的逻辑关系。在Haskell中，我们可以通过类型系统和函数式编程的特性来优雅地实现谓词逻辑的各种概念和推理规则。

谓词逻辑的主要特点：

1. **表达能力**：比命题逻辑具有更强的表达能力
2. **形式化程度**：提供严格的语义定义和推理规则
3. **应用广泛**：在数学、计算机科学、人工智能等领域有广泛应用
4. **理论基础**：为高阶逻辑和类型论提供基础

通过Haskell的实现，我们不仅能够理解谓词逻辑的形式化定义，还能够实际运行和验证逻辑推理过程。
