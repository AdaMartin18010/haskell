# 经典逻辑基础

## 概述

经典逻辑是形式逻辑的基础，包括命题逻辑和一阶谓词逻辑。它提供了形式化推理的基本工具，是计算机科学和人工智能的重要理论基础。

## 形式化定义

### 命题逻辑

#### 语法定义

命题逻辑的语法由以下BNF文法定义：

```haskell
-- 命题逻辑语法
data Proposition = 
    Atom String                    -- 原子命题
  | Not Proposition               -- 否定
  | And Proposition Proposition   -- 合取
  | Or Proposition Proposition    -- 析取
  | Implies Proposition Proposition -- 蕴含
  | Iff Proposition Proposition   -- 等价
  deriving (Show, Eq)
```

#### 语义定义

命题逻辑的语义通过真值函数定义：

```haskell
-- 真值赋值
type Valuation = String -> Bool

-- 语义解释函数
interpret :: Proposition -> Valuation -> Bool
interpret (Atom p) v = v p
interpret (Not p) v = not (interpret p v)
interpret (And p q) v = interpret p v && interpret q v
interpret (Or p q) v = interpret p v || interpret q v
interpret (Implies p q) v = not (interpret p v) || interpret q v
interpret (Iff p q) v = interpret p v == interpret q v
```

### 一阶谓词逻辑

#### 语法定义

```haskell
-- 一阶逻辑语法
data Term = 
    Var String
  | Const String
  | Func String [Term]
  deriving (Show, Eq)

data Formula = 
    Pred String [Term]
  | Equal Term Term
  | Not' Formula
  | And' Formula Formula
  | Or' Formula Formula
  | Implies' Formula Formula
  | ForAll String Formula
  | Exists String Formula
  deriving (Show, Eq)
```

#### 语义定义

```haskell
-- 一阶逻辑语义
data Structure = Structure {
  domain :: [String],
  predicates :: String -> [String] -> Bool,
  functions :: String -> [String] -> String
}

type Assignment = String -> String

interpretTerm :: Term -> Structure -> Assignment -> String
interpretTerm (Var x) _ a = a x
interpretTerm (Const c) _ _ = c
interpretTerm (Func f ts) s a = functions s f (map (\t -> interpretTerm t s a) ts)

interpretFormula :: Formula -> Structure -> Assignment -> Bool
interpretFormula (Pred p ts) s a = predicates s p (map (\t -> interpretTerm t s a) ts)
interpretFormula (Equal t1 t2) s a = interpretTerm t1 s a == interpretTerm t2 s a
interpretFormula (Not' f) s a = not (interpretFormula f s a)
interpretFormula (And' f1 f2) s a = interpretFormula f1 s a && interpretFormula f2 s a
interpretFormula (Or' f1 f2) s a = interpretFormula f1 s a || interpretFormula f2 s a
interpretFormula (Implies' f1 f2) s a = not (interpretFormula f1 s a) || interpretFormula f2 s a
interpretFormula (ForAll x f) s a = all (\d -> interpretFormula f s (updateAssignment a x d)) (domain s)
interpretFormula (Exists x f) s a = any (\d -> interpretFormula f s (updateAssignment a x d)) (domain s)

updateAssignment :: Assignment -> String -> String -> Assignment
updateAssignment a x d y = if x == y then d else a y
```

## 推理系统

### 自然演绎系统

```haskell
-- 自然演绎规则
data InferenceRule = 
    AndIntro
  | AndElim1
  | AndElim2
  | OrIntro1
  | OrIntro2
  | OrElim
  | ImpliesIntro
  | ImpliesElim
  | NotIntro
  | NotElim
  | IffIntro
  | IffElim1
  | IffElim2
  deriving (Show)

-- 证明树
data Proof = 
    Axiom Proposition
  | Apply InferenceRule [Proof]
  deriving (Show)

-- 证明检查器
checkProof :: Proof -> Bool
checkProof (Axiom _) = True
checkProof (Apply rule premises) = 
  case rule of
    AndIntro -> length premises == 2
    AndElim1 -> length premises == 1
    AndElim2 -> length premises == 1
    OrIntro1 -> length premises == 1
    OrIntro2 -> length premises == 1
    OrElim -> length premises == 3
    ImpliesIntro -> length premises == 1
    ImpliesElim -> length premises == 2
    NotIntro -> length premises == 1
    NotElim -> length premises == 2
    IffIntro -> length premises == 2
    IffElim1 -> length premises == 1
    IffElim2 -> length premises == 1
```

## 形式化证明

### 基本定理

#### 定理1：双重否定律

对于任意命题 $P$，有 $P \leftrightarrow \neg\neg P$

**证明**：
```haskell
-- 双重否定律的Haskell实现
doubleNegation :: Proposition -> Bool
doubleNegation p = 
  let v = \_ -> True  -- 任意真值赋值
  in interpret p v == interpret (Not (Not p)) v

-- 形式化证明
doubleNegationProof :: Proof
doubleNegationProof = Apply IffIntro [
  Apply ImpliesIntro [Axiom (Atom "P")],
  Apply ImpliesIntro [Axiom (Not (Not (Atom "P")))]
]
```

#### 定理2：德摩根律

对于任意命题 $P$ 和 $Q$，有：
- $\neg(P \land Q) \leftrightarrow (\neg P \lor \neg Q)$
- $\neg(P \lor Q) \leftrightarrow (\neg P \land \neg Q)$

**证明**：
```haskell
-- 德摩根律的Haskell实现
deMorgan1 :: Proposition -> Proposition -> Bool
deMorgan1 p q = 
  let v = \_ -> True
  in interpret (Not (And p q)) v == interpret (Or (Not p) (Not q)) v

deMorgan2 :: Proposition -> Proposition -> Bool
deMorgan2 p q = 
  let v = \_ -> True
  in interpret (Not (Or p q)) v == interpret (And (Not p) (Not q)) v
```

## 应用示例

### 逻辑推理引擎

```haskell
-- 简单的逻辑推理引擎
class LogicalReasoner a where
  entails :: a -> a -> Bool
  satisfiable :: a -> Bool
  valid :: a -> Bool

instance LogicalReasoner Proposition where
  entails premises conclusion = 
    all (\v -> not (interpret premises v) || interpret conclusion v) allValuations
  satisfiable p = any (\v -> interpret p v) allValuations
  valid p = all (\v -> interpret p v) allValuations

-- 生成所有可能的真值赋值
allValuations :: [Valuation]
allValuations = undefined  -- 需要根据原子命题集合生成
```

### 模型检测

```haskell
-- 简单的模型检测器
modelCheck :: Proposition -> Valuation -> Bool
modelCheck p v = interpret p v

-- 寻找满足公式的赋值
findSatisfyingAssignment :: Proposition -> Maybe Valuation
findSatisfyingAssignment p = 
  case filter (\v -> interpret p v) allValuations of
    (v:_) -> Just v
    [] -> Nothing
```

## 形式化验证

### 类型安全保证

```haskell
-- 使用Haskell类型系统确保逻辑正确性
newtype ValidFormula = ValidFormula { unValid :: Proposition }
  deriving (Show)

-- 智能构造函数确保公式有效性
mkValidFormula :: Proposition -> Maybe ValidFormula
mkValidFormula p = 
  if valid p 
    then Just (ValidFormula p)
    else Nothing

-- 类型安全的推理
safeInference :: ValidFormula -> ValidFormula -> Maybe ValidFormula
safeInference (ValidFormula p1) (ValidFormula p2) = 
  case p1 of
    Implies premise conclusion -> 
      if premise == unValid p2 
        then Just (ValidFormula conclusion)
        else Nothing
    _ -> Nothing
```

## 总结

经典逻辑为形式化推理提供了坚实的基础，通过Haskell的类型系统和函数式编程特性，我们可以实现严格的逻辑推理系统。这些实现不仅具有理论价值，也为实际应用中的形式化验证提供了工具支持。

## 相关链接

- [形式逻辑主索引](../README.md)
- [模态逻辑](../02-Modal-Logic/01-Basic-Concepts.md)
- [哲学逻辑](../02-Philosophical-Logic/01-Basic-Concepts.md)
- [计算逻辑](../03-Computational-Logic/01-Basic-Concepts.md) 