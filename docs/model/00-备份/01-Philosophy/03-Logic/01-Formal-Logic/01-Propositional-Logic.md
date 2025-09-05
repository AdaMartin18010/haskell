# 命题逻辑 (Propositional Logic)

## 概述

命题逻辑是形式逻辑的基础分支，研究命题之间的逻辑关系。本节将从形式化角度分析命题逻辑，并用Haskell实现相关的概念、推理规则和证明系统。

## 形式化定义

### 基本概念

```haskell
-- 命题变量的类型
type Proposition = String

-- 命题公式的数据类型
data Formula = 
    Atom Proposition                    -- 原子命题
  | Not Formula                        -- 否定
  | And Formula Formula                -- 合取
  | Or Formula Formula                 -- 析取
  | Implies Formula Formula            -- 蕴含
  | Iff Formula Formula                -- 等价
  | True                               -- 真值
  | False                              -- 假值
  deriving (Show, Eq)

-- 真值赋值
type Valuation = Proposition -> Bool

-- 公式的语义解释
interpret :: Formula -> Valuation -> Bool
interpret formula valuation = case formula of
  Atom p -> valuation p
  Not phi -> not (interpret phi valuation)
  And phi psi -> interpret phi valuation && interpret psi valuation
  Or phi psi -> interpret phi valuation || interpret psi valuation
  Implies phi psi -> not (interpret phi valuation) || interpret psi valuation
  Iff phi psi -> interpret phi valuation == interpret psi valuation
  True -> True
  False -> False
```

### 逻辑连接词

```haskell
-- 逻辑连接词的类型
data Connective = 
    Negation
  | Conjunction
  | Disjunction
  | Implication
  | Equivalence
  deriving (Show, Eq)

-- 连接词的优先级
connectivePrecedence :: Connective -> Int
connectivePrecedence conn = case conn of
  Negation -> 4
  Conjunction -> 3
  Disjunction -> 2
  Implication -> 1
  Equivalence -> 0

-- 连接词的真值表
connectiveTruthTable :: Connective -> [(Bool, Bool, Bool)]
connectiveTruthTable conn = case conn of
  Negation -> [(True, False), (False, True)]
  Conjunction -> [(True, True, True), (True, False, False), (False, True, False), (False, False, False)]
  Disjunction -> [(True, True, True), (True, False, True), (False, True, True), (False, False, False)]
  Implication -> [(True, True, True), (True, False, False), (False, True, True), (False, False, True)]
  Equivalence -> [(True, True, True), (True, False, False), (False, True, False), (False, False, True)]
```

## 推理规则

### 自然演绎系统

```haskell
-- 推理规则的类型
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
  | TrueIntro
  | FalseElim
  deriving (Show, Eq)

-- 证明的类型
data Proof = 
    Assumption Formula
  | RuleApplication InferenceRule [Proof] Formula
  deriving (Show, Eq)

-- 推理规则的应用
applyRule :: InferenceRule -> [Formula] -> Maybe Formula
applyRule rule premises = case (rule, premises) of
  (AndIntro, [phi, psi]) -> Just (And phi psi)
  (AndElim1, [And phi _]) -> Just phi
  (AndElim2, [And _ psi]) -> Just psi
  (OrIntro1, [phi]) -> Just (Or phi (Atom "Q"))  -- 需要指定第二个析取支
  (OrIntro2, [psi]) -> Just (Or (Atom "P") psi)  -- 需要指定第一个析取支
  (ImpliesElim, [Implies phi psi, phi']) -> 
    if phi == phi' then Just psi else Nothing
  (NotElim, [Not phi, phi']) -> 
    if phi == phi' then Just False else Nothing
  _ -> Nothing
```

### 公理系统

```haskell
-- 公理的类型
data Axiom = 
    Axiom1  -- p -> (q -> p)
  | Axiom2  -- (p -> (q -> r)) -> ((p -> q) -> (p -> r))
  | Axiom3  -- (¬p -> ¬q) -> (q -> p)
  deriving (Show, Eq)

-- 公理的实例化
instantiateAxiom :: Axiom -> Formula -> Formula -> Formula -> Maybe Formula
instantiateAxiom axiom p q r = case axiom of
  Axiom1 -> Just (Implies p (Implies q p))
  Axiom2 -> Just (Implies (Implies p (Implies q r)) (Implies (Implies p q) (Implies p r)))
  Axiom3 -> Just (Implies (Implies (Not p) (Not q)) (Implies q p))

-- 公理系统的证明
data AxiomaticProof = 
    AxiomInstance Axiom [Formula]
  | ModusPonens AxiomaticProof AxiomaticProof
  deriving (Show, Eq)
```

## 语义理论

### 真值表方法

```haskell
-- 获取公式中的所有命题变量
getPropositions :: Formula -> [Proposition]
getPropositions formula = case formula of
  Atom p -> [p]
  Not phi -> getPropositions phi
  And phi psi -> nub (getPropositions phi ++ getPropositions psi)
  Or phi psi -> nub (getPropositions phi ++ getPropositions psi)
  Implies phi psi -> nub (getPropositions phi ++ getPropositions psi)
  Iff phi psi -> nub (getPropositions phi ++ getPropositions psi)
  True -> []
  False -> []

-- 生成所有可能的真值赋值
generateValuations :: [Proposition] -> [Valuation]
generateValuations props = 
  let n = length props
      boolLists = replicateM n [True, False]
  in map (\bools -> \p -> bools !! (fromJust (elemIndex p props))) boolLists

-- 真值表
truthTable :: Formula -> [(Valuation, Bool)]
truthTable formula = 
  let props = getPropositions formula
      valuations = generateValuations props
  in map (\v -> (v, interpret formula v)) valuations

-- 检查公式是否为重言式
isTautology :: Formula -> Bool
isTautology formula = all snd (truthTable formula)

-- 检查公式是否为矛盾式
isContradiction :: Formula -> Bool
isContradiction formula = all (not . snd) (truthTable formula)

-- 检查公式是否为可满足式
isSatisfiable :: Formula -> Bool
isSatisfiable formula = any snd (truthTable formula)
```

### 语义后承

```haskell
-- 语义后承关系
semanticEntailment :: [Formula] -> Formula -> Bool
semanticEntailment premises conclusion = 
  let allProps = nub (concatMap getPropositions (conclusion : premises))
      valuations = generateValuations allProps
  in all (\v -> 
    if all (\premise -> interpret premise v) premises 
    then interpret conclusion v 
    else True) valuations

-- 逻辑等价
logicalEquivalence :: Formula -> Formula -> Bool
logicalEquivalence phi psi = 
  semanticEntailment [phi] psi && semanticEntailment [psi] phi
```

## 应用示例

### 经典推理

```haskell
-- 假言推理 (Modus Ponens)
modusPonens :: Formula -> Formula -> Maybe Formula
modusPonens (Implies p q) p' = 
  if p == p' then Just q else Nothing
modusPonens _ _ = Nothing

-- 假言三段论
hypotheticalSyllogism :: Formula -> Formula -> Maybe Formula
hypotheticalSyllogism (Implies p q) (Implies q r) = 
  Just (Implies p r)
hypotheticalSyllogism _ _ = Nothing

-- 构造性二难推理
constructiveDilemma :: Formula -> Formula -> Formula -> Maybe Formula
constructiveDilemma (Or p q) (Implies p r) (Implies q s) = 
  Just (Or r s)
constructiveDilemma _ _ _ = Nothing
```

### 逻辑等价

```haskell
-- 德摩根律
deMorgan1 :: Formula -> Formula
deMorgan1 (Not (And p q)) = Or (Not p) (Not q)
deMorgan1 formula = formula

deMorgan2 :: Formula -> Formula
deMorgan2 (Not (Or p q)) = And (Not p) (Not q)
deMorgan2 formula = formula

-- 分配律
distributive1 :: Formula -> Formula
distributive1 (And p (Or q r)) = Or (And p q) (And p r)
distributive1 formula = formula

distributive2 :: Formula -> Formula
distributive2 (Or p (And q r)) = And (Or p q) (Or p r)
distributive2 formula = formula
```

## 形式化验证

### 一致性检查

```haskell
-- 检查推理规则的一致性
checkInferenceConsistency :: IO ()
checkInferenceConsistency = do
  putStrLn "=== 推理规则一致性检查 ==="
  
  -- 检查合取引入和消除的一致性
  let phi = Atom "P"
      psi = Atom "Q"
      conj = And phi psi
      intro = applyRule AndIntro [phi, psi]
      elim1 = applyRule AndElim1 [conj]
      elim2 = applyRule AndElim2 [conj]
  
  putStrLn $ "合取引入: " ++ show intro
  putStrLn $ "合取消除1: " ++ show elim1
  putStrLn $ "合取消除2: " ++ show elim2
  
  -- 检查蕴含消除的一致性
  let impl = Implies phi psi
      mp = applyRule ImpliesElim [impl, phi]
  putStrLn $ "蕴含消除: " ++ show mp
```

### 完备性检查

```haskell
-- 检查证明系统的完备性
checkCompleteness :: IO ()
checkCompleteness = do
  putStrLn "=== 证明系统完备性检查 ==="
  
  -- 检查经典重言式
  let excludedMiddle = Or (Atom "P") (Not (Atom "P"))
      doubleNegation = Iff (Atom "P") (Not (Not (Atom "P")))
      contraposition = Iff (Implies (Atom "P") (Atom "Q")) 
                           (Implies (Not (Atom "Q")) (Not (Atom "P")))
  
  putStrLn $ "排中律是重言式: " ++ show (isTautology excludedMiddle)
  putStrLn $ "双重否定是重言式: " ++ show (isTautology doubleNegation)
  putStrLn $ "逆否命题是重言式: " ++ show (isTautology contraposition)
```

## 总结

命题逻辑通过形式化方法建立了严格的逻辑系统：

1. **语法系统**：定义了命题公式的构造规则
2. **语义系统**：提供了真值解释和语义后承
3. **证明系统**：建立了自然演绎和公理化证明
4. **推理规则**：定义了有效的推理模式

通过Haskell的形式化实现，我们可以：

- 严格定义逻辑概念
- 验证推理规则的正确性
- 检查证明的有效性
- 分析逻辑等价关系

这种形式化方法不仅澄清了逻辑概念，还为逻辑学研究提供了精确的分析工具。

---

**相关链接**：

- [谓词逻辑](../02-Predicate-Logic.md)
- [模态逻辑](../03-Modal-Logic.md)
- [非经典逻辑](../04-Non-Classical-Logic.md)
- [逻辑哲学](../05-Philosophy-of-Logic.md)
