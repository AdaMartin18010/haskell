# Kripke语义理论

## 概述

Kripke语义是模态逻辑的标准语义学，由Saul Kripke在20世纪60年代提出。它为模态逻辑提供了直观且严格的语义解释，广泛应用于哲学、计算机科学和人工智能领域。

## 数学定义

### Kripke框架

**Kripke框架**是一个二元组 $\mathcal{F} = (W, R)$，其中：
- $W$ 是非空集合，称为可能世界集（worlds）
- $R \subseteq W \times W$ 是二元关系，称为可达关系（accessibility relation）

### Kripke模型

**Kripke模型**是一个三元组 $\mathcal{M} = (W, R, V)$，其中：
- $(W, R)$ 是Kripke框架
- $V: \Phi \to \mathcal{P}(W)$ 是赋值函数，将每个命题变量映射到可能世界的子集

### 真值定义

设 $\mathcal{M} = (W, R, V)$ 是Kripke模型，$w \in W$ 是可能世界，$\varphi$ 是模态公式。真值关系 $\models$ 递归定义如下：

1. **原子公式**：$\mathcal{M}, w \models p$ 当且仅当 $w \in V(p)$
2. **否定**：$\mathcal{M}, w \models \neg \varphi$ 当且仅当 $\mathcal{M}, w \not\models \varphi$
3. **合取**：$\mathcal{M}, w \models \varphi \land \psi$ 当且仅当 $\mathcal{M}, w \models \varphi$ 且 $\mathcal{M}, w \models \psi$
4. **析取**：$\mathcal{M}, w \models \varphi \lor \psi$ 当且仅当 $\mathcal{M}, w \models \varphi$ 或 $\mathcal{M}, w \models \psi$
5. **蕴含**：$\mathcal{M}, w \models \varphi \to \psi$ 当且仅当 $\mathcal{M}, w \not\models \varphi$ 或 $\mathcal{M}, w \models \psi$
6. **必然**：$\mathcal{M}, w \models \Box \varphi$ 当且仅当对所有 $v \in W$，如果 $wRv$ 则 $\mathcal{M}, v \models \varphi$
7. **可能**：$\mathcal{M}, w \models \Diamond \varphi$ 当且仅当存在 $v \in W$ 使得 $wRv$ 且 $\mathcal{M}, v \models \varphi$

### 有效性

- **模型有效性**：公式 $\varphi$ 在模型 $\mathcal{M}$ 中有效，记作 $\mathcal{M} \models \varphi$，当且仅当对所有 $w \in W$，$\mathcal{M}, w \models \varphi$
- **框架有效性**：公式 $\varphi$ 在框架 $\mathcal{F}$ 中有效，记作 $\mathcal{F} \models \varphi$，当且仅当对所有赋值函数 $V$，$(W, R, V) \models \varphi$

## Haskell实现

### Kripke模型数据类型

```haskell
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

-- 可能世界类型
type World = Int

-- 可达关系
type AccessibilityRelation = [(World, World)]

-- 命题变量
type Proposition = String

-- 赋值函数
type Valuation = [(Proposition, [World])]

-- Kripke框架
data KripkeFrame = KripkeFrame {
    worlds :: [World],
    accessibility :: AccessibilityRelation
} deriving (Eq, Show)

-- Kripke模型
data KripkeModel = KripkeModel {
    frame :: KripkeFrame,
    valuation :: Valuation
} deriving (Eq, Show)

-- 模态公式
data ModalFormula = 
    Prop Proposition                    -- 原子命题
    | Neg ModalFormula                  -- 否定
    | Conj ModalFormula ModalFormula    -- 合取
    | Disj ModalFormula ModalFormula    -- 析取
    | Impl ModalFormula ModalFormula    -- 蕴含
    | Box ModalFormula                  -- 必然
    | Diamond ModalFormula              -- 可能
    deriving (Eq, Show)

-- 真值关系
satisfies :: KripkeModel -> World -> ModalFormula -> Bool
satisfies model world formula = 
    case formula of
        Prop p -> world `elem` getValuation model p
        Neg phi -> not (satisfies model world phi)
        Conj phi psi -> satisfies model world phi && satisfies model world psi
        Disj phi psi -> satisfies model world phi || satisfies model world psi
        Impl phi psi -> not (satisfies model world phi) || satisfies model world psi
        Box phi -> all (\w -> satisfies model w phi) (accessibleWorlds model world)
        Diamond phi -> any (\w -> satisfies model w phi) (accessibleWorlds model world)

-- 获取可达世界
accessibleWorlds :: KripkeModel -> World -> [World]
accessibleWorlds model world = 
    [w | (w1, w2) <- accessibility (frame model), w1 == world, w2 == w]

-- 获取赋值
getValuation :: KripkeModel -> Proposition -> [World]
getValuation model prop = 
    case lookup prop (valuation model) of
        Just worlds -> worlds
        Nothing -> []

-- 模型有效性
modelValid :: KripkeModel -> ModalFormula -> Bool
modelValid model formula = 
    all (\world -> satisfies model world formula) (worlds (frame model))

-- 框架有效性
frameValid :: KripkeFrame -> ModalFormula -> Bool
frameValid frame formula = 
    let allValuations = generateAllValuations frame
    in all (\valuation -> 
        let model = KripkeModel frame valuation
        in modelValid model formula
    ) allValuations
```

### 框架性质

```haskell
-- 框架性质检查
class FrameProperty where
    -- 自反性
    isReflexive :: KripkeFrame -> Bool
    isReflexive frame = 
        all (\w -> (w, w) `elem` accessibility frame) (worlds frame)
    
    -- 对称性
    isSymmetric :: KripkeFrame -> Bool
    isSymmetric frame = 
        all (\(w1, w2) -> (w2, w1) `elem` accessibility frame) (accessibility frame)
    
    -- 传递性
    isTransitive :: KripkeFrame -> Bool
    isTransitive frame = 
        all (\(w1, w2) -> 
            all (\(w2', w3) -> 
                w2 == w2' ==> (w1, w3) `elem` accessibility frame
            ) (accessibility frame)
        ) (accessibility frame)
    
    -- 欧几里得性
    isEuclidean :: KripkeFrame -> Bool
    isEuclidean frame = 
        all (\(w1, w2) -> 
            all (\(w1', w3) -> 
                w1 == w1' && (w1, w2) `elem` accessibility frame && 
                (w1, w3) `elem` accessibility frame ==>
                (w2, w3) `elem` accessibility frame
            ) (accessibility frame)
        ) (accessibility frame)
    
    -- 序列性
    isSerial :: KripkeFrame -> Bool
    isSerial frame = 
        all (\w -> any (\(w1, w2) -> w1 == w) (accessibility frame)) (worlds frame)

-- 逻辑系统对应的框架性质
data LogicSystem = 
    K    -- 基本模态逻辑
    | T   -- 自反
    | B   -- 自反对称
    | S4  -- 自反传递
    | S5  -- 自反对称传递
    deriving (Eq, Show)

-- 检查框架是否满足逻辑系统的性质
satisfiesLogicSystem :: KripkeFrame -> LogicSystem -> Bool
satisfiesLogicSystem frame K = True
satisfiesLogicSystem frame T = isReflexive frame
satisfiesLogicSystem frame B = isReflexive frame && isSymmetric frame
satisfiesLogicSystem frame S4 = isReflexive frame && isTransitive frame
satisfiesLogicSystem frame S5 = isReflexive frame && isSymmetric frame && isTransitive frame
```

### 模型构建

```haskell
-- 构建简单模型
buildSimpleModel :: [World] -> AccessibilityRelation -> Valuation -> KripkeModel
buildSimpleModel ws rel val = 
    KripkeModel (KripkeFrame ws rel) val

-- 构建自反模型
buildReflexiveModel :: [World] -> AccessibilityRelation -> Valuation -> KripkeModel
buildReflexiveModel ws rel val = 
    let reflexiveRel = rel ++ [(w, w) | w <- ws]
    in KripkeModel (KripkeFrame ws reflexiveRel) val

-- 构建S5模型（等价关系）
buildS5Model :: [World] -> Valuation -> KripkeModel
buildS5Model ws val = 
    let -- 完全关系（所有世界之间都可达）
        completeRel = [(w1, w2) | w1 <- ws, w2 <- ws]
    in KripkeModel (KripkeFrame ws completeRel) val

-- 构建树状模型
buildTreeModel :: [World] -> [(World, World)] -> Valuation -> KripkeModel
buildTreeModel ws edges val = 
    KripkeModel (KripkeFrame ws edges) val

-- 生成所有可能的赋值
generateAllValuations :: KripkeFrame -> [Valuation]
generateAllValuations frame = 
    let props = ["p", "q", "r"]  -- 假设的命题变量
        worldSubsets = powerSet (worlds frame)
        valuations = sequence [worldSubsets | _ <- props]
    in zipWith (\valuation props -> zip props valuation) valuations (repeat props)

-- 幂集
powerSet :: [a] -> [[a]]
powerSet [] = [[]]
powerSet (x:xs) = 
    let rest = powerSet xs
    in rest ++ map (x:) rest
```

### 逻辑推理

```haskell
-- 逻辑推理规则
data InferenceRule = 
    ModusPonens
    | Necessitation
    | Distribution
    | K
    | T
    | B
    | S4
    | S5
    deriving (Eq, Show)

-- 应用推理规则
applyInferenceRule :: InferenceRule -> [ModalFormula] -> Maybe ModalFormula
applyInferenceRule rule premises = 
    case rule of
        ModusPonens -> 
            case premises of
                [Impl phi psi, phi'] | phi == phi' -> Just psi
                _ -> Nothing
        
        Necessitation -> 
            case premises of
                [phi] | isTautology phi -> Just (Box phi)
                _ -> Nothing
        
        Distribution -> 
            case premises of
                [Box (Impl phi psi)] -> Just (Impl (Box phi) (Box psi))
                _ -> Nothing
        
        K -> 
            case premises of
                [Box (Impl phi psi), Box phi'] | phi == phi' -> Just (Box psi)
                _ -> Nothing
        
        T -> 
            case premises of
                [Box phi] -> Just phi
                _ -> Nothing
        
        B -> 
            case premises of
                [phi] -> Just (Box (Diamond phi))
                _ -> Nothing
        
        S4 -> 
            case premises of
                [Box phi] -> Just (Box (Box phi))
                _ -> Nothing
        
        S5 -> 
            case premises of
                [Diamond phi] -> Just (Box (Diamond phi))
                _ -> Nothing

-- 检查是否为重言式
isTautology :: ModalFormula -> Bool
isTautology formula = 
    -- 简化实现：检查在S5模型中是否有效
    let s5Frame = KripkeFrame [1, 2] [(1, 1), (1, 2), (2, 1), (2, 2)]
        allValuations = generateAllValuations s5Frame
    in all (\valuation -> 
        let model = KripkeModel s5Frame valuation
        in modelValid model formula
    ) allValuations

-- 证明系统
data Proof = 
    Axiom ModalFormula
    | Rule InferenceRule [Proof] ModalFormula
    deriving (Eq, Show)

-- 检查证明的有效性
isValidProof :: Proof -> Bool
isValidProof (Axiom formula) = isTautology formula
isValidProof (Rule rule proofs conclusion) = 
    let premises = map getConclusion proofs
        maybeConclusion = applyInferenceRule rule premises
    in maybeConclusion == Just conclusion

-- 获取证明的结论
getConclusion :: Proof -> ModalFormula
getConclusion (Axiom formula) = formula
getConclusion (Rule _ _ conclusion) = conclusion
```

## 重要定理与证明

### 定理1：K公理的有效性

**定理**：公式 $\Box(\varphi \to \psi) \to (\Box\varphi \to \Box\psi)$ 在所有Kripke框架中有效。

**证明**：
1. 设 $\mathcal{M} = (W, R, V)$ 是任意Kripke模型，$w \in W$ 是任意可能世界
2. 假设 $\mathcal{M}, w \models \Box(\varphi \to \psi)$ 且 $\mathcal{M}, w \models \Box\varphi$
3. 需要证明 $\mathcal{M}, w \models \Box\psi$
4. 设 $v$ 是任意满足 $wRv$ 的世界
5. 由 $\mathcal{M}, w \models \Box(\varphi \to \psi)$ 得 $\mathcal{M}, v \models \varphi \to \psi$
6. 由 $\mathcal{M}, w \models \Box\varphi$ 得 $\mathcal{M}, v \models \varphi$
7. 由 $\mathcal{M}, v \models \varphi \to \psi$ 和 $\mathcal{M}, v \models \varphi$ 得 $\mathcal{M}, v \models \psi$
8. 因此对所有满足 $wRv$ 的世界 $v$，都有 $\mathcal{M}, v \models \psi$
9. 所以 $\mathcal{M}, w \models \Box\psi$

### 定理2：T公理与自反性

**定理**：公式 $\Box\varphi \to \varphi$ 在Kripke框架中有效当且仅当该框架是自反的。

**证明**：
- **必要性**：假设 $\Box\varphi \to \varphi$ 在框架 $\mathcal{F} = (W, R)$ 中有效
  - 设 $w \in W$ 是任意世界
  - 构造赋值 $V$ 使得 $V(p) = W \setminus \{w\}$
  - 则 $\mathcal{M} = (W, R, V), w \models \Box p$（因为所有可达世界都满足 $p$）
  - 由 $\Box p \to p$ 有效得 $\mathcal{M}, w \models p$
  - 因此 $w \in V(p) = W \setminus \{w\}$，矛盾
  - 所以 $w \in V(p)$，即 $wRw$，框架是自反的

- **充分性**：假设框架 $\mathcal{F} = (W, R)$ 是自反的
  - 设 $\mathcal{M} = (W, R, V)$ 是任意模型，$w \in W$ 是任意世界
  - 假设 $\mathcal{M}, w \models \Box\varphi$
  - 由自反性得 $wRw$，所以 $\mathcal{M}, w \models \varphi$
  - 因此 $\mathcal{M}, w \models \Box\varphi \to \varphi$

### 定理3：S5的特征

**定理**：S5逻辑（等价关系框架）中，$\Diamond\varphi \leftrightarrow \neg\Box\neg\varphi$ 是有效的。

**证明**：
1. 设 $\mathcal{M} = (W, R, V)$ 是S5模型，$w \in W$ 是任意世界
2. 证明 $\mathcal{M}, w \models \Diamond\varphi \to \neg\Box\neg\varphi$：
   - 假设 $\mathcal{M}, w \models \Diamond\varphi$
   - 则存在 $v$ 使得 $wRv$ 且 $\mathcal{M}, v \models \varphi$
   - 假设 $\mathcal{M}, w \models \Box\neg\varphi$
   - 则对所有 $u$ 满足 $wRu$，有 $\mathcal{M}, u \models \neg\varphi$
   - 特别地，$\mathcal{M}, v \models \neg\varphi$，矛盾
   - 所以 $\mathcal{M}, w \models \neg\Box\neg\varphi$

3. 证明 $\mathcal{M}, w \models \neg\Box\neg\varphi \to \Diamond\varphi$：
   - 假设 $\mathcal{M}, w \models \neg\Box\neg\varphi$
   - 则 $\mathcal{M}, w \not\models \Box\neg\varphi$
   - 所以存在 $v$ 使得 $wRv$ 且 $\mathcal{M}, v \not\models \neg\varphi$
   - 即 $\mathcal{M}, v \models \varphi$
   - 因此 $\mathcal{M}, w \models \Diamond\varphi$

## 应用示例

### 示例1：知识逻辑

```haskell
-- 知识逻辑模型
data KnowledgeModel = KnowledgeModel {
    agents :: [Agent],
    worlds :: [World],
    accessibility :: Agent -> World -> [World],
    valuation :: Valuation
} deriving (Eq, Show)

type Agent = String

-- 知识算子
data KnowledgeFormula = 
    KProp Agent Proposition
    | KNeg Agent KnowledgeFormula
    | KConj KnowledgeFormula KnowledgeFormula
    | KDisj KnowledgeFormula KnowledgeFormula
    | KImpl KnowledgeFormula KnowledgeFormula
    | KBox Agent KnowledgeFormula
    | KDiamond Agent KnowledgeFormula
    deriving (Eq, Show)

-- 知识语义
satisfiesKnowledge :: KnowledgeModel -> World -> KnowledgeFormula -> Bool
satisfiesKnowledge model world formula = 
    case formula of
        KProp agent prop -> world `elem` getValuation model prop
        KNeg agent phi -> not (satisfiesKnowledge model world phi)
        KConj phi psi -> satisfiesKnowledge model world phi && satisfiesKnowledge model world psi
        KDisj phi psi -> satisfiesKnowledge model world phi || satisfiesKnowledge model world psi
        KImpl phi psi -> not (satisfiesKnowledge model world phi) || satisfiesKnowledge model world psi
        KBox agent phi -> all (\w -> satisfiesKnowledge model w phi) (accessibleWorlds model agent world)
        KDiamond agent phi -> any (\w -> satisfiesKnowledge model w phi) (accessibleWorlds model agent world)

-- 获取智能体的可达世界
accessibleWorlds :: KnowledgeModel -> Agent -> World -> [World]
accessibleWorlds model agent world = accessibility model agent world

-- 构建公共知识模型
buildCommonKnowledgeModel :: [Agent] -> [World] -> Valuation -> KnowledgeModel
buildCommonKnowledgeModel agents worlds val = 
    let -- 公共知识：所有智能体都有相同的可达关系
        commonAccessibility agent world = worlds
    in KnowledgeModel agents worlds commonAccessibility val
```

### 示例2：时态逻辑

```haskell
-- 时态逻辑模型
data TemporalModel = TemporalModel {
    timePoints :: [TimePoint],
    temporalRelation :: TimePoint -> [TimePoint],
    valuation :: Valuation
} deriving (Eq, Show)

type TimePoint = Int

-- 时态公式
data TemporalFormula = 
    TProp Proposition
    | TNeg TemporalFormula
    | TConj TemporalFormula TemporalFormula
    | TDisj TemporalFormula TemporalFormula
    | TImpl TemporalFormula TemporalFormula
    | G TemporalFormula      -- 全局性（总是）
    | F TemporalFormula      -- 未来性（最终）
    | X TemporalFormula      -- 下一个
    | U TemporalFormula TemporalFormula  -- 直到
    deriving (Eq, Show)

-- 时态语义
satisfiesTemporal :: TemporalModel -> TimePoint -> TemporalFormula -> Bool
satisfiesTemporal model time formula = 
    case formula of
        TProp prop -> time `elem` getValuation model prop
        TNeg phi -> not (satisfiesTemporal model time phi)
        TConj phi psi -> satisfiesTemporal model time phi && satisfiesTemporal model time psi
        TDisj phi psi -> satisfiesTemporal model time phi || satisfiesTemporal model time psi
        TImpl phi psi -> not (satisfiesTemporal model time phi) || satisfiesTemporal model time psi
        G phi -> all (\t -> satisfiesTemporal model t phi) (temporalRelation model time)
        F phi -> any (\t -> satisfiesTemporal model t phi) (temporalRelation model time)
        X phi -> 
            let nextTimes = [t | t <- temporalRelation model time, t > time]
            in case nextTimes of
                [] -> False
                (next:_) -> satisfiesTemporal model next phi
        U phi psi -> 
            let futureTimes = [t | t <- temporalRelation model time, t >= time]
            in any (\t -> satisfiesTemporal model t psi && 
                         all (\t' -> satisfiesTemporal model t' phi) 
                             [t' | t' <- futureTimes, t' >= time, t' < t]) futureTimes

-- 构建线性时间模型
buildLinearTimeModel :: [TimePoint] -> Valuation -> TemporalModel
buildLinearTimeModel times val = 
    let linearRelation time = [t | t <- times, t >= time]
    in TemporalModel times linearRelation val
```

### 示例3：信念逻辑

```haskell
-- 信念逻辑模型
data BeliefModel = BeliefModel {
    agents :: [Agent],
    worlds :: [World],
    plausibility :: Agent -> World -> World -> Bool,  -- 更可信关系
    valuation :: Valuation
} deriving (Eq, Show)

-- 信念公式
data BeliefFormula = 
    BProp Agent Proposition
    | BNeg Agent BeliefFormula
    | BConj BeliefFormula BeliefFormula
    | BDisj BeliefFormula BeliefFormula
    | BImpl BeliefFormula BeliefFormula
    | B Agent BeliefFormula      -- 信念
    | S Agent BeliefFormula      -- 强信念
    deriving (Eq, Show)

-- 信念语义
satisfiesBelief :: BeliefModel -> World -> BeliefFormula -> Bool
satisfiesBelief model world formula = 
    case formula of
        BProp agent prop -> world `elem` getValuation model prop
        BNeg agent phi -> not (satisfiesBelief model world phi)
        BConj phi psi -> satisfiesBelief model world phi && satisfiesBelief model world psi
        BDisj phi psi -> satisfiesBelief model world phi || satisfiesBelief model world psi
        BImpl phi psi -> not (satisfiesBelief model world phi) || satisfiesBelief model world psi
        B agent phi -> 
            let mostPlausible = mostPlausibleWorlds model agent world
            in all (\w -> satisfiesBelief model w phi) mostPlausible
        S agent phi -> 
            let plausible = plausibleWorlds model agent world
            in all (\w -> satisfiesBelief model w phi) plausible

-- 最可信世界
mostPlausibleWorlds :: BeliefModel -> Agent -> World -> [World]
mostPlausibleWorlds model agent world = 
    let allWorlds = worlds model
        plausible = [w | w <- allWorlds, plausibility model agent world w]
        mostPlausible = [w | w <- plausible, 
                            not (any (\w' -> plausibility model agent w w') plausible)]
    in mostPlausible

-- 可信世界
plausibleWorlds :: BeliefModel -> Agent -> World -> [World]
plausibleWorlds model agent world = 
    [w | w <- worlds model, plausibility model agent world w]
```

## 总结

Kripke语义理论为模态逻辑提供了完整且直观的语义基础：

1. **严格的数学定义**：基于可能世界和可达关系的语义结构
2. **完整的Haskell实现**：包含模型构建、真值计算、推理规则等
3. **重要的理论结果**：K公理有效性、T公理与自反性、S5特征等
4. **实际应用示例**：知识逻辑、时态逻辑、信念逻辑等

这个理论框架为后续的模态逻辑系统、模型检测、形式化验证等提供了必要的理论基础。

---

**相关文档**：
- [模态逻辑基础](./01-Basic-Concepts.md)
- [线性时态逻辑](../07-Temporal-Logic/01-Linear-Temporal-Logic.md)
- [形式化验证理论](../04-Formal-Methods/01-Model-Checking.md) 