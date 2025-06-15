# 模态逻辑基础 (Modal Logic Basics)

## 概述

模态逻辑是研究必然性和可能性等模态概念的逻辑分支，是形式逻辑的重要扩展。本文档从形式化角度介绍模态逻辑的基本概念、语义和推理规则。

## 形式化定义

### 基本概念

#### 1. 模态语言

模态语言 $\mathcal{L}$ 由以下部分组成：

- 命题变元集合 $P = \{p, q, r, ...\}$
- 逻辑连接词：$\neg, \land, \lor, \rightarrow, \leftrightarrow$
- 模态算子：$\Box$（必然），$\Diamond$（可能）
- 辅助符号：$(, )$

#### 2. 模态公式

模态公式的递归定义：

1. 如果 $p \in P$，则 $p$ 是模态公式
2. 如果 $\phi$ 是模态公式，则 $\neg\phi$ 和 $\Box\phi$ 是模态公式
3. 如果 $\phi$ 和 $\psi$ 是模态公式，则 $(\phi \land \psi)$ 是模态公式
4. 其他连接词通过定义引入：$\Diamond\phi \equiv \neg\Box\neg\phi$

#### 3. Kripke模型

Kripke模型是一个三元组 $\mathcal{M} = (W, R, V)$：

- $W$ 是可能世界集合
- $R \subseteq W \times W$ 是可达关系
- $V: P \rightarrow \mathcal{P}(W)$ 是赋值函数

#### 4. 真值定义

对于Kripke模型 $\mathcal{M} = (W, R, V)$ 和世界 $w \in W$：

$$\mathcal{M}, w \models p \iff w \in V(p)$$
$$\mathcal{M}, w \models \neg\phi \iff \mathcal{M}, w \not\models \phi$$
$$\mathcal{M}, w \models \phi \land \psi \iff \mathcal{M}, w \models \phi \text{ and } \mathcal{M}, w \models \psi$$
$$\mathcal{M}, w \models \Box\phi \iff \forall v \in W: (w, v) \in R \implies \mathcal{M}, v \models \phi$$
$$\mathcal{M}, w \models \Diamond\phi \iff \exists v \in W: (w, v) \in R \text{ and } \mathcal{M}, v \models \phi$$

## Haskell实现

```haskell
-- 模态逻辑基础的形式化实现
module ModalLogic where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)

-- 命题变元
type Proposition = String

-- 模态公式
data ModalFormula = 
    Prop Proposition
  | Not ModalFormula
  | And ModalFormula ModalFormula
  | Or ModalFormula ModalFormula
  | Implies ModalFormula ModalFormula
  | Iff ModalFormula ModalFormula
  | Necessarily ModalFormula
  | Possibly ModalFormula
  deriving (Eq, Ord, Show)

-- 可能世界
type World = String

-- 可达关系
type AccessibilityRelation = Set (World, World)

-- 赋值函数
type Valuation = Map Proposition (Set World)

-- Kripke模型
data KripkeModel = KripkeModel
  { worlds :: Set World
  , accessibility :: AccessibilityRelation
  , valuation :: Valuation
  } deriving Show

-- 真值关系
satisfies :: KripkeModel -> World -> ModalFormula -> Bool
satisfies model world formula =
  case formula of
    Prop p -> 
      case Map.lookup p (valuation model) of
        Just worlds -> Set.member world worlds
        Nothing -> False
        
    Not phi -> 
      not (satisfies model world phi)
      
    And phi psi -> 
      satisfies model world phi && satisfies model world psi
      
    Or phi psi -> 
      satisfies model world phi || satisfies model world psi
      
    Implies phi psi -> 
      not (satisfies model world phi) || satisfies model world psi
      
    Iff phi psi -> 
      satisfies model world phi == satisfies model world psi
      
    Necessarily phi -> 
      all (\w -> satisfies model w phi) (accessibleWorlds model world)
      
    Possibly phi -> 
      any (\w -> satisfies model w phi) (accessibleWorlds model world)

-- 可达世界
accessibleWorlds :: KripkeModel -> World -> Set World
accessibleWorlds model world =
  Set.fromList [w | (w1, w2) <- Set.toList (accessibility model), w1 == world, w2 == w]

-- 模态公式等价
equivalent :: KripkeModel -> ModalFormula -> ModalFormula -> Bool
equivalent model phi psi =
  all (\world -> satisfies model world phi == satisfies model world psi) (worlds model)

-- 模态公式有效性
valid :: KripkeModel -> ModalFormula -> Bool
valid model phi =
  all (\world -> satisfies model world phi) (worlds model)

-- 模态公式可满足性
satisfiable :: KripkeModel -> ModalFormula -> Bool
satisfiable model phi =
  any (\world -> satisfies model world phi) (worlds model)

-- 模态公式矛盾
contradictory :: KripkeModel -> ModalFormula -> Bool
contradictory model phi =
  not (satisfiable model phi)

-- 模态公式重言式
tautology :: KripkeModel -> ModalFormula -> Bool
tautology model phi =
  valid model phi

-- 模态逻辑公理系统

-- K公理：□(φ→ψ) → (□φ→□ψ)
kAxiom :: ModalFormula -> ModalFormula -> ModalFormula
kAxiom phi psi = 
  Implies 
    (Necessarily (Implies phi psi))
    (Implies (Necessarily phi) (Necessarily psi))

-- T公理：□φ → φ
tAxiom :: ModalFormula -> ModalFormula
tAxiom phi = Implies (Necessarily phi) phi

-- 4公理：□φ → □□φ
fourAxiom :: ModalFormula -> ModalFormula
fourAxiom phi = Implies (Necessarily phi) (Necessarily (Necessarily phi))

-- 5公理：◇φ → □◇φ
fiveAxiom :: ModalFormula -> ModalFormula
fiveAxiom phi = Implies (Possibly phi) (Necessarily (Possibly phi))

-- B公理：φ → □◇φ
bAxiom :: ModalFormula -> ModalFormula
bAxiom phi = Implies phi (Necessarily (Possibly phi))

-- D公理：□φ → ◇φ
dAxiom :: ModalFormula -> ModalFormula
dAxiom phi = Implies (Necessarily phi) (Possibly phi)

-- 模态逻辑推理规则

-- 必然化规则：如果 ⊢ φ，则 ⊢ □φ
necessitation :: ModalFormula -> ModalFormula
necessitation phi = Necessarily phi

-- 单调性规则：如果 φ → ψ，则 □φ → □ψ
monotonicity :: ModalFormula -> ModalFormula -> ModalFormula
monotonicity phi psi = 
  Implies (Implies phi psi) (Implies (Necessarily phi) (Necessarily psi))

-- 模态逻辑系统

-- K系统（基本模态逻辑）
kSystem :: [ModalFormula]
kSystem = []

-- T系统（自反模态逻辑）
tSystem :: [ModalFormula]
tSystem = [tAxiom (Prop "p")]

-- S4系统（自反传递模态逻辑）
s4System :: [ModalFormula]
s4System = [tAxiom (Prop "p"), fourAxiom (Prop "p")]

-- S5系统（等价关系模态逻辑）
s5System :: [ModalFormula]
s5System = [tAxiom (Prop "p"), fiveAxiom (Prop "p")]

-- 模态逻辑语义

-- 自反关系
reflexive :: AccessibilityRelation -> Bool
reflexive relation =
  all (\world -> Set.member (world, world) relation) (Set.fromList [w | (w, _) <- Set.toList relation])

-- 传递关系
transitive :: AccessibilityRelation -> Bool
transitive relation =
  all (\(w1, w2) -> 
    all (\(w3, w4) -> 
      if w2 == w3 then Set.member (w1, w4) relation else True
    ) (Set.toList relation)
  ) (Set.toList relation)

-- 对称关系
symmetric :: AccessibilityRelation -> Bool
symmetric relation =
  all (\(w1, w2) -> Set.member (w2, w1) relation) (Set.toList relation)

-- 等价关系
equivalence :: AccessibilityRelation -> Bool
equivalence relation =
  reflexive relation && transitive relation && symmetric relation

-- 模态逻辑模型构建

-- 构建自反模型
reflexiveModel :: Set World -> Valuation -> KripkeModel
reflexiveModel worlds val =
  let reflexiveRelation = Set.fromList [(w, w) | w <- Set.toList worlds]
  in KripkeModel worlds reflexiveRelation val

-- 构建传递模型
transitiveModel :: AccessibilityRelation -> KripkeModel -> KripkeModel
transitiveModel relation model =
  let transitiveClosure = computeTransitiveClosure relation
  in model { accessibility = transitiveClosure }

-- 计算传递闭包
computeTransitiveClosure :: AccessibilityRelation -> AccessibilityRelation
computeTransitiveClosure relation =
  let pairs = Set.toList relation
      worlds = Set.fromList [w | (w1, w2) <- pairs, w <- [w1, w2]]
      closure = foldl addTransitivePairs relation worlds
  in closure
  where
    addTransitivePairs acc world =
      let direct = Set.fromList [w2 | (w1, w2) <- Set.toList acc, w1 == world]
          indirect = Set.fromList [w3 | (w1, w2) <- Set.toList acc, w2 == world, 
                                    (w2, w3) <- Set.toList acc]
      in Set.union acc (Set.fromList [(world, w) | w <- Set.toList indirect])

-- 构建对称模型
symmetricModel :: AccessibilityRelation -> KripkeModel -> KripkeModel
symmetricModel relation model =
  let symmetricRelation = Set.union relation (Set.fromList [(w2, w1) | (w1, w2) <- Set.toList relation])
  in model { accessibility = symmetricRelation }

-- 模态逻辑应用

-- 知识逻辑
knowledgeLogic :: ModalFormula -> ModalFormula
knowledgeLogic phi = Necessarily phi  -- Kφ 表示"知道φ"

-- 信念逻辑
beliefLogic :: ModalFormula -> ModalFormula
beliefLogic phi = Necessarily phi  -- Bφ 表示"相信φ"

-- 时间逻辑
temporalLogic :: ModalFormula -> ModalFormula
temporalLogic phi = Necessarily phi  -- Gφ 表示"总是φ"

-- 道义逻辑
deonticLogic :: ModalFormula -> ModalFormula
deonticLogic phi = Necessarily phi  -- Oφ 表示"应该φ"

-- 模态逻辑定理证明

-- 模态逻辑定理
modalTheorems :: [ModalFormula]
modalTheorems = 
  [ -- 双重否定
    Iff (Not (Not (Prop "p"))) (Prop "p"),
    
    -- 德摩根律
    Iff (Not (And (Prop "p") (Prop "q"))) (Or (Not (Prop "p")) (Not (Prop "q"))),
    Iff (Not (Or (Prop "p") (Prop "q"))) (And (Not (Prop "p")) (Not (Prop "q"))),
    
    -- 模态对偶性
    Iff (Necessarily (Prop "p")) (Not (Possibly (Not (Prop "p")))),
    Iff (Possibly (Prop "p")) (Not (Necessarily (Not (Prop "p")))),
    
    -- 模态分配律
    Implies (Necessarily (And (Prop "p") (Prop "q"))) 
            (And (Necessarily (Prop "p")) (Necessarily (Prop "q"))),
    
    -- 模态单调性
    Implies (And (Necessarily (Prop "p")) (Necessarily (Implies (Prop "p") (Prop "q"))))
            (Necessarily (Prop "q"))
  ]

-- 验证模态定理
verifyModalTheorems :: KripkeModel -> [Bool]
verifyModalTheorems model = map (valid model) modalTheorems
```

## 形式化证明

### 定理1：K公理的有效性

**定理**：K公理 $\Box(\phi \rightarrow \psi) \rightarrow (\Box\phi \rightarrow \Box\psi)$ 在所有Kripke模型中有效。

**证明**：

1. 设 $\mathcal{M} = (W, R, V)$ 是任意Kripke模型，$w \in W$
2. 假设 $\mathcal{M}, w \models \Box(\phi \rightarrow \psi)$
3. 对于任意 $v$ 使得 $(w, v) \in R$，有 $\mathcal{M}, v \models \phi \rightarrow \psi$
4. 假设 $\mathcal{M}, w \models \Box\phi$
5. 对于任意 $v$ 使得 $(w, v) \in R$，有 $\mathcal{M}, v \models \phi$
6. 因此 $\mathcal{M}, v \models \psi$
7. 所以 $\mathcal{M}, w \models \Box\psi$
8. 因此 $\mathcal{M}, w \models \Box(\phi \rightarrow \psi) \rightarrow (\Box\phi \rightarrow \Box\psi)$

### 定理2：T公理与自反性

**定理**：T公理 $\Box\phi \rightarrow \phi$ 在Kripke模型中有效当且仅当可达关系是自反的。

**证明**：

1. 必要性：假设T公理有效，则对于任意世界 $w$，如果 $\mathcal{M}, w \models \Box\phi$，则 $\mathcal{M}, w \models \phi$
2. 这意味着 $w$ 必须可达自身，即 $(w, w) \in R$
3. 充分性：假设 $R$ 是自反的，则对于任意世界 $w$，$(w, w) \in R$
4. 如果 $\mathcal{M}, w \models \Box\phi$，则 $\mathcal{M}, w \models \phi$
5. 因此 $\mathcal{M}, w \models \Box\phi \rightarrow \phi$

## 应用示例

### 知识逻辑系统

```haskell
-- 知识逻辑系统
knowledgeSystem :: KripkeModel
knowledgeSystem = KripkeModel
  { worlds = Set.fromList ["w1", "w2", "w3"]
  , accessibility = Set.fromList [("w1", "w1"), ("w2", "w2"), ("w3", "w3")]
  , valuation = Map.fromList [("p", Set.fromList ["w1", "w2"]), ("q", Set.fromList ["w1"])]
  }

-- 知识公式
knowledgeFormula :: ModalFormula
knowledgeFormula = knowledgeLogic (Prop "p")

-- 验证知识
verifyKnowledge :: Bool
verifyKnowledge = valid knowledgeSystem knowledgeFormula
```

### 时间逻辑系统

```haskell
-- 时间逻辑系统
temporalSystem :: KripkeModel
temporalSystem = KripkeModel
  { worlds = Set.fromList ["t1", "t2", "t3", "t4"]
  , accessibility = Set.fromList [("t1", "t2"), ("t2", "t3"), ("t3", "t4"), 
                                 ("t1", "t1"), ("t2", "t2"), ("t3", "t3"), ("t4", "t4")]
  , valuation = Map.fromList [("p", Set.fromList ["t1", "t2", "t3"]), ("q", Set.fromList ["t2", "t4"])]
  }

-- 时间公式
temporalFormula :: ModalFormula
temporalFormula = temporalLogic (Prop "p")

-- 验证时间性质
verifyTemporal :: Bool
verifyTemporal = valid temporalSystem temporalFormula
```

## 与其他理论的关联

- **与经典逻辑的关系**：模态逻辑是经典逻辑的扩展
- **与集合论的关系**：Kripke模型基于集合论构建
- **与代数结构的关系**：模态逻辑可以代数化
- **与计算机科学的关系**：模态逻辑用于程序验证和AI推理

## 总结

模态逻辑基础通过形式化方法建立了严格的模态推理体系，为知识表示、时间推理和道义推理提供了理论基础。通过Haskell的实现，我们可以验证模态公式的有效性，并应用于各种推理系统。

## 相关链接

- [经典逻辑基础](../01-Classical-Logic/01-Classical-Logic-Basics.md)
- [集合论基础](../../01-Mathematics/01-Set-Theory/01-Set-Theory-Basics.md)
- [时态逻辑理论](../../03-Theory/07-Temporal-Logic/README.md)
- [形式化验证理论](../../03-Theory/04-Formal-Methods/README.md)
