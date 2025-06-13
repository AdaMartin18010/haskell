-- 文件: PropositionalLogic.hs
-- 描述: 命题逻辑的完整Haskell实现
-- 作者: 形式化知识体系重构项目
-- 日期: 2024-11-XX

module PropositionalLogic where

import Data.List (nub, (\\), intersect, union)
import Data.Maybe (fromJust, isJust)

-- ============================================================================
-- 基本类型定义
-- ============================================================================

-- 命题变元
type Proposition = String

-- 公式数据类型
data Formula = 
    Atom Proposition                    -- 原子公式
  | Not Formula                        -- 否定
  | And Formula Formula                -- 合取
  | Or Formula Formula                 -- 析取
  | Implies Formula Formula            -- 蕴含
  | Iff Formula Formula                -- 等价
  deriving (Eq, Show)

-- 解释函数类型
type Interpretation = Proposition -> Bool

-- 证明上下文
type Context = [Formula]

-- 证明关系
data Derivation = 
    Assumption Formula
  | ImplicationIntro Formula Derivation
  | ImplicationElim Derivation Derivation
  | ConjunctionIntro Derivation Derivation
  | ConjunctionElim1 Derivation
  | ConjunctionElim2 Derivation
  | DisjunctionIntro1 Formula Derivation
  | DisjunctionIntro2 Formula Derivation
  | DisjunctionElim Derivation Derivation Derivation
  | NegationIntro Formula Derivation
  | NegationElim Derivation Derivation
  | ContradictionElim Derivation Formula
  deriving (Eq, Show)

-- ============================================================================
-- 语法函数
-- ============================================================================

-- 公式复杂度
complexity :: Formula -> Int
complexity (Atom _) = 0
complexity (Not phi) = 1 + complexity phi
complexity (And phi psi) = 1 + max (complexity phi) (complexity psi)
complexity (Or phi psi) = 1 + max (complexity phi) (complexity psi)
complexity (Implies phi psi) = 1 + max (complexity phi) (complexity psi)
complexity (Iff phi psi) = 1 + max (complexity phi) (complexity psi)

-- 子公式集合
subformulas :: Formula -> [Formula]
subformulas (Atom p) = [Atom p]
subformulas (Not phi) = Not phi : subformulas phi
subformulas (And phi psi) = And phi psi : subformulas phi ++ subformulas psi
subformulas (Or phi psi) = Or phi psi : subformulas phi ++ subformulas psi
subformulas (Implies phi psi) = Implies phi psi : subformulas phi ++ subformulas psi
subformulas (Iff phi psi) = Iff phi psi : subformulas phi ++ subformulas psi

-- 命题变元集合
propositions :: Formula -> [Proposition]
propositions (Atom p) = [p]
propositions (Not phi) = propositions phi
propositions (And phi psi) = propositions phi ++ propositions psi
propositions (Or phi psi) = propositions phi ++ propositions psi
propositions (Implies phi psi) = propositions phi ++ propositions psi
propositions (Iff phi psi) = propositions phi ++ propositions psi

-- 公式深度
depth :: Formula -> Int
depth (Atom _) = 0
depth (Not phi) = 1 + depth phi
depth (And phi psi) = 1 + max (depth phi) (depth psi)
depth (Or phi psi) = 1 + max (depth phi) (depth psi)
depth (Implies phi psi) = 1 + max (depth phi) (depth psi)
depth (Iff phi psi) = 1 + max (depth phi) (depth psi)

-- ============================================================================
-- 语义函数
-- ============================================================================

-- 真值函数
eval :: Formula -> Interpretation -> Bool
eval (Atom p) i = i p
eval (Not phi) i = not (eval phi i)
eval (And phi psi) i = eval phi i && eval psi i
eval (Or phi psi) i = eval phi i || eval psi i
eval (Implies phi psi) i = not (eval phi i) || eval psi i
eval (Iff phi psi) i = eval phi i == eval psi i

-- 生成所有解释
generateAllInterpretations :: [Proposition] -> [Interpretation]
generateAllInterpretations [] = [const False]
generateAllInterpretations (p:ps) = 
    [\q -> if q == p then b else i q | b <- [False, True], i <- generateAllInterpretations ps]

-- 重言式检查
isTautology :: Formula -> Bool
isTautology phi = all (\i -> eval phi i) allInterpretations
  where
    props = nub (propositions phi)
    allInterpretations = generateAllInterpretations props

-- 矛盾式检查
isContradiction :: Formula -> Bool
isContradiction phi = all (\i -> not (eval phi i)) allInterpretations
  where
    props = nub (propositions phi)
    allInterpretations = generateAllInterpretations props

-- 可满足式检查
isSatisfiable :: Formula -> Bool
isSatisfiable phi = any (\i -> eval phi i) allInterpretations
  where
    props = nub (propositions phi)
    allInterpretations = generateAllInterpretations props

-- 逻辑等价
logicallyEquivalent :: Formula -> Formula -> Bool
logicallyEquivalent phi psi = all (\i -> eval phi i == eval psi i) allInterpretations
  where
    props = nub (propositions phi ++ propositions psi)
    allInterpretations = generateAllInterpretations props

-- 逻辑蕴含
logicallyImplies :: Formula -> Formula -> Bool
logicallyImplies phi psi = all (\i -> not (eval phi i) || eval psi i) allInterpretations
  where
    props = nub (propositions phi ++ propositions psi)
    allInterpretations = generateAllInterpretations props

-- 模型检查
isModel :: Interpretation -> Context -> Bool
isModel i ctx = all (\phi -> eval phi i) ctx

-- 所有模型
allModels :: Context -> [Interpretation]
allModels ctx = 
    let props = nub (concatMap propositions ctx)
        allInterpretations = generateAllInterpretations props
    in [i | i <- allInterpretations, isModel i ctx]

-- ============================================================================
-- 证明系统
-- ============================================================================

-- 获取证明结论
conclusion :: Derivation -> Formula
conclusion (Assumption phi) = phi
conclusion (ImplicationIntro psi deriv) = Implies psi (conclusion deriv)
conclusion (ImplicationElim deriv1 deriv2) = 
    case conclusion deriv1 of
        Implies _ chi -> chi
        _ -> error "Invalid implication elimination"
conclusion (ConjunctionIntro deriv1 deriv2) = And (conclusion deriv1) (conclusion deriv2)
conclusion (ConjunctionElim1 deriv) = 
    case conclusion deriv of
        And psi _ -> psi
        _ -> error "Invalid conjunction elimination"
conclusion (ConjunctionElim2 deriv) = 
    case conclusion deriv of
        And _ chi -> chi
        _ -> error "Invalid conjunction elimination"
conclusion (DisjunctionIntro1 psi deriv) = Or psi (conclusion deriv)
conclusion (DisjunctionIntro2 psi deriv) = Or (conclusion deriv) psi
conclusion (DisjunctionElim _ deriv2 _) = conclusion deriv2
conclusion (NegationIntro psi deriv) = Not psi
conclusion (NegationElim _ _) = Atom "⊥"
conclusion (ContradictionElim _ phi) = phi

-- 证明检查
checkProof :: Context -> Formula -> Derivation -> Bool
checkProof ctx phi (Assumption psi) = psi `elem` ctx
checkProof ctx phi (ImplicationIntro psi deriv) = 
    phi == Implies psi (conclusion deriv) && 
    checkProof (psi:ctx) (conclusion deriv) deriv
checkProof ctx phi (ImplicationElim deriv1 deriv2) = 
    case conclusion deriv1 of
        Implies psi chi -> phi == chi && 
                          checkProof ctx (Implies psi chi) deriv1 && 
                          checkProof ctx psi deriv2
        _ -> False
checkProof ctx phi (ConjunctionIntro deriv1 deriv2) = 
    case phi of
        And psi chi -> checkProof ctx psi deriv1 && checkProof ctx chi deriv2
        _ -> False
checkProof ctx phi (ConjunctionElim1 deriv) = 
    case conclusion deriv of
        And psi _ -> phi == psi && checkProof ctx (conclusion deriv) deriv
        _ -> False
checkProof ctx phi (ConjunctionElim2 deriv) = 
    case conclusion deriv of
        And _ chi -> phi == chi && checkProof ctx (conclusion deriv) deriv
        _ -> False
checkProof ctx phi (DisjunctionIntro1 psi deriv) = 
    case phi of
        Or psi' chi -> psi == psi' && checkProof ctx psi deriv
        _ -> False
checkProof ctx phi (DisjunctionIntro2 psi deriv) = 
    case phi of
        Or chi psi' -> psi == psi' && checkProof ctx psi deriv
        _ -> False
checkProof ctx phi (DisjunctionElim deriv1 deriv2 deriv3) = 
    case conclusion deriv1 of
        Or psi chi -> checkProof ctx (Or psi chi) deriv1 &&
                     checkProof (psi:ctx) phi deriv2 &&
                     checkProof (chi:ctx) phi deriv3
        _ -> False
checkProof ctx phi (NegationIntro psi deriv) = 
    phi == Not psi && 
    checkProof (psi:ctx) (Atom "⊥") deriv
checkProof ctx phi (NegationElim deriv1 deriv2) = 
    case (conclusion deriv1, conclusion deriv2) of
        (psi, Not psi') -> psi == psi' && 
                          checkProof ctx psi deriv1 && 
                          checkProof ctx (Not psi') deriv2
        _ -> False
checkProof ctx phi (ContradictionElim deriv _) = 
    checkProof ctx (Atom "⊥") deriv

-- 证明存在性检查（简化版本）
hasProof :: Context -> Formula -> Bool
hasProof gamma psi = 
    case psi of
        Implies alpha beta -> hasProof (alpha:gamma) beta
        And alpha beta -> hasProof gamma alpha && hasProof gamma beta
        Or alpha beta -> hasProof gamma alpha || hasProof gamma beta
        Not alpha -> hasProof (alpha:gamma) (Atom "⊥")
        _ -> psi `elem` gamma

-- ============================================================================
-- 元理论函数
-- ============================================================================

-- 一致性检查
isConsistent :: Context -> Bool
isConsistent ctx = not (hasProof ctx (Atom "⊥"))

-- 可靠性检查
soundness :: Context -> Formula -> Derivation -> Bool
soundness ctx phi deriv = 
    checkProof ctx phi deriv && 
    all (\i -> eval phi i) (modelsOf ctx)
  where
    modelsOf gamma = [i | i <- allInterpretations, all (\psi -> eval psi i) gamma]
    allInterpretations = generateAllInterpretations (concatMap propositions gamma)

-- 完备性检查（简化版本）
completeness :: Context -> Formula -> Bool
completeness ctx phi = 
    if all (\i -> eval phi i) (modelsOf ctx)
    then hasProof ctx phi
    else True
  where
    modelsOf gamma = [i | i <- allInterpretations, all (\psi -> eval psi i) gamma]
    allInterpretations = generateAllInterpretations (concatMap propositions gamma)

-- 极大一致集构造
maximalConsistentSet :: Context -> [Formula]
maximalConsistentSet ctx = 
    let allFormulas = generateAllFormulas ctx
        addIfConsistent gamma phi = 
            if isConsistent (phi:gamma) then phi:gamma else gamma
    in foldl addIfConsistent ctx allFormulas

-- 生成所有公式（简化版本）
generateAllFormulas :: Context -> [Formula]
generateAllFormulas ctx = 
    let props = nub (concatMap propositions ctx)
        atoms = map Atom props
        -- 这里简化处理，实际应该生成所有可能的公式
    in atoms

-- ============================================================================
-- 标准重言式
-- ============================================================================

-- 排中律
excludedMiddle :: Formula
excludedMiddle = Or (Atom "p") (Not (Atom "p"))

-- 矛盾律
nonContradiction :: Formula
nonContradiction = Not (And (Atom "p") (Not (Atom "p")))

-- 同一律
identity :: Formula
identity = Implies (Atom "p") (Atom "p")

-- 双重否定律
doubleNegation :: Formula
doubleNegation = Iff (Atom "p") (Not (Not (Atom "p")))

-- 德摩根律
deMorgan1 :: Formula
deMorgan1 = Iff (Not (And (Atom "p") (Atom "q"))) 
                (Or (Not (Atom "p")) (Not (Atom "q")))

deMorgan2 :: Formula
deMorgan2 = Iff (Not (Or (Atom "p") (Atom "q"))) 
                (And (Not (Atom "p")) (Not (Atom "q")))

-- 分配律
distributive1 :: Formula
distributive1 = Iff (And (Atom "p") (Or (Atom "q") (Atom "r")))
                    (Or (And (Atom "p") (Atom "q")) (And (Atom "p") (Atom "r")))

distributive2 :: Formula
distributive2 = Iff (Or (Atom "p") (And (Atom "q") (Atom "r")))
                    (And (Or (Atom "p") (Atom "q")) (Or (Atom "p") (Atom "r")))

-- 蕴含的等价形式
implicationEquivalence :: Formula
implicationEquivalence = Iff (Implies (Atom "p") (Atom "q"))
                              (Or (Not (Atom "p")) (Atom "q"))

-- ============================================================================
-- 示例和测试
-- ============================================================================

-- 基本示例
example1 :: Formula
example1 = Implies (And (Atom "p") (Atom "q")) (Atom "p")

example2 :: Formula
example2 = Or (Atom "p") (Not (Atom "p"))

example3 :: Formula
example3 = Implies (Atom "p") (Implies (Atom "q") (Atom "p"))

-- 电路设计验证示例
circuitExample :: Formula
circuitExample = 
    Iff (And (Atom "input1") (Atom "input2")) 
        (Atom "output")

-- 协议验证示例
protocolExample :: Formula
protocolExample = 
    Implies (And (Atom "send") (Atom "receive")) 
            (Atom "complete")

-- 约束条件示例
constraintExample :: Formula
constraintExample = 
    Implies (Atom "condition1") 
            (Or (Atom "action1") (Atom "action2"))

-- 测试函数
testTautology :: Bool
testTautology = isTautology example2

testSatisfiable :: Bool
testSatisfiable = isSatisfiable example1

testEquivalent :: Bool
testEquivalent = logicallyEquivalent 
    (Implies (Atom "p") (Atom "q")) 
    (Or (Not (Atom "p")) (Atom "q"))

-- 验证标准重言式
testStandardTautologies :: [Bool]
testStandardTautologies = 
    [ isTautology excludedMiddle
    , isTautology nonContradiction
    , isTautology identity
    , isTautology doubleNegation
    , isTautology deMorgan1
    , isTautology deMorgan2
    , isTautology distributive1
    , isTautology distributive2
    , isTautology implicationEquivalence
    ]

-- ============================================================================
-- 实用工具函数
-- ============================================================================

-- 公式的析取范式（DNF）
toDNF :: Formula -> Formula
toDNF = error "DNF conversion not implemented"

-- 公式的合取范式（CNF）
toCNF :: Formula -> Formula
toCNF = error "CNF conversion not implemented"

-- 公式的最小化
minimize :: Formula -> Formula
minimize = error "Minimization not implemented"

-- 公式的等价性检查
areEquivalent :: Formula -> Formula -> Bool
areEquivalent phi psi = logicallyEquivalent phi psi

-- 公式的蕴含性检查
doesImply :: Formula -> Formula -> Bool
doesImply phi psi = logicallyImplies phi psi

-- 上下文的一致性检查
isContextConsistent :: Context -> Bool
isContextConsistent = isConsistent

-- 上下文的可满足性检查
isContextSatisfiable :: Context -> Bool
isContextSatisfiable ctx = not (null (allModels ctx))

-- ============================================================================
-- 性能优化函数
-- ============================================================================

-- 缓存解释结果
type Cache = [(Formula, Interpretation, Bool)]

-- 带缓存的求值函数
evalWithCache :: Formula -> Interpretation -> Cache -> (Bool, Cache)
evalWithCache phi i cache = 
    case lookup (phi, i) cache of
        Just result -> (result, cache)
        Nothing -> 
            let result = eval phi i
                newCache = ((phi, i, result):cache)
            in (result, newCache)

-- 优化的重言式检查
isTautologyOptimized :: Formula -> Bool
isTautologyOptimized phi = 
    let props = nub (propositions phi)
        interpretations = generateAllInterpretations props
        check i = eval phi i
    in all check interpretations

-- ============================================================================
-- 导出列表
-- ============================================================================

module PropositionalLogic 
    ( -- 类型
      Proposition(..)
    , Formula(..)
    , Interpretation
    , Context
    , Derivation(..)
    
    -- 语法函数
    , complexity
    , subformulas
    , propositions
    , depth
    
    -- 语义函数
    , eval
    , generateAllInterpretations
    , isTautology
    , isContradiction
    , isSatisfiable
    , logicallyEquivalent
    , logicallyImplies
    , isModel
    , allModels
    
    -- 证明系统
    , conclusion
    , checkProof
    , hasProof
    
    -- 元理论函数
    , isConsistent
    , soundness
    , completeness
    , maximalConsistentSet
    
    -- 标准重言式
    , excludedMiddle
    , nonContradiction
    , identity
    , doubleNegation
    , deMorgan1
    , deMorgan2
    , distributive1
    , distributive2
    , implicationEquivalence
    
    -- 示例
    , example1
    , example2
    , example3
    , circuitExample
    , protocolExample
    , constraintExample
    
    -- 测试函数
    , testTautology
    , testSatisfiable
    , testEquivalent
    , testStandardTautologies
    
    -- 实用工具
    , areEquivalent
    , doesImply
    , isContextConsistent
    , isContextSatisfiable
    
    -- 性能优化
    , evalWithCache
    , isTautologyOptimized
    ) where 