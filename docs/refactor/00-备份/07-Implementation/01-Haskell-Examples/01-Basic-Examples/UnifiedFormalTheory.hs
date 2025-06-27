{-# LANGUAGE GADTs, TypeFamilies, FlexibleContexts, FlexibleInstances #-}

-- 统一形式理论公理化框架的Haskell实现
-- 为各种形式理论提供统一的基础和映射机制

module UnifiedFormalTheory where

import Data.List (nub, intersect, union)
import Data.Maybe (fromJust, isJust)
import Control.Monad (guard)

-- ============================================================================
-- 1. 基本类型定义
-- ============================================================================

-- 统一形式系统
data UnifiedFormalSystem = 
    UnifiedFormalSystem 
        { symbols :: SymbolSet
        , rules :: RuleSet
        , axioms :: AxiomSet
        , derivation :: DerivationRelation
        , typeSystem :: TypeSystem
        , languageSystem :: LanguageSystem
        , modelSystem :: ModelSystem
        }
  deriving (Show, Eq)

-- 符号集合
data SymbolSet = 
    SymbolSet 
        { constants :: [Constant]
        , variables :: [Variable]
        , operators :: [Operator]
        , predicates :: [Predicate]
        }
  deriving (Show, Eq)

-- 符号类型
data Constant = Constant String deriving (Show, Eq)
data Variable = Variable String deriving (Show, Eq)
data Operator = Operator String Int deriving (Show, Eq) -- 名称和元数
data Predicate = Predicate String Int deriving (Show, Eq) -- 名称和元数

-- 规则集合
data RuleSet = 
    RuleSet 
        { formationRules :: [FormationRule]
        , introductionRules :: [IntroductionRule]
        , eliminationRules :: [EliminationRule]
        , computationRules :: [ComputationRule]
        }
  deriving (Show, Eq)

-- 规则类型
data FormationRule = FormationRule String deriving (Show, Eq)
data IntroductionRule = IntroductionRule String deriving (Show, Eq)
data EliminationRule = EliminationRule String deriving (Show, Eq)
data ComputationRule = ComputationRule String deriving (Show, Eq)

-- 公理集合
data AxiomSet = 
    AxiomSet 
        { logicalAxioms :: [LogicalAxiom]
        , mathematicalAxioms :: [MathematicalAxiom]
        , structuralAxioms :: [StructuralAxiom]
        }
  deriving (Show, Eq)

-- 公理类型
data LogicalAxiom = LogicalAxiom String deriving (Show, Eq)
data MathematicalAxiom = MathematicalAxiom String deriving (Show, Eq)
data StructuralAxiom = StructuralAxiom String deriving (Show, Eq)

-- 推导关系
data DerivationRelation = 
    DerivationRelation 
        { premises :: [Formula]
        , conclusion :: Formula
        , rule :: Rule
        }
  deriving (Show, Eq)

-- 公式
data Formula = 
    Atomic String [Term]
  | Not Formula
  | And Formula Formula
  | Or Formula Formula
  | Implies Formula Formula
  | Iff Formula Formula
  | ForAll Variable Formula
  | Exists Variable Formula
  deriving (Show, Eq)

-- 项
data Term = 
    Var Variable
  | Const Constant
  | App Term Term
  deriving (Show, Eq)

-- 规则
data Rule = 
    ModusPonens
  | UniversalGeneralization
  | ExistentialIntroduction
  | AndIntroduction
  | AndElimination
  | OrIntroduction
  | OrElimination
  | NotIntroduction
  | NotElimination
  deriving (Show, Eq)

-- 类型系统
data TypeSystem = 
    TypeSystem 
        { baseTypes :: [BaseType]
        , typeConstructors :: [TypeConstructor]
        , typeRules :: [TypeRule]
        , typeChecking :: TypeChecking
        }
  deriving (Show, Eq)

-- 基础类型
data BaseType = 
    UnitType
  | BooleanType
  | NaturalType
  | IntegerType
  | RealType
  | StringType
  deriving (Show, Eq)

-- 类型构造子
data TypeConstructor = 
    ProductType Type Type
  | SumType Type Type
  | FunctionType Type Type
  | ListType Type
  | MaybeType Type
  | RecursiveType String Type
  deriving (Show, Eq)

-- 类型
data Type = 
    Base BaseType
  | Constructed TypeConstructor
  | Variable String
  deriving (Show, Eq)

-- 类型规则
data TypeRule = 
    TypeRule 
        { premises :: [TypeJudgment]
        , conclusion :: TypeJudgment
        , name :: String
        }
  deriving (Show, Eq)

-- 类型判断
data TypeJudgment = 
    TypeJudgment 
        { context :: TypeContext
        , term :: Term
        , type_ :: Type
        }
  deriving (Show, Eq)

-- 类型上下文
type TypeContext = [(Variable, Type)]

-- 类型检查
data TypeChecking = 
    TypeChecking 
        { check :: TypeContext -> Term -> Type -> Bool
        , infer :: TypeContext -> Term -> Maybe Type
        , unify :: Type -> Type -> Maybe Substitution
        }

-- 替换
type Substitution = [(String, Type)]

-- 语言系统
data LanguageSystem = 
    LanguageSystem 
        { syntax :: Syntax
        , semantics :: Semantics
        , pragmatics :: Pragmatics
        }
  deriving (Show, Eq)

-- 语法
data Syntax = 
    Syntax 
        { alphabet :: [Symbol]
        , formationRules :: [FormationRule]
        , wellFormedness :: WellFormedness
        }
  deriving (Show, Eq)

-- 符号
data Symbol = 
    Terminal String
  | NonTerminal String
  deriving (Show, Eq)

-- 良构性
data WellFormedness = 
    WellFormedness 
        { check :: String -> Bool
        , generate :: [String]
        }
  deriving (Show, Eq)

-- 语义
data Semantics = 
    Semantics 
        { interpretation :: Interpretation
        , evaluation :: Evaluation
        , satisfaction :: Satisfaction
        }
  deriving (Show, Eq)

-- 解释
data Interpretation = 
    Interpretation 
        { domain :: Domain
        , function :: Function
        , relation :: Relation
        }
  deriving (Show, Eq)

-- 域
data Domain = 
    Domain 
        { elements :: [Element]
        , structure :: Structure
        }
  deriving (Show, Eq)

-- 元素
data Element = 
    Element 
        { name :: String
        , properties :: [Property]
        }
  deriving (Show, Eq)

-- 属性
data Property = 
    Property 
        { name :: String
        , value :: Value
        }
  deriving (Show, Eq)

-- 值
data Value = 
    Boolean Bool
  | Number Double
  | String String
  | Function Function
  deriving (Show, Eq)

-- 函数
data Function = 
    Function 
        { domain :: [Element]
        , codomain :: [Element]
        , mapping :: [(Element, Element)]
        }
  deriving (Show, Eq)

-- 关系
data Relation = 
    Relation 
        { domain :: [Element]
        , tuples :: [[Element]]
        }
  deriving (Show, Eq)

-- 结构
data Structure = 
    Structure 
        { operations :: [Operation]
        , relations :: [Relation]
        , axioms :: [Axiom]
        }
  deriving (Show, Eq)

-- 操作
data Operation = 
    Operation 
        { name :: String
        , arity :: Int
        , function :: Function
        }
  deriving (Show, Eq)

-- 公理
data Axiom = 
    Axiom 
        { name :: String
        , formula :: Formula
        }
  deriving (Show, Eq)

-- 评估
data Evaluation = 
    Evaluation 
        { evaluate :: Environment -> Term -> Value
        , environment :: Environment
        }
  deriving (Show, Eq)

-- 环境
type Environment = [(Variable, Value)]

-- 满足
data Satisfaction = 
    Satisfaction 
        { satisfies :: Model -> Formula -> Bool
        , model :: Model
        }
  deriving (Show, Eq)

-- 模型
data Model = 
    Model 
        { domain :: Domain
        , interpretation :: Interpretation
        }
  deriving (Show, Eq)

-- 语用学
data Pragmatics = 
    Pragmatics 
        { context :: Context
        , intention :: Intention
        , effect :: Effect
        }
  deriving (Show, Eq)

-- 上下文
data Context = 
    Context 
        { speaker :: Agent
        , hearer :: Agent
        , situation :: Situation
        }
  deriving (Show, Eq)

-- 智能体
data Agent = 
    Agent 
        { name :: String
        , knowledge :: Knowledge
        , beliefs :: Beliefs
        }
  deriving (Show, Eq)

-- 知识
data Knowledge = 
    Knowledge 
        { facts :: [Fact]
        , rules :: [Rule]
        }
  deriving (Show, Eq)

-- 事实
data Fact = 
    Fact 
        { proposition :: Formula
        , confidence :: Double
        }
  deriving (Show, Eq)

-- 信念
data Beliefs = 
    Beliefs 
        { propositions :: [Formula]
        , degrees :: [Double]
        }
  deriving (Show, Eq)

-- 情境
data Situation = 
    Situation 
        { time :: Time
        , place :: Place
        , circumstances :: [Circumstance]
        }
  deriving (Show, Eq)

-- 时间
data Time = 
    Time 
        { moment :: String
        , duration :: Duration
        }
  deriving (Show, Eq)

-- 持续时间
data Duration = 
    Duration 
        { start :: String
        , end :: String
        }
  deriving (Show, Eq)

-- 地点
data Place = 
    Place 
        { location :: String
        , coordinates :: Coordinates
        }
  deriving (Show, Eq)

-- 坐标
data Coordinates = 
    Coordinates 
        { x :: Double
        , y :: Double
        , z :: Double
        }
  deriving (Show, Eq)

-- 情况
data Circumstance = 
    Circumstance 
        { description :: String
        , relevance :: Relevance
        }
  deriving (Show, Eq)

-- 相关性
data Relevance = 
    High
  | Medium
  | Low
  deriving (Show, Eq)

-- 意图
data Intention = 
    Intention 
        { goal :: Goal
        , plan :: Plan
        }
  deriving (Show, Eq)

-- 目标
data Goal = 
    Goal 
        { description :: String
        , priority :: Priority
        }
  deriving (Show, Eq)

-- 优先级
data Priority = 
    High
  | Medium
  | Low
  deriving (Show, Eq)

-- 计划
data Plan = 
    Plan 
        { steps :: [Step]
        , resources :: [Resource]
        }
  deriving (Show, Eq)

-- 步骤
data Step = 
    Step 
        { action :: Action
        , precondition :: Formula
        , postcondition :: Formula
        }
  deriving (Show, Eq)

-- 动作
data Action = 
    Action 
        { name :: String
        , parameters :: [Parameter]
        }
  deriving (Show, Eq)

-- 参数
data Parameter = 
    Parameter 
        { name :: String
        , type_ :: Type
        }
  deriving (Show, Eq)

-- 资源
data Resource = 
    Resource 
        { name :: String
        , availability :: Bool
        }
  deriving (Show, Eq)

-- 效果
data Effect = 
    Effect 
        { outcome :: Outcome
        , impact :: Impact
        }
  deriving (Show, Eq)

-- 结果
data Outcome = 
    Outcome 
        { success :: Bool
        , description :: String
        }
  deriving (Show, Eq)

-- 影响
data Impact = 
    Impact 
        { magnitude :: Magnitude
        , scope :: Scope
        }
  deriving (Show, Eq)

-- 量级
data Magnitude = 
    Large
  | Medium
  | Small
  deriving (Show, Eq)

-- 范围
data Scope = 
    Global
  | Local
  | Individual
  deriving (Show, Eq)

-- 模型系统
data ModelSystem = 
    ModelSystem 
        { models :: [Model]
        , relationships :: [ModelRelationship]
        , transformations :: [Transformation]
        }
  deriving (Show, Eq)

-- 模型关系
data ModelRelationship = 
    ModelRelationship 
        { source :: Model
        , target :: Model
        , relation :: RelationType
        }
  deriving (Show, Eq)

-- 关系类型
data RelationType = 
    Isomorphism
  | Homomorphism
  | Embedding
  | Projection
  deriving (Show, Eq)

-- 变换
data Transformation = 
    Transformation 
        { name :: String
        , function :: Model -> Model
        , properties :: [Property]
        }
  deriving (Show, Eq)

-- ============================================================================
-- 2. 实例和示例
-- ============================================================================

-- 示例：命题逻辑系统
propositionalLogicSystem :: UnifiedFormalSystem
propositionalLogicSystem = UnifiedFormalSystem
    { symbols = SymbolSet
        { constants = [Constant "T", Constant "F"]
        , variables = [Variable "p", Variable "q", Variable "r"]
        , operators = [Operator "¬" 1, Operator "∧" 2, Operator "∨" 2, Operator "→" 2]
        , predicates = []
        }
    , rules = RuleSet
        { formationRules = [FormationRule "原子公式", FormationRule "复合公式"]
        , introductionRules = [IntroductionRule "合取引入", IntroductionRule "析取引入"]
        , eliminationRules = [EliminationRule "合取消除", EliminationRule "析取消除"]
        , computationRules = [ComputationRule "双重否定", ComputationRule "德摩根律"]
        }
    , axioms = AxiomSet
        { logicalAxioms = [LogicalAxiom "排中律", LogicalAxiom "矛盾律"]
        , mathematicalAxioms = []
        , structuralAxioms = [StructuralAxiom "结合律", StructuralAxiom "交换律"]
        }
    , derivation = DerivationRelation
        { premises = [Atomic "p" [], Atomic "q" []]
        , conclusion = Atomic "p∧q" []
        , rule = AndIntroduction
        }
    , typeSystem = TypeSystem
        { baseTypes = [BooleanType]
        , typeConstructors = [FunctionType (Base BooleanType) (Base BooleanType)]
        , typeRules = []
        , typeChecking = TypeChecking
            { check = \_ _ _ -> True
            , infer = \_ _ -> Just (Base BooleanType)
            , unify = \_ _ -> Just []
            }
        }
    , languageSystem = LanguageSystem
        { syntax = Syntax
            { alphabet = [Terminal "p", Terminal "q", Terminal "∧", Terminal "∨"]
            , formationRules = [FormationRule "命题公式"]
            , wellFormedness = WellFormedness
                { check = \s -> length s > 0
                , generate = ["p", "q", "p∧q", "p∨q"]
                }
            }
        , semantics = Semantics
            { interpretation = Interpretation
                { domain = Domain
                    { elements = [Element "T" [], Element "F" []]
                    , structure = Structure [] [] []
                    }
                , function = Function [] [] []
                , relation = Relation [] []
                }
            , evaluation = Evaluation
                { evaluate = \_ _ -> Boolean True
                , environment = []
                }
            , satisfaction = Satisfaction
                { satisfies = \_ _ -> True
                , model = Model
                    { domain = Domain [] (Structure [] [] [])
                    , interpretation = Interpretation
                        { domain = Domain [] (Structure [] [] [])
                        , function = Function [] [] []
                        , relation = Relation [] []
                        }
                    }
                }
            }
        , pragmatics = Pragmatics
            { context = Context
                { speaker = Agent "Speaker" (Knowledge [] []) (Beliefs [] [])
                , hearer = Agent "Hearer" (Knowledge [] []) (Beliefs [] [])
                , situation = Situation
                    { time = Time "now" (Duration "now" "now")
                    , place = Place "here" (Coordinates 0 0 0)
                    , circumstances = []
                    }
                }
            , intention = Intention
                { goal = Goal "communicate" High
                , plan = Plan [] []
                }
            , effect = Effect
                { outcome = Outcome True "successful"
                , impact = Impact Medium Local
                }
            }
        }
    , modelSystem = ModelSystem
        { models = []
        , relationships = []
        , transformations = []
        }
    }

-- ============================================================================
-- 3. 工具函数
-- ============================================================================

-- 检查公式的有效性
isValidFormula :: Formula -> Bool
isValidFormula (Atomic _ _) = True
isValidFormula (Not f) = isValidFormula f
isValidFormula (And f1 f2) = isValidFormula f1 && isValidFormula f2
isValidFormula (Or f1 f2) = isValidFormula f1 && isValidFormula f2
isValidFormula (Implies f1 f2) = isValidFormula f1 && isValidFormula f2
isValidFormula (Iff f1 f2) = isValidFormula f1 && isValidFormula f2
isValidFormula (ForAll _ f) = isValidFormula f
isValidFormula (Exists _ f) = isValidFormula f

-- 检查类型系统的完整性
isTypeSystemComplete :: TypeSystem -> Bool
isTypeSystemComplete (TypeSystem baseTypes typeConstructors typeRules typeChecking) =
    not (null baseTypes) && 
    not (null typeRules) &&
    all isValidTypeRule typeRules

-- 检查类型规则的有效性
isValidTypeRule :: TypeRule -> Bool
isValidTypeRule (TypeRule premises conclusion name) =
    not (null name) && 
    not (null premises) &&
    isValidTypeJudgment conclusion

-- 检查类型判断的有效性
isValidTypeJudgment :: TypeJudgment -> Bool
isValidTypeJudgment (TypeJudgment context term type_) =
    not (null context) &&
    isValidTerm term &&
    isValidType type_

-- 检查项的有效性
isValidTerm :: Term -> Bool
isValidTerm (Var _) = True
isValidTerm (Const _) = True
isValidTerm (App t1 t2) = isValidTerm t1 && isValidTerm t2

-- 检查类型的有效性
isValidType :: Type -> Bool
isValidType (Base _) = True
isValidType (Constructed _) = True
isValidType (Variable _) = True

-- 检查形式系统的完整性
isFormalSystemComplete :: UnifiedFormalSystem -> Bool
isFormalSystemComplete system =
    not (null (symbols system)) &&
    not (null (rules system)) &&
    not (null (axioms system)) &&
    isTypeSystemComplete (typeSystem system)

-- 生成所有可能的公式
generateFormulas :: SymbolSet -> [Formula]
generateFormulas (SymbolSet constants variables operators predicates) =
    let atomicFormulas = [Atomic (name p) [] | p <- predicates]
        compoundFormulas = concatMap generateCompoundFormulas atomicFormulas
    in atomicFormulas ++ compoundFormulas

-- 生成复合公式
generateCompoundFormulas :: Formula -> [Formula]
generateCompoundFormulas f =
    [Not f,
     And f f,
     Or f f,
     Implies f f,
     Iff f f]

-- 检查推导的有效性
isValidDerivation :: DerivationRelation -> Bool
isValidDerivation (DerivationRelation premises conclusion rule) =
    not (null premises) &&
    isValidFormula conclusion &&
    all isValidFormula premises

-- 应用推导规则
applyRule :: Rule -> [Formula] -> Maybe Formula
applyRule AndIntroduction [f1, f2] = Just (And f1 f2)
applyRule AndElimination [And f1 f2] = Just f1
applyRule OrIntroduction [f1] = Just (Or f1 f1)
applyRule OrElimination [Or f1 f2] = Just f1
applyRule NotIntroduction [f] = Just (Not f)
applyRule NotElimination [Not (Not f)] = Just f
applyRule Implies [f1, f2] = Just (Implies f1 f2)
applyRule _ _ = Nothing

-- 检查语义解释的一致性
isInterpretationConsistent :: Interpretation -> Bool
isInterpretationConsistent (Interpretation domain function relation) =
    not (null (elements domain)) &&
    isValidFunction function &&
    isValidRelation relation

-- 检查函数的有效性
isValidFunction :: Function -> Bool
isValidFunction (Function domain codomain mapping) =
    not (null domain) &&
    not (null codomain) &&
    all (\pair -> fst pair `elem` domain && snd pair `elem` codomain) mapping

-- 检查关系的有效性
isValidRelation :: Relation -> Bool
isValidRelation (Relation domain tuples) =
    not (null domain) &&
    all (\tuple -> all (`elem` domain) tuple) tuples

-- 检查模型的正确性
isModelCorrect :: Model -> Bool
isModelCorrect (Model domain interpretation) =
    not (null (elements domain)) &&
    isInterpretationConsistent interpretation

-- 检查语用学的一致性
isPragmaticsConsistent :: Pragmatics -> Bool
isPragmaticsConsistent (Pragmatics context intention effect) =
    isValidContext context &&
    isValidIntention intention &&
    isValidEffect effect

-- 检查上下文的有效性
isValidContext :: Context -> Bool
isValidContext (Context speaker hearer situation) =
    not (null (name speaker)) &&
    not (null (name hearer)) &&
    isValidSituation situation

-- 检查意图的有效性
isValidIntention :: Intention -> Bool
isValidIntention (Intention goal plan) =
    not (null (description goal)) &&
    not (null (steps plan))

-- 检查效果的有效性
isValidEffect :: Effect -> Bool
isValidEffect (Effect outcome impact) =
    not (null (description outcome))

-- 检查情境的有效性
isValidSituation :: Situation -> Bool
isValidSituation (Situation time place circumstances) =
    not (null (moment time)) &&
    not (null (location place))

-- ============================================================================
-- 4. 高级功能
-- ============================================================================

-- 形式系统验证器
class FormalSystemValidator a where
    validate :: a -> Bool
    generateCounterexamples :: a -> [a]
    prove :: a -> Maybe Proof

-- 证明
data Proof = 
    Proof 
        { premises :: [Formula]
        , steps :: [ProofStep]
        , conclusion :: Formula
        }
  deriving (Show, Eq)

-- 证明步骤
data ProofStep = 
    ProofStep 
        { rule :: Rule
        , premises :: [Formula]
        , conclusion :: Formula
        , justification :: String
        }
  deriving (Show, Eq)

-- 形式系统验证器的实例
instance FormalSystemValidator UnifiedFormalSystem where
    validate system = 
        isFormalSystemComplete system &&
        all isValidFormula (extractAllFormulas system) &&
        all isValidDerivation (extractAllDerivations system)
    
    generateCounterexamples system =
        if validate system then []
        else [system { symbols = emptySymbolSet }]
    
    prove system = 
        if validate system
        then Just (Proof [] [] (Atomic "valid" []))
        else Nothing

-- 提取所有公式
extractAllFormulas :: UnifiedFormalSystem -> [Formula]
extractAllFormulas system =
    [conclusion (derivation system)] ++
    premises (derivation system) ++
    extractAxiomFormulas (axioms system)

-- 提取公理公式
extractAxiomFormulas :: AxiomSet -> [Formula]
extractAxiomFormulas (AxiomSet logical mathematical structural) =
    map (\_ -> Atomic "axiom" []) (logical ++ mathematical ++ structural)

-- 提取所有推导
extractAllDerivations :: UnifiedFormalSystem -> [DerivationRelation]
extractAllDerivations system = [derivation system]

-- 空符号集
emptySymbolSet :: SymbolSet
emptySymbolSet = SymbolSet [] [] [] []

-- 形式系统比较器
class FormalSystemComparator a where
    compare :: a -> a -> Comparison
    isSubsystem :: a -> a -> Bool
    merge :: a -> a -> Maybe a

-- 比较结果
data Comparison = 
    Equivalent
  | Subsystem
  | Supersystem
  | Incompatible
  | Partial
  deriving (Show, Eq)

-- 形式系统比较器的实例
instance FormalSystemComparator UnifiedFormalSystem where
    compare sys1 sys2
        | symbols sys1 == symbols sys2 && 
          rules sys1 == rules sys2 &&
          axioms sys1 == axioms sys2 = Equivalent
        | isSubsystem sys1 sys2 = Subsystem
        | isSubsystem sys2 sys1 = Supersystem
        | canMerge sys1 sys2 = Partial
        | otherwise = Incompatible
    
    isSubsystem sys1 sys2 =
        all (`elem` symbols sys2) (symbols sys1) &&
        all (`elem` rules sys2) (rules sys1) &&
        all (`elem` axioms sys2) (axioms sys1)
    
    merge sys1 sys2 =
        if canMerge sys1 sys2
        then Just (UnifiedFormalSystem
            { symbols = mergeSymbolSets (symbols sys1) (symbols sys2)
            , rules = mergeRuleSets (rules sys1) (rules sys2)
            , axioms = mergeAxiomSets (axioms sys1) (axioms sys2)
            , derivation = derivation sys1
            , typeSystem = typeSystem sys1
            , languageSystem = languageSystem sys1
            , modelSystem = modelSystem sys1
            })
        else Nothing

-- 检查是否可以合并
canMerge :: UnifiedFormalSystem -> UnifiedFormalSystem -> Bool
canMerge sys1 sys2 =
    not (null (intersect (symbols sys1) (symbols sys2))) &&
    not (null (intersect (rules sys1) (rules sys2)))

-- 合并符号集
mergeSymbolSets :: SymbolSet -> SymbolSet -> SymbolSet
mergeSymbolSets (SymbolSet c1 v1 o1 p1) (SymbolSet c2 v2 o2 p2) =
    SymbolSet (nub (c1 ++ c2)) (nub (v1 ++ v2)) (nub (o1 ++ o2)) (nub (p1 ++ p2))

-- 合并规则集
mergeRuleSets :: RuleSet -> RuleSet -> RuleSet
mergeRuleSets (RuleSet f1 i1 e1 c1) (RuleSet f2 i2 e2 c2) =
    RuleSet (nub (f1 ++ f2)) (nub (i1 ++ i2)) (nub (e1 ++ e2)) (nub (c1 ++ c2))

-- 合并公理集
mergeAxiomSets :: AxiomSet -> AxiomSet -> AxiomSet
mergeAxiomSets (AxiomSet l1 m1 s1) (AxiomSet l2 m2 s2) =
    AxiomSet (nub (l1 ++ l2)) (nub (m1 ++ m2)) (nub (s1 ++ s2))

-- ============================================================================
-- 5. 示例和测试
-- ============================================================================

-- 测试函数
testUnifiedFormalTheory :: IO ()
testUnifiedFormalTheory = do
    putStrLn "=== 统一形式理论测试 ==="
    
    -- 测试命题逻辑系统
    putStrLn "1. 测试命题逻辑系统:"
    print $ isFormalSystemComplete propositionalLogicSystem
    print $ isValidFormula (And (Atomic "p" []) (Atomic "q" []))
    
    -- 测试公式生成
    putStrLn "2. 测试公式生成:"
    let formulas = generateFormulas (symbols propositionalLogicSystem)
    print $ length formulas
    print $ take 3 formulas
    
    -- 测试推导规则
    putStrLn "3. 测试推导规则:"
    print $ applyRule AndIntroduction [Atomic "p" [], Atomic "q" []]
    print $ applyRule AndElimination [And (Atomic "p" []) (Atomic "q" [])]
    
    -- 测试系统验证
    putStrLn "4. 测试系统验证:"
    print $ validate propositionalLogicSystem
    print $ prove propositionalLogicSystem
    
    -- 测试系统比较
    putStrLn "5. 测试系统比较:"
    print $ compare propositionalLogicSystem propositionalLogicSystem
    print $ isSubsystem propositionalLogicSystem propositionalLogicSystem
    
    putStrLn "=== 测试完成 ==="

-- 运行测试
main :: IO ()
main = testUnifiedFormalTheory 