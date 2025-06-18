# 函数式设计模式 (Functional Design Patterns)

## 概述

函数式设计模式是Haskell编程中的核心模式，体现了函数式编程的核心理念：不可变性、纯函数、高阶函数和函数组合。本文档系统性介绍Haskell中的函数式设计模式，包括形式化定义、数学模型和实际应用。

## 目录

1. [基本概念](#基本概念)
2. [函数组合模式](#函数组合模式)
3. [柯里化模式](#柯里化模式)
4. [部分应用模式](#部分应用模式)
5. [函数提升模式](#函数提升模式)
6. [Haskell实现](#haskell实现)
7. [最佳实践](#最佳实践)

## 基本概念

### 定义 5.1.1: 函数式设计模式 (Functional Design Pattern)

函数式设计模式是使用纯函数、不可变数据和函数组合来解决编程问题的标准化方法。

### 定义 5.1.2: 纯函数 (Pure Function)

纯函数是对于相同输入总是产生相同输出，且没有副作用的函数。

### 函数式模式的数学定义

函数式模式可以表示为：
$$F = (D, C, P, E)$$

其中：
- $D$ 是数据流
- $C$ 是函数组合
- $P$ 是纯函数集合
- $E$ 是效果处理

## 函数组合模式

### 函数组合的定义

```haskell
-- 函数组合操作符
(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

-- 函数组合模式
data FunctionComposition = FunctionComposition
  { composition :: [Function]
  , compositionType :: CompositionType
  , compositionResult :: Function
  }

-- 函数
data Function = Function
  { functionName :: String
  , functionType :: FunctionType
  , functionBody :: String
  , functionPurity :: Bool
  }

-- 函数类型
data FunctionType = 
    Unary (Type -> Type)
  | Binary (Type -> Type -> Type)
  | HigherOrder ((Type -> Type) -> Type -> Type)

-- 组合类型
data CompositionType = 
    Sequential
  | Parallel
  | Conditional
  | Recursive

-- 类型
data Type = 
    Int
  | String
  | Bool
  | List Type
  | Function Type Type

-- 创建函数组合
createFunctionComposition :: [Function] -> CompositionType -> FunctionComposition
createFunctionComposition functions compType = FunctionComposition
  { composition = functions
  , compositionType = compType
  , compositionResult = composeFunctions functions compType
  }

-- 组合函数
composeFunctions :: [Function] -> CompositionType -> Function
composeFunctions functions compType = case compType of
  Sequential -> composeSequential functions
  Parallel -> composeParallel functions
  Conditional -> composeConditional functions
  Recursive -> composeRecursive functions

-- 顺序组合
composeSequential :: [Function] -> Function
composeSequential functions = Function
  { functionName = "sequential_composition"
  , functionType = Unary (head (map functionType functions))
  , functionBody = "f1 . f2 . f3"
  , functionPurity = all functionPurity functions
  }

-- 并行组合
composeParallel :: [Function] -> Function
composeParallel functions = Function
  { functionName = "parallel_composition"
  , functionType = Unary (head (map functionType functions))
  , functionBody = "\\x -> (f1 x, f2 x, f3 x)"
  , functionPurity = all functionPurity functions
  }

-- 条件组合
composeConditional :: [Function] -> Function
composeConditional functions = Function
  { functionName = "conditional_composition"
  , functionType = Unary (head (map functionType functions))
  , functionBody = "\\x -> if condition x then f1 x else f2 x"
  , functionPurity = all functionPurity functions
  }

-- 递归组合
composeRecursive :: [Function] -> Function
composeRecursive functions = Function
  { functionName = "recursive_composition"
  , functionType = Unary (head (map functionType functions))
  , functionBody = "\\x -> if baseCase x then x else f (recursive x)"
  , functionPurity = all functionPurity functions
  }
```

### 函数组合的数学表示

函数组合的数学定义：
$$(f \circ g)(x) = f(g(x))$$

组合的代数性质：
- **结合律**: $(f \circ g) \circ h = f \circ (g \circ h)$
- **单位元**: $f \circ id = id \circ f = f$

### 实际应用示例

```haskell
-- 函数组合示例
functionCompositionExample :: IO ()
functionCompositionExample = do
  putStrLn "Function Composition Examples"
  
  -- 基本函数
  let double = (*2)
  let addOne = (+1)
  let square = (^2)
  
  -- 顺序组合
  let composed1 = double . addOne . square
  putStrLn $ "double . addOne . square $ 3 = " ++ show (composed1 3)
  
  -- 并行组合
  let parallel = \x -> (double x, addOne x, square x)
  putStrLn $ "parallel 3 = " ++ show (parallel 3)
  
  -- 条件组合
  let conditional = \x -> if x > 0 then double x else addOne x
  putStrLn $ "conditional 3 = " ++ show (conditional 3)
  putStrLn $ "conditional (-3) = " ++ show (conditional (-3))
  
  -- 递归组合
  let factorial = \n -> if n <= 1 then 1 else n * factorial (n-1)
  putStrLn $ "factorial 5 = " ++ show (factorial 5)
```

## 柯里化模式

### 柯里化的定义

```haskell
-- 柯里化模式
data CurryingPattern = CurryingPattern
  { originalFunction :: Function
  , curriedFunction :: Function
  , curryingSteps :: [CurryingStep]
  }

-- 柯里化步骤
data CurryingStep = CurryingStep
  { stepNumber :: Int
  , stepDescription :: String
  , stepFunction :: Function
  , stepType :: CurryingType
  }

-- 柯里化类型
data CurryingType = 
    PartialApplication
  | FullCurrying
  | ReverseCurrying

-- 柯里化器
data Currier = Currier
  { currierType :: CurrierType
  , currierRules :: [CurryingRule]
  }

-- 柯里化器类型
data CurrierType = 
    ManualCurrier
  | AutomaticCurrier
  | OptimizedCurrier

-- 柯里化规则
data CurryingRule = CurryingRule
  { ruleName :: String
  , ruleCondition :: CurryingCondition
  , ruleAction :: CurryingAction
  }

-- 柯里化条件
data CurryingCondition = 
    HasMultipleArgs Int
  | IsPureFunction
  | HasTypeSignature

-- 柯里化动作
data CurryingAction = 
    ApplyFirst
  | ApplyLast
  | ApplyMiddle Int

-- 执行柯里化
performCurrying :: Currier -> Function -> CurryingPattern
performCurrier currier func = 
  let steps = applyCurryingRules currier func
      curriedFunc = createCurriedFunction steps
  in CurryingPattern
    { originalFunction = func
    , curriedFunction = curriedFunc
    , curryingSteps = steps
    }

-- 应用柯里化规则
applyCurryingRules :: Currier -> Function -> [CurryingStep]
applyCurrier currier func = 
  map (\rule -> applyCurryingRule rule func) (currierRules currier)

-- 应用单个柯里化规则
applyCurryingRule :: CurryingRule -> Function -> CurryingStep
applyCurryingRule rule func = 
  let stepNum = 1  -- 简化实现
      description = "Applied " ++ ruleName rule
      stepFunc = createStepFunction rule func
      stepType = determineCurryingType rule
  in CurryingStep
    { stepNumber = stepNum
    , stepDescription = description
    , stepFunction = stepFunc
    , stepType = stepType
    }

-- 创建步骤函数
createStepFunction :: CurryingRule -> Function -> Function
createStepFunction rule func = 
  case ruleAction rule of
    ApplyFirst -> Function
      { functionName = functionName func ++ "_curried_first"
      , functionType = Unary (functionType func)
      , functionBody = "\\x -> " ++ functionName func ++ " x"
      , functionPurity = functionPurity func
      }
    ApplyLast -> Function
      { functionName = functionName func ++ "_curried_last"
      , functionType = Unary (functionType func)
      , functionBody = "\\x -> " ++ functionName func ++ " x"
      , functionPurity = functionPurity func
      }
    ApplyMiddle _ -> Function
      { functionName = functionName func ++ "_curried_middle"
      , functionType = Unary (functionType func)
      , functionBody = "\\x -> " ++ functionName func ++ " x"
      , functionPurity = functionPurity func
      }

-- 确定柯里化类型
determineCurryingType :: CurryingRule -> CurryingType
determineCurryingType rule = 
  case ruleAction rule of
    ApplyFirst -> PartialApplication
    ApplyLast -> PartialApplication
    ApplyMiddle _ -> PartialApplication

-- 创建柯里化函数
createCurriedFunction :: [CurryingStep] -> Function
createCurriedFunction steps = Function
  { functionName = "curried_function"
  , functionType = Unary Int
  , functionBody = "\\x -> " ++ concatMap (\step -> functionName (stepFunction step) ++ " ") steps ++ "x"
  , functionPurity = all (\step -> functionPurity (stepFunction step)) steps
  }
```

### 柯里化的数学表示

柯里化的数学定义：
$$\text{curry}: (A \times B \rightarrow C) \rightarrow (A \rightarrow (B \rightarrow C))$$

柯里化的逆操作：
$$\text{uncurry}: (A \rightarrow (B \rightarrow C)) \rightarrow (A \times B \rightarrow C)$$

### 实际应用示例

```haskell
-- 柯里化示例
curryingExample :: IO ()
curryingExample = do
  putStrLn "Currying Examples"
  
  -- 原始多参数函数
  let add :: Int -> Int -> Int
      add x y = x + y
  
  -- 柯里化后的函数
  let addCurried = add
  let addFive = addCurried 5
  
  putStrLn $ "add 3 4 = " ++ show (add 3 4)
  putStrLn $ "addCurried 3 4 = " ++ show (addCurried 3 4)
  putStrLn $ "addFive 3 = " ++ show (addFive 3)
  
  -- 部分应用
  let multiply :: Int -> Int -> Int
      multiply x y = x * y
  
  let double = multiply 2
  let triple = multiply 3
  
  putStrLn $ "double 5 = " ++ show (double 5)
  putStrLn $ "triple 5 = " ++ show (triple 5)
  
  -- 高阶函数中的柯里化
  let numbers = [1, 2, 3, 4, 5]
  let doubled = map double numbers
  let tripled = map triple numbers
  
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Doubled: " ++ show doubled
  putStrLn $ "Tripled: " ++ show tripled
```

## 部分应用模式

### 部分应用的定义

```haskell
-- 部分应用模式
data PartialApplicationPattern = PartialApplicationPattern
  { originalFunction :: Function
  , appliedArguments :: [Argument]
  , remainingArguments :: [Argument]
  , partialFunction :: Function
  }

-- 参数
data Argument = Argument
  { argumentValue :: String
  , argumentType :: Type
  , argumentPosition :: Int
  }

-- 部分应用器
data PartialApplicator = PartialApplicator
  { applicatorType :: ApplicatorType
  , applicationStrategy :: ApplicationStrategy
  }

-- 应用器类型
data ApplicatorType = 
    LeftToRight
  | RightToLeft
  | Positional
  | Named

-- 应用策略
data ApplicationStrategy = ApplicationStrategy
  { strategyName :: String
  , strategyRules :: [ApplicationRule]
  , strategyOptimization :: OptimizationLevel
  }

-- 应用规则
data ApplicationRule = ApplicationRule
  { ruleName :: String
  , ruleCondition :: ApplicationCondition
  , ruleAction :: ApplicationAction
  }

-- 应用条件
data ApplicationCondition = 
    HasFixedArgs Int
  | IsPureFunction
  | HasTypeSignature
  | IsHigherOrder

-- 应用动作
data ApplicationAction = 
    ApplyLeft
  | ApplyRight
  | ApplyPosition Int
  | ApplyNamed String

-- 优化级别
data OptimizationLevel = 
    NoOptimization
  | BasicOptimization
  | AdvancedOptimization
  | FullOptimization

-- 执行部分应用
performPartialApplication :: PartialApplicator -> Function -> [Argument] -> PartialApplicationPattern
performPartialApplication applicator func args = 
  let strategy = applicationStrategy applicator
      appliedArgs = applyArguments strategy func args
      remainingArgs = getRemainingArguments func appliedArgs
      partialFunc = createPartialFunction func appliedArgs
  in PartialApplicationPattern
    { originalFunction = func
    , appliedArguments = appliedArgs
    , remainingArguments = remainingArgs
    , partialFunction = partialFunc
    }

-- 应用参数
applyArguments :: ApplicationStrategy -> Function -> [Argument] -> [Argument]
applyArguments strategy func args = 
  let rules = strategyRules strategy
  in concatMap (\rule -> applyApplicationRule rule func args) rules

-- 应用单个规则
applyApplicationRule :: ApplicationRule -> Function -> [Argument] -> [Argument]
applyApplicationRule rule func args = 
  if checkApplicationCondition rule func
    then case ruleAction rule of
      ApplyLeft -> take 1 args
      ApplyRight -> drop (length args - 1) args
      ApplyPosition pos -> if pos < length args then [args !! pos] else []
      ApplyNamed name -> filter (\arg -> argumentValue arg == name) args
    else []

-- 检查应用条件
checkApplicationCondition :: ApplicationRule -> Function -> Bool
checkApplicationCondition rule func = 
  case ruleCondition rule of
    HasFixedArgs n -> True  -- 简化实现
    IsPureFunction -> functionPurity func
    HasTypeSignature -> True  -- 简化实现
    IsHigherOrder -> True  -- 简化实现

-- 获取剩余参数
getRemainingArguments :: Function -> [Argument] -> [Argument]
getRemainingArguments func appliedArgs = 
  -- 简化实现，实际会根据函数类型计算剩余参数
  []

-- 创建部分应用函数
createPartialFunction :: Function -> [Argument] -> Function
createPartialFunction func appliedArgs = Function
  { functionName = functionName func ++ "_partial"
  , functionType = Unary (functionType func)
  , functionBody = "\\x -> " ++ functionName func ++ " " ++ concatMap argumentValue appliedArgs ++ " x"
  , functionPurity = functionPurity func
  }
```

### 部分应用的数学表示

部分应用的数学定义：
$$\text{partial}: (A \times B \rightarrow C) \times A \rightarrow (B \rightarrow C)$$

部分应用的性质：
- **左结合性**: $\text{partial}(f, a)(b) = f(a, b)$
- **右结合性**: $\text{partial}(f, b)(a) = f(a, b)$

### 实际应用示例

```haskell
-- 部分应用示例
partialApplicationExample :: IO ()
partialApplicationExample = do
  putStrLn "Partial Application Examples"
  
  -- 基本部分应用
  let add :: Int -> Int -> Int
      add x y = x + y
  
  let addTen = add 10
  let addTwenty = add 20
  
  putStrLn $ "addTen 5 = " ++ show (addTen 5)
  putStrLn $ "addTwenty 5 = " ++ show (addTwenty 5)
  
  -- 高阶函数中的部分应用
  let numbers = [1, 2, 3, 4, 5]
  let addTenToAll = map addTen
  let addTwentyToAll = map addTwenty
  
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Add ten: " ++ show (addTenToAll numbers)
  putStrLn $ "Add twenty: " ++ show (addTwentyToAll numbers)
  
  -- 函数组合中的部分应用
  let filterGreaterThan :: Int -> [Int] -> [Int]
      filterGreaterThan n = filter (> n)
  
  let filterGreaterThanFive = filterGreaterThan 5
  let filterGreaterThanTen = filterGreaterThan 10
  
  putStrLn $ "Greater than 5: " ++ show (filterGreaterThanFive numbers)
  putStrLn $ "Greater than 10: " ++ show (filterGreaterThanTen numbers)
```

## 函数提升模式

### 函数提升的定义

```haskell
-- 函数提升模式
data FunctionLiftingPattern = FunctionLiftingPattern
  { originalFunction :: Function
  , liftedFunction :: Function
  , liftingType :: LiftingType
  , liftingContext :: LiftingContext
  }

-- 提升类型
data LiftingType = 
    FunctorLifting
  | ApplicativeLifting
  | MonadLifting
  | TraversableLifting

-- 提升上下文
data LiftingContext = LiftingContext
  { contextType :: ContextType
  , contextRules :: [LiftingRule]
  , contextOptimization :: OptimizationLevel
  }

-- 上下文类型
data ContextType = 
    MaybeContext
  | ListContext
  | EitherContext String
  | IOContext
  | CustomContext String

-- 提升规则
data LiftingRule = LiftingRule
  { ruleName :: String
  , ruleCondition :: LiftingCondition
  , ruleAction :: LiftingAction
  }

-- 提升条件
data LiftingCondition = 
    IsFunctor
  | IsApplicative
  | IsMonad
  | IsTraversable

-- 提升动作
data LiftingAction = 
    LiftToFunctor
  | LiftToApplicative
  | LiftToMonad
  | LiftToTraversable

-- 函数提升器
data FunctionLifter = FunctionLifter
  { lifterType :: LiftingType
  , lifterRules :: [LiftingRule]
  , lifterContext :: LiftingContext
  }

-- 执行函数提升
performFunctionLifting :: FunctionLifter -> Function -> FunctionLiftingPattern
performFunctionLifting lifter func = 
  let liftedFunc = liftFunction lifter func
      liftingType = lifterType lifter
      context = lifterContext lifter
  in FunctionLiftingPattern
    { originalFunction = func
    , liftedFunction = liftedFunc
    , liftingType = liftingType
    , liftingContext = context
    }

-- 提升函数
liftFunction :: FunctionLifter -> Function -> Function
liftFunction lifter func = 
  case lifterType lifter of
    FunctorLifting -> liftToFunctor func
    ApplicativeLifting -> liftToApplicative func
    MonadLifting -> liftToMonad func
    TraversableLifting -> liftToTraversable func

-- 提升到Functor
liftToFunctor :: Function -> Function
liftToFunctor func = Function
  { functionName = "fmap " ++ functionName func
  , functionType = Unary (functionType func)
  , functionBody = "fmap " ++ functionName func
  , functionPurity = functionPurity func
  }

-- 提升到Applicative
liftToApplicative :: Function -> Function
liftToApplicative func = Function
  { functionName = "liftA " ++ functionName func
  , functionType = Unary (functionType func)
  , functionBody = "liftA " ++ functionName func
  , functionPurity = functionPurity func
  }

-- 提升到Monad
liftToMonad :: Function -> Function
liftToMonad func = Function
  { functionName = "liftM " ++ functionName func
  , functionType = Unary (functionType func)
  , functionBody = "liftM " ++ functionName func
  , functionPurity = functionPurity func
  }

-- 提升到Traversable
liftToTraversable :: Function -> Function
liftToTraversable func = Function
  { functionName = "traverse " ++ functionName func
  , functionType = Unary (functionType func)
  , functionBody = "traverse " ++ functionName func
  , functionPurity = functionPurity func
  }
```

### 函数提升的数学表示

函数提升的数学定义：

**Functor提升**:
$$fmap: (a \rightarrow b) \rightarrow F a \rightarrow F b$$

**Applicative提升**:
$$liftA: (a \rightarrow b) \rightarrow F a \rightarrow F b$$

**Monad提升**:
$$liftM: (a \rightarrow b) \rightarrow M a \rightarrow M b$$

### 实际应用示例

```haskell
-- 函数提升示例
functionLiftingExample :: IO ()
functionLiftingExample = do
  putStrLn "Function Lifting Examples"
  
  -- 基本函数
  let double :: Int -> Int
      double x = x * 2
  
  let addOne :: Int -> Int
      addOne x = x + 1
  
  -- Functor提升
  let maybeNumbers = [Just 1, Just 2, Nothing, Just 4]
  let liftedDouble = fmap double
  let liftedAddOne = fmap addOne
  
  putStrLn $ "Original: " ++ show maybeNumbers
  putStrLn $ "Lifted double: " ++ show (map liftedDouble maybeNumbers)
  putStrLn $ "Lifted addOne: " ++ show (map liftedAddOne maybeNumbers)
  
  -- Applicative提升
  let add :: Int -> Int -> Int
      add x y = x + y
  
  let maybeX = Just 5
  let maybeY = Just 3
  
  let liftedAdd = liftA2 add
  putStrLn $ "liftA2 add (Just 5) (Just 3) = " ++ show (liftedAdd maybeX maybeY)
  
  -- Monad提升
  let divide :: Int -> Int -> Maybe Int
      divide x y = if y == 0 then Nothing else Just (x `div` y)
  
  let maybeDiv = liftM2 divide
  putStrLn $ "liftM2 divide (Just 10) (Just 2) = " ++ show (maybeDiv (Just 10) (Just 2))
  putStrLn $ "liftM2 divide (Just 10) (Just 0) = " ++ show (maybeDiv (Just 10) (Just 0))
  
  -- Traversable提升
  let numbers = [1, 2, 3, 4, 5]
  let safeDivide :: Int -> Int -> Maybe Int
      safeDivide x y = if y == 0 then Nothing else Just (x `div` y)
  
  let divideByTwo = safeDivide 10
  let traversedResult = traverse divideByTwo numbers
  putStrLn $ "traverse (safeDivide 10) [1,2,3,4,5] = " ++ show traversedResult
```

## Haskell实现

### 综合示例

```haskell
-- 函数式设计模式模块
module FunctionalDesignPatterns where

import Data.Maybe (fromMaybe)
import Control.Applicative (liftA2)
import Control.Monad (liftM2)

-- 函数组合器
class FunctionComposer a where
  compose :: (b -> c) -> (a -> b) -> a -> c
  pipe :: (a -> b) -> (b -> c) -> a -> c

-- 柯里化器
class Currier a b where
  curry :: ((a, b) -> c) -> a -> b -> c
  uncurry :: (a -> b -> c) -> (a, b) -> c

-- 部分应用器
class PartialApplicator f where
  partial :: f -> a -> f
  apply :: f -> a -> b

-- 函数提升器
class FunctionLifter f where
  lift :: (a -> b) -> f a -> f b
  liftA :: (a -> b -> c) -> f a -> f b -> f c
  liftM :: (a -> b) -> f a -> f b

-- 函数组合示例
functionCompositionExample :: IO ()
functionCompositionExample = do
  putStrLn "Function Composition Demo"
  
  -- 基本函数
  let double = (*2)
  let addOne = (+1)
  let square = (^2)
  
  -- 组合函数
  let composed = double . addOne . square
  putStrLn $ "double . addOne . square $ 3 = " ++ show (composed 3)
  
  -- 管道操作
  let piped = square >.> addOne >.> double
  putStrLn $ "square >.> addOne >.> double $ 3 = " ++ show (piped 3)

-- 管道操作符
(>.) :: (a -> b) -> (b -> c) -> a -> c
(>.) = flip (.)

-- 柯里化示例
curryingExample :: IO ()
curryingExample = do
  putStrLn "Currying Demo"
  
  -- 原始函数
  let add :: Int -> Int -> Int
      add x y = x + y
  
  -- 柯里化
  let addFive = add 5
  putStrLn $ "add 5 3 = " ++ show (addFive 3)
  
  -- 部分应用
  let multiply :: Int -> Int -> Int
      multiply x y = x * y
  
  let double = multiply 2
  putStrLn $ "double 5 = " ++ show (double 5)

-- 部分应用示例
partialApplicationExample :: IO ()
partialApplicationExample = do
  putStrLn "Partial Application Demo"
  
  -- 高阶函数中的部分应用
  let numbers = [1, 2, 3, 4, 5]
  let addTen = (+10)
  let multiplyByTwo = (*2)
  
  let processed = map (addTen . multiplyByTwo) numbers
  putStrLn $ "Processed: " ++ show processed
  
  -- 过滤和映射的组合
  let filterAndMap = map addTen . filter (>2)
  let result = filterAndMap numbers
  putStrLn $ "Filter and map: " ++ show result

-- 函数提升示例
functionLiftingExample :: IO ()
functionLiftingExample = do
  putStrLn "Function Lifting Demo"
  
  -- Maybe上下文中的提升
  let maybeNumbers = [Just 1, Just 2, Nothing, Just 4]
  let doubleMaybe = fmap (*2)
  
  let doubled = map doubleMaybe maybeNumbers
  putStrLn $ "Doubled maybe: " ++ show doubled
  
  -- Applicative提升
  let addMaybe = liftA2 (+)
  let result = addMaybe (Just 5) (Just 3)
  putStrLn $ "Applicative add: " ++ show result
  
  -- Monad提升
  let divideMaybe = liftM2 div
  let divResult = divideMaybe (Just 10) (Just 2)
  putStrLn $ "Monad divide: " ++ show divResult

-- 综合模式示例
comprehensivePatternExample :: IO ()
comprehensivePatternExample = do
  putStrLn "Comprehensive Pattern Demo"
  
  -- 数据
  let numbers = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  
  -- 函数组合
  let processNumber = (*2) . (+1) . (^2)
  
  -- 部分应用
  let filterEven = filter even
  let mapProcess = map processNumber
  
  -- 函数提升
  let safeDivide :: Int -> Int -> Maybe Int
      safeDivide x y = if y == 0 then Nothing else Just (x `div` y)
  
  let divideByTwo = safeDivide 10
  
  -- 组合所有模式
  let pipeline = mapProcess . filterEven
  let result = pipeline numbers
  
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Pipeline result: " ++ show result
  
  -- 使用提升的函数
  let maybeResults = traverse divideByTwo result
  putStrLn $ "Safe division results: " ++ show maybeResults
```

### 实际应用示例

```haskell
-- 实际应用示例
realWorldExample :: IO ()
realWorldExample = do
  putStrLn "Real World Application Demo"
  
  -- 模拟用户数据
  let users = [("Alice", 25), ("Bob", 30), ("Charlie", 35), ("David", 40)]
  
  -- 数据处理管道
  let extractAge = snd
  let isAdult = (>=18)
  let formatAge = \age -> "Age: " ++ show age
  
  -- 组合处理函数
  let processUser = formatAge . extractAge
  let filterAdults = filter (isAdult . extractAge)
  let mapProcess = map processUser
  
  -- 完整管道
  let userPipeline = mapProcess . filterAdults
  let result = userPipeline users
  
  putStrLn $ "Users: " ++ show users
  putStrLn $ "Processed adults: " ++ show result
  
  -- 错误处理
  let safeExtractAge :: (String, Int) -> Maybe Int
      safeExtractAge (_, age) = if age >= 0 then Just age else Nothing
  
  let safeProcessUser = fmap formatAge . safeExtractAge
  let safeResults = mapMaybe safeProcessUser users
  
  putStrLn $ "Safe processing: " ++ show safeResults

-- 辅助函数
mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe f = concatMap (maybe [] (:[]) . f)
```

## 最佳实践

1. **优先使用函数组合**: 利用函数组合构建复杂功能
2. **利用柯里化**: 创建可重用的函数片段
3. **合理使用部分应用**: 减少重复代码
4. **适当使用函数提升**: 处理上下文中的计算
5. **保持函数纯度**: 避免副作用，提高可测试性

## 相关链接

- [类型类模式](./02-Type-Class-Patterns.md)
- [单子变换器模式](./03-Monad-Transformer-Patterns.md)
- [透镜模式](./04-Lens-Patterns.md)

---

**作者**: 形式化知识体系重构项目  
**最后更新**: 2024年12月  
**版本**: 1.0 