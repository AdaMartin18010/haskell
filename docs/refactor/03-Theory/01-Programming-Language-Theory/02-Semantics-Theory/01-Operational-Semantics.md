# 操作语义 (Operational Semantics)

## 概述

操作语义是编程语言语义学的重要分支，通过描述程序执行的具体步骤来定义语言的语义。操作语义关注程序如何从初始状态逐步执行到最终状态。

## 基本概念

### 配置 (Configuration)

配置表示程序执行过程中的状态，通常包含程序代码和当前环境。

```haskell
-- 基本配置类型
data Configuration a = Configuration
  { program :: a
  , environment :: Environment
  , store :: Store
  }

-- 环境：变量到值的映射
type Environment = [(String, Value)]

-- 存储：地址到值的映射
type Store = [(Address, Value)]

-- 地址
type Address = Integer

-- 值
data Value = IntVal Integer
           | BoolVal Bool
           | Closure String Expr Environment
           | UnitVal
           deriving (Eq, Show)

-- 表达式
data Expr = Var String
          | IntLit Integer
          | BoolLit Bool
          | Add Expr Expr
          | Sub Expr Expr
          | Mul Expr Expr
          | Div Expr Expr
          | Eq Expr Expr
          | Lt Expr Expr
          | If Expr Expr Expr
          | Lambda String Expr
          | App Expr Expr
          | Let String Expr Expr
          | Ref Expr
          | Deref Expr
          | Assign Expr Expr
          | Seq Expr Expr
          deriving (Eq, Show)
```

## 小步语义 (Small-Step Semantics)

### 基本规则

小步语义通过关系 $\rightarrow$ 描述程序的一步执行。

```haskell
-- 小步语义关系
data Step = Step Configuration Configuration deriving (Show)

-- 小步语义规则
smallStep :: Configuration Expr -> Maybe (Configuration Expr)
smallStep (Configuration expr env store) = case expr of
  -- 算术运算
  Add (IntLit n1) (IntLit n2) -> 
    Just $ Configuration (IntLit (n1 + n2)) env store
  
  Sub (IntLit n1) (IntLit n2) -> 
    Just $ Configuration (IntLit (n1 - n2)) env store
  
  Mul (IntLit n1) (IntLit n2) -> 
    Just $ Configuration (IntLit (n1 * n2)) env store
  
  Div (IntLit n1) (IntLit n2) -> 
    if n2 /= 0 
    then Just $ Configuration (IntLit (n1 `div` n2)) env store
    else Nothing  -- 除零错误
  
  -- 比较运算
  Eq (IntLit n1) (IntLit n2) -> 
    Just $ Configuration (BoolLit (n1 == n2)) env store
  
  Lt (IntLit n1) (IntLit n2) -> 
    Just $ Configuration (BoolLit (n1 < n2)) env store
  
  -- 条件语句
  If (BoolLit True) e1 _ -> 
    Just $ Configuration e1 env store
  
  If (BoolLit False) _ e2 -> 
    Just $ Configuration e2 env store
  
  -- 函数应用
  App (Closure x body env') (IntLit n) -> 
    Just $ Configuration body ((x, IntVal n) : env') store
  
  -- 变量查找
  Var x -> 
    case lookup x env of
      Just (IntVal n) -> Just $ Configuration (IntLit n) env store
      Just (BoolVal b) -> Just $ Configuration (BoolLit b) env store
      _ -> Nothing
  
  -- 上下文规则
  Add e1 e2 -> 
    case smallStep (Configuration e1 env store) of
      Just (Configuration e1' env' store') -> 
        Just $ Configuration (Add e1' e2) env' store'
      Nothing -> 
        case smallStep (Configuration e2 env store) of
          Just (Configuration e2' env' store') -> 
            Just $ Configuration (Add e1 e2') env' store'
          Nothing -> Nothing
  
  If e1 e2 e3 -> 
    case smallStep (Configuration e1 env store) of
      Just (Configuration e1' env' store') -> 
        Just $ Configuration (If e1' e2 e3) env' store'
      Nothing -> Nothing
  
  App e1 e2 -> 
    case smallStep (Configuration e1 env store) of
      Just (Configuration e1' env' store') -> 
        Just $ Configuration (App e1' e2) env' store'
      Nothing -> 
        case smallStep (Configuration e2 env store) of
          Just (Configuration e2' env' store') -> 
            Just $ Configuration (App e1 e2') env' store'
          Nothing -> Nothing
  
  -- 其他情况
  _ -> Nothing
```

### 多步执行

```haskell
-- 多步执行关系
multiStep :: Configuration Expr -> [Configuration Expr]
multiStep config = config : case smallStep config of
  Just next -> multiStep next
  Nothing -> []

-- 执行到最终状态
execute :: Configuration Expr -> Maybe (Configuration Expr)
execute config = case multiStep config of
  [] -> Nothing
  steps -> Just $ last steps

-- 检查是否为最终状态
isFinal :: Configuration Expr -> Bool
isFinal config = case smallStep config of
  Nothing -> True
  Just _ -> False
```

## 大步语义 (Big-Step Semantics)

### 求值关系

大步语义通过关系 $\Downarrow$ 直接描述表达式的求值结果。

```haskell
-- 大步语义关系
data BigStep = BigStep Expr Environment Value deriving (Show)

-- 大步语义规则
bigStep :: Expr -> Environment -> Maybe Value
bigStep expr env = case expr of
  -- 字面量
  IntLit n -> Just $ IntVal n
  BoolLit b -> Just $ BoolVal b
  
  -- 变量
  Var x -> lookup x env
  
  -- 算术运算
  Add e1 e2 -> do
    IntVal n1 <- bigStep e1 env
    IntVal n2 <- bigStep e2 env
    return $ IntVal (n1 + n2)
  
  Sub e1 e2 -> do
    IntVal n1 <- bigStep e1 env
    IntVal n2 <- bigStep e2 env
    return $ IntVal (n1 - n2)
  
  Mul e1 e2 -> do
    IntVal n1 <- bigStep e1 env
    IntVal n2 <- bigStep e2 env
    return $ IntVal (n1 * n2)
  
  Div e1 e2 -> do
    IntVal n1 <- bigStep e1 env
    IntVal n2 <- bigStep e2 env
    if n2 /= 0 
    then return $ IntVal (n1 `div` n2)
    else Nothing
  
  -- 比较运算
  Eq e1 e2 -> do
    IntVal n1 <- bigStep e1 env
    IntVal n2 <- bigStep e2 env
    return $ BoolVal (n1 == n2)
  
  Lt e1 e2 -> do
    IntVal n1 <- bigStep e1 env
    IntVal n2 <- bigStep e2 env
    return $ BoolVal (n1 < n2)
  
  -- 条件语句
  If e1 e2 e3 -> do
    BoolVal b <- bigStep e1 env
    if b then bigStep e2 env else bigStep e3 env
  
  -- 函数抽象
  Lambda x body -> Just $ Closure x body env
  
  -- 函数应用
  App e1 e2 -> do
    Closure x body env' <- bigStep e1 env
    v <- bigStep e2 env
    bigStep body ((x, v) : env')
  
  -- Let绑定
  Let x e1 e2 -> do
    v <- bigStep e1 env
    bigStep e2 ((x, v) : env)
  
  -- 其他情况
  _ -> Nothing
```

## 结构化操作语义 (SOS)

### 标签转换系统

```haskell
-- 标签
data Label = Tau           -- 内部动作
           | Input String   -- 输入动作
           | Output String  -- 输出动作
           | Call String    -- 函数调用
           | Return Value   -- 函数返回
           deriving (Eq, Show)

-- 标签转换
data LabeledTransition = LabeledTransition 
  { from :: Configuration Expr
  , label :: Label
  , to :: Configuration Expr
  } deriving (Show)

-- 标签转换规则
labeledStep :: Configuration Expr -> Maybe (LabeledTransition, Configuration Expr)
labeledStep (Configuration expr env store) = case expr of
  -- 函数调用
  App (Closure x body env') (IntLit n) -> 
    Just (LabeledTransition 
      (Configuration expr env store) 
      (Call x) 
      (Configuration body ((x, IntVal n) : env') store),
      Configuration body ((x, IntVal n) : env') store)
  
  -- 函数返回
  IntLit n -> 
    Just (LabeledTransition 
      (Configuration expr env store) 
      (Return (IntVal n)) 
      (Configuration expr env store),
      Configuration expr env store)
  
  -- 内部计算
  Add (IntLit n1) (IntLit n2) -> 
    Just (LabeledTransition 
      (Configuration expr env store) 
      Tau 
      (Configuration (IntLit (n1 + n2)) env store),
      Configuration (IntLit (n1 + n2)) env store)
  
  -- 其他情况
  _ -> Nothing
```

## 抽象机语义 (Abstract Machine Semantics)

### 栈式抽象机

```haskell
-- 抽象机状态
data AbstractMachine = AbstractMachine
  { code :: [Instruction]
  , stack :: [Value]
  , environment :: Environment
  , store :: Store
  }

-- 指令
data Instruction = Push Value
                 | Pop
                 | AddI
                 | SubI
                 | MulI
                 | DivI
                 | EqI
                 | LtI
                 | IfI [Instruction] [Instruction]
                 | CallI
                 | ReturnI
                 | Load String
                 | StoreI String
                 deriving (Eq, Show)

-- 抽象机执行
executeMachine :: AbstractMachine -> Maybe AbstractMachine
executeMachine machine = case code machine of
  [] -> Nothing  -- 停机
  (Push v):rest -> 
    Just $ machine { code = rest, stack = v : stack machine }
  
  Pop:rest -> 
    case stack machine of
      _:stack' -> Just $ machine { code = rest, stack = stack' }
      [] -> Nothing
  
  AddI:rest -> 
    case stack machine of
      (IntVal n2):(IntVal n1):stack' -> 
        Just $ machine { code = rest, stack = IntVal (n1 + n2) : stack' }
      _ -> Nothing
  
  SubI:rest -> 
    case stack machine of
      (IntVal n2):(IntVal n1):stack' -> 
        Just $ machine { code = rest, stack = IntVal (n1 - n2) : stack' }
      _ -> Nothing
  
  MulI:rest -> 
    case stack machine of
      (IntVal n2):(IntVal n1):stack' -> 
        Just $ machine { code = rest, stack = IntVal (n1 * n2) : stack' }
      _ -> Nothing
  
  DivI:rest -> 
    case stack machine of
      (IntVal n2):(IntVal n1):stack' -> 
        if n2 /= 0 
        then Just $ machine { code = rest, stack = IntVal (n1 `div` n2) : stack' }
        else Nothing
      _ -> Nothing
  
  EqI:rest -> 
    case stack machine of
      (IntVal n2):(IntVal n1):stack' -> 
        Just $ machine { code = rest, stack = BoolVal (n1 == n2) : stack' }
      _ -> Nothing
  
  LtI:rest -> 
    case stack machine of
      (IntVal n2):(IntVal n1):stack' -> 
        Just $ machine { code = rest, stack = BoolVal (n1 < n2) : stack' }
      _ -> Nothing
  
  (IfI code1 code2):rest -> 
    case stack machine of
      (BoolVal True):stack' -> 
        Just $ machine { code = code1 ++ rest, stack = stack' }
      (BoolVal False):stack' -> 
        Just $ machine { code = code2 ++ rest, stack = stack' }
      _ -> Nothing
  
  Load x:rest -> 
    case lookup x (environment machine) of
      Just v -> Just $ machine { code = rest, stack = v : stack machine }
      Nothing -> Nothing
  
  StoreI x:rest -> 
    case stack machine of
      v:stack' -> 
        Just $ machine { 
          code = rest, 
          stack = stack', 
          environment = (x, v) : environment machine 
        }
      _ -> Nothing
  
  _ -> Nothing

-- 编译表达式到指令序列
compile :: Expr -> [Instruction]
compile expr = case expr of
  IntLit n -> [Push (IntVal n)]
  BoolLit b -> [Push (BoolVal b)]
  Var x -> [Load x]
  Add e1 e2 -> compile e1 ++ compile e2 ++ [AddI]
  Sub e1 e2 -> compile e1 ++ compile e2 ++ [SubI]
  Mul e1 e2 -> compile e1 ++ compile e2 ++ [MulI]
  Div e1 e2 -> compile e1 ++ compile e2 ++ [DivI]
  Eq e1 e2 -> compile e1 ++ compile e2 ++ [EqI]
  Lt e1 e2 -> compile e1 ++ compile e2 ++ [LtI]
  If e1 e2 e3 -> compile e1 ++ [IfI (compile e2) (compile e3)]
  Let x e1 e2 -> compile e1 ++ [StoreI x] ++ compile e2 ++ [Pop]
  _ -> []
```

## 并发操作语义

### 进程代数

```haskell
-- 进程
data Process = Nil                    -- 空进程
             | Action String Process  -- 动作前缀
             | Choice Process Process -- 选择
             | Par Process Process    -- 并行
             | Restrict String Process -- 限制
             deriving (Eq, Show)

-- 并发配置
data ConcurrentConfig = ConcurrentConfig
  { processes :: [Process]
  , sharedState :: Environment
  }

-- 并发转换规则
concurrentStep :: ConcurrentConfig -> [ConcurrentConfig]
concurrentStep config = concatMap (stepProcess config) (processes config)

-- 单个进程的转换
stepProcess :: ConcurrentConfig -> Process -> [ConcurrentConfig]
stepProcess config process = case process of
  Action a p -> 
    [config { processes = replace (processes config) process p }]
  
  Choice p1 p2 -> 
    stepProcess config p1 ++ stepProcess config p2
  
  Par p1 p2 -> 
    let steps1 = stepProcess config p1
        steps2 = stepProcess config p2
    in steps1 ++ steps2 ++ 
       [config { processes = replace (processes config) process (Par p1' p2') } 
        | p1' <- [p1], p2' <- [p2]]
  
  _ -> []

-- 辅助函数
replace :: [a] -> a -> a -> [a]
replace xs old new = map (\x -> if x == old then new else x) xs
```

## 应用示例

### 简单程序执行

```haskell
-- 示例程序：计算 (3 + 4) * 2
exampleProgram :: Expr
exampleProgram = Mul (Add (IntLit 3) (IntLit 4)) (IntLit 2)

-- 小步语义执行
exampleSmallStep :: [Configuration Expr]
exampleSmallStep = multiStep $ Configuration exampleProgram [] []

-- 大步语义执行
exampleBigStep :: Maybe Value
exampleBigStep = bigStep exampleProgram []

-- 抽象机执行
exampleMachine :: AbstractMachine
exampleMachine = AbstractMachine
  { code = compile exampleProgram
  , stack = []
  , environment = []
  , store = []
  }

-- 执行抽象机
executeExampleMachine :: [AbstractMachine]
executeExampleMachine = iterateMachine exampleMachine
  where
    iterateMachine machine = case executeMachine machine of
      Just next -> machine : iterateMachine next
      Nothing -> [machine]
```

### 函数调用示例

```haskell
-- 定义函数：f(x) = x + 1
functionDefinition :: Expr
functionDefinition = Lambda "x" (Add (Var "x") (IntLit 1))

-- 函数调用：f(5)
functionCall :: Expr
functionCall = App functionDefinition (IntLit 5)

-- 执行函数调用
executeFunctionCall :: Maybe Value
executeFunctionCall = bigStep functionCall []
```

## 语义等价性

### 语义等价关系

```haskell
-- 语义等价
semanticEquivalence :: Expr -> Expr -> Environment -> Bool
semanticEquivalence e1 e2 env = 
  bigStep e1 env == bigStep e2 env

-- 上下文等价
contextualEquivalence :: Expr -> Expr -> Bool
contextualEquivalence e1 e2 = 
  all (\env -> semanticEquivalence e1 e2 env) allEnvironments
  where
    allEnvironments = []  -- 简化实现
```

## 总结

操作语义为编程语言提供了精确的执行模型，通过不同的语义风格（小步、大步、结构化、抽象机）来描述程序的行为。主要特点：

1. **精确性**：提供程序执行的精确描述
2. **可执行性**：语义规则可以直接实现为解释器
3. **分析性**：便于进行程序分析和验证
4. **教学性**：帮助理解程序执行过程

通过Haskell的实现，我们能够：

- 实际执行语义规则
- 验证语义性质
- 构建程序分析工具
- 开发语言解释器

操作语义为编程语言的理论研究和实际实现提供了坚实的基础。
