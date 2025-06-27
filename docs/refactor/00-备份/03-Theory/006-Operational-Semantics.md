# 操作语义 (Operational Semantics)

## 📚 概述

操作语义通过描述程序执行的计算步骤来定义程序语言的语义。它关注程序如何从初始状态转换到最终状态，提供了程序行为的精确描述。本文档提供了操作语义的完整数学形式化，包括小步语义、大步语义、自然语义等核心概念，以及完整的 Haskell 实现。

**相关文档：**

- [[001-Linear-Type-Theory]] - 线性类型理论
- [[002-Affine-Type-Theory]] - 仿射类型理论
- [[003-Temporal-Type-Theory]] - 时态类型理论
- [[004-Quantum-Type-Theory]] - 量子类型理论
- [[005-Denotational-Semantics]] - 指称语义
- [[007-Axiomatic-Semantics]] - 公理语义
- [[008-Category-Semantics]] - 范畴语义
- [[haskell/02-Type-System]] - Haskell 类型系统

## 1. 操作语义基础

### 1.1 配置与转换关系

**定义 1.1 (配置)**
配置 $\langle e, \sigma \rangle$ 是表达式 $e$ 和状态 $\sigma$ 的有序对，表示程序执行的瞬时状态。

**定义 1.2 (转换关系)**
转换关系 $\rightarrow$ 是配置集合上的二元关系，表示程序执行的一步转换：
$$\langle e, \sigma \rangle \rightarrow \langle e', \sigma' \rangle$$

**定义 1.3 (多步转换)**
多步转换 $\rightarrow^*$ 是转换关系的自反传递闭包：
$$\langle e, \sigma \rangle \rightarrow^* \langle e', \sigma' \rangle$$

**定理 1.1 (转换关系的性质)**
转换关系满足：

1. **确定性**：$\langle e, \sigma \rangle \rightarrow \langle e_1, \sigma_1 \rangle$ 且 $\langle e, \sigma \rangle \rightarrow \langle e_2, \sigma_2 \rangle$ 蕴含 $e_1 = e_2$ 且 $\sigma_1 = \sigma_2$
2. **终止性**：存在配置 $\langle e', \sigma' \rangle$ 使得 $\langle e, \sigma \rangle \rightarrow^* \langle e', \sigma' \rangle$ 且不存在 $\langle e'', \sigma'' \rangle$ 使得 $\langle e', \sigma' \rangle \rightarrow \langle e'', \sigma'' \rangle$

### 1.2 Haskell 实现：操作语义基础

```haskell
-- 配置
data Configuration = Config Expression State
  deriving (Eq, Show)

-- 转换关系
type TransitionRelation = Configuration -> Maybe Configuration

-- 多步转换
type MultiStepTransition = Configuration -> [Configuration]

-- 状态
type State = [(String, Value)]

-- 值
data Value = 
  IntVal Integer |
  BoolVal Bool |
  FuncVal String Expression Environment |
  UnitVal |
  Error String
  deriving (Eq, Show)

-- 表达式
data Expression = 
  Var String |
  LitInt Integer |
  LitBool Bool |
  Add Expression Expression |
  Sub Expression Expression |
  Mul Expression Expression |
  Div Expression Expression |
  And Expression Expression |
  Or Expression Expression |
  Not Expression |
  If Expression Expression Expression |
  Lambda String Expression |
  App Expression Expression |
  Let String Expression Expression |
  Seq Expression Expression |
  While Expression Expression |
  Assign String Expression |
  Skip
  deriving (Eq, Show)

-- 环境
type Environment = [(String, Value)]

-- 基础转换关系
basicTransition :: TransitionRelation
basicTransition (Config expr state) = case expr of
  -- 变量查找
  Var x -> 
    case lookup x state of
      Just v -> Just (Config (LitInt 0) state)  -- 简化：返回单位值
      Nothing -> Just (Config (Error "Undefined variable") state)
  
  -- 字面量
  LitInt n -> Just (Config (LitInt n) state)
  LitBool b -> Just (Config (LitBool b) state)
  
  -- 算术运算
  Add (LitInt n1) (LitInt n2) -> 
    Just (Config (LitInt (n1 + n2)) state)
  
  Sub (LitInt n1) (LitInt n2) -> 
    Just (Config (LitInt (n1 - n2)) state)
  
  Mul (LitInt n1) (LitInt n2) -> 
    Just (Config (LitInt (n1 * n2)) state)
  
  Div (LitInt n1) (LitInt n2) -> 
    if n2 == 0 
    then Just (Config (Error "Division by zero") state)
    else Just (Config (LitInt (n1 `div` n2)) state)
  
  -- 逻辑运算
  And (LitBool b1) (LitBool b2) -> 
    Just (Config (LitBool (b1 && b2)) state)
  
  Or (LitBool b1) (LitBool b2) -> 
    Just (Config (LitBool (b1 || b2)) state)
  
  Not (LitBool b) -> 
    Just (Config (LitBool (not b)) state)
  
  -- 条件语句
  If (LitBool True) e1 _ -> 
    Just (Config e1 state)
  
  If (LitBool False) _ e2 -> 
    Just (Config e2 state)
  
  -- 其他情况不转换
  _ -> Nothing

-- 多步转换
multiStepTransition :: TransitionRelation -> MultiStepTransition
multiStepTransition trans config = 
  let step config' = 
        case trans config' of
          Just next -> config' : step next
          Nothing -> [config']
  in step config

-- 转换到最终状态
transitionToFinal :: TransitionRelation -> Configuration -> Maybe Configuration
transitionToFinal trans config = 
  let steps = multiStepTransition trans config
      finalSteps = filter (\c -> trans c == Nothing) steps
  in case finalSteps of
       (final:_) -> Just final
       [] -> Nothing
```

## 2. 小步语义 (Small-Step Semantics)

### 2.1 小步语义定义

**定义 2.1 (小步语义)**
小步语义通过一系列小的计算步骤来描述程序执行：
$$\frac{\langle e_1, \sigma_1 \rangle \rightarrow \langle e_2, \sigma_2 \rangle}{\langle e_1, \sigma_1 \rangle \rightarrow \langle e_2, \sigma_2 \rangle}$$

**定义 2.2 (求值上下文)**
求值上下文 $E$ 是包含一个洞的表达式：
$$E ::= [\cdot] \mid E + e \mid e + E \mid \text{if } E \text{ then } e_1 \text{ else } e_2$$

**定义 2.3 (小步规则)**
小步规则定义基本计算步骤：

1. **算术运算**：
   $$\frac{\langle n_1 + n_2, \sigma \rangle \rightarrow \langle n_1 + n_2, \sigma \rangle}$$

2. **条件语句**：
   $$\frac{\langle \text{if true then } e_1 \text{ else } e_2, \sigma \rangle \rightarrow \langle e_1, \sigma \rangle}$$
   $$\frac{\langle \text{if false then } e_1 \text{ else } e_2, \sigma \rangle \rightarrow \langle e_2, \sigma \rangle}$$

3. **变量查找**：
   $$\frac{\sigma(x) = v}{\langle x, \sigma \rangle \rightarrow \langle v, \sigma \rangle}$$

### 2.2 Haskell 实现：小步语义

```haskell
-- 求值上下文
data EvaluationContext = 
  Hole |
  AddLeft EvaluationContext Expression |
  AddRight Expression EvaluationContext |
  SubLeft EvaluationContext Expression |
  SubRight Expression EvaluationContext |
  MulLeft EvaluationContext Expression |
  MulRight Expression EvaluationContext |
  DivLeft EvaluationContext Expression |
  DivRight Expression EvaluationContext |
  IfContext EvaluationContext Expression Expression |
  AppLeft EvaluationContext Expression |
  AppRight Expression EvaluationContext |
  LetContext String EvaluationContext Expression

-- 上下文填充
fillContext :: EvaluationContext -> Expression -> Expression
fillContext Hole e = e
fillContext (AddLeft ctx e2) e1 = Add (fillContext ctx e1) e2
fillContext (AddRight e1 ctx) e2 = Add e1 (fillContext ctx e2)
fillContext (SubLeft ctx e2) e1 = Sub (fillContext ctx e1) e2
fillContext (SubRight e1 ctx) e2 = Sub e1 (fillContext ctx e2)
fillContext (MulLeft ctx e2) e1 = Mul (fillContext ctx e1) e2
fillContext (MulRight e1 ctx) e2 = Mul e1 (fillContext ctx e2)
fillContext (DivLeft ctx e2) e1 = Div (fillContext ctx e1) e2
fillContext (DivRight e1 ctx) e2 = Div e1 (fillContext ctx e2)
fillContext (IfContext ctx e1 e2) cond = If (fillContext ctx cond) e1 e2
fillContext (AppLeft ctx e2) e1 = App (fillContext ctx e1) e2
fillContext (AppRight e1 ctx) e2 = App e1 (fillContext ctx e2)
fillContext (LetContext x ctx e2) e1 = Let x (fillContext ctx e1) e2

-- 小步语义
smallStepSemantics :: TransitionRelation
smallStepSemantics (Config expr state) = case expr of
  -- 变量查找
  Var x -> 
    case lookup x state of
      Just (IntVal n) -> Just (Config (LitInt n) state)
      Just (BoolVal b) -> Just (Config (LitBool b) state)
      Just (FuncVal x body env) -> Just (Config (Lambda x body) state)
      _ -> Just (Config (Error "Invalid value") state)
  
  -- 算术运算
  Add (LitInt n1) (LitInt n2) -> 
    Just (Config (LitInt (n1 + n2)) state)
  
  Sub (LitInt n1) (LitInt n2) -> 
    Just (Config (LitInt (n1 - n2)) state)
  
  Mul (LitInt n1) (LitInt n2) -> 
    Just (Config (LitInt (n1 * n2)) state)
  
  Div (LitInt n1) (LitInt n2) -> 
    if n2 == 0 
    then Just (Config (Error "Division by zero") state)
    else Just (Config (LitInt (n1 `div` n2)) state)
  
  -- 逻辑运算
  And (LitBool b1) (LitBool b2) -> 
    Just (Config (LitBool (b1 && b2)) state)
  
  Or (LitBool b1) (LitBool b2) -> 
    Just (Config (LitBool (b1 || b2)) state)
  
  Not (LitBool b) -> 
    Just (Config (LitBool (not b)) state)
  
  -- 条件语句
  If (LitBool True) e1 _ -> 
    Just (Config e1 state)
  
  If (LitBool False) _ e2 -> 
    Just (Config e2 state)
  
  -- 函数应用
  App (Lambda x body) arg -> 
    Just (Config body ((x, valueOf arg state) : state))
  
  -- 变量绑定
  Let x e1 e2 -> 
    Just (Config e2 ((x, valueOf e1 state) : state))
  
  -- 序列
  Seq Skip e2 -> 
    Just (Config e2 state)
  
  -- 赋值
  Assign x (LitInt n) -> 
    Just (Config Skip (updateState state x (IntVal n)))
  
  Assign x (LitBool b) -> 
    Just (Config Skip (updateState state x (BoolVal b)))
  
  -- 循环
  While cond body -> 
    Just (Config (If cond (Seq body (While cond body)) Skip) state)
  
  -- 其他情况不转换
  _ -> Nothing

-- 辅助函数
valueOf :: Expression -> State -> Value
valueOf (LitInt n) _ = IntVal n
valueOf (LitBool b) _ = BoolVal b
valueOf (Var x) state = 
  case lookup x state of
    Just v -> v
    Nothing -> Error "Undefined variable"
valueOf _ _ = Error "Cannot evaluate"

updateState :: State -> String -> Value -> State
updateState state x v = (x, v) : filter ((/= x) . fst) state

-- 小步语义执行
executeSmallStep :: Expression -> State -> [Configuration]
executeSmallStep expr state = 
  multiStepTransition smallStepSemantics (Config expr state)

-- 小步语义示例
smallStepExample :: IO ()
smallStepExample = do
  let expr = Add (LitInt 3) (Mul (LitInt 4) (LitInt 5))
      state = []
      steps = executeSmallStep expr state
  
  putStrLn "Small-step execution:"
  mapM_ print steps
```

## 3. 大步语义 (Big-Step Semantics)

### 3.1 大步语义定义

**定义 3.1 (大步语义)**
大步语义直接描述表达式到最终值的求值：
$$\langle e, \sigma \rangle \Downarrow v$$

**定义 3.2 (大步规则)**
大步规则定义完整求值过程：

1. **字面量**：
   $$\frac{}{\langle n, \sigma \rangle \Downarrow n}$$

2. **变量**：
   $$\frac{\sigma(x) = v}{\langle x, \sigma \rangle \Downarrow v}$$

3. **算术运算**：
   $$\frac{\langle e_1, \sigma \rangle \Downarrow n_1 \quad \langle e_2, \sigma \rangle \Downarrow n_2}{\langle e_1 + e_2, \sigma \rangle \Downarrow n_1 + n_2}$$

4. **条件语句**：
   $$\frac{\langle e_1, \sigma \rangle \Downarrow \text{true} \quad \langle e_2, \sigma \rangle \Downarrow v}{\langle \text{if } e_1 \text{ then } e_2 \text{ else } e_3, \sigma \rangle \Downarrow v}$$

### 3.2 Haskell 实现：大步语义

```haskell
-- 大步语义关系
type BigStepRelation = Expression -> State -> Maybe Value

-- 大步语义
bigStepSemantics :: BigStepRelation
bigStepSemantics expr state = case expr of
  -- 字面量
  LitInt n -> Just (IntVal n)
  LitBool b -> Just (BoolVal b)
  
  -- 变量
  Var x -> lookup x state
  
  -- 算术运算
  Add e1 e2 -> do
    IntVal n1 <- bigStepSemantics e1 state
    IntVal n2 <- bigStepSemantics e2 state
    return (IntVal (n1 + n2))
  
  Sub e1 e2 -> do
    IntVal n1 <- bigStepSemantics e1 state
    IntVal n2 <- bigStepSemantics e2 state
    return (IntVal (n1 - n2))
  
  Mul e1 e2 -> do
    IntVal n1 <- bigStepSemantics e1 state
    IntVal n2 <- bigStepSemantics e2 state
    return (IntVal (n1 * n2))
  
  Div e1 e2 -> do
    IntVal n1 <- bigStepSemantics e1 state
    IntVal n2 <- bigStepSemantics e2 state
    if n2 == 0 
    then Nothing
    else return (IntVal (n1 `div` n2))
  
  -- 逻辑运算
  And e1 e2 -> do
    BoolVal b1 <- bigStepSemantics e1 state
    BoolVal b2 <- bigStepSemantics e2 state
    return (BoolVal (b1 && b2))
  
  Or e1 e2 -> do
    BoolVal b1 <- bigStepSemantics e1 state
    BoolVal b2 <- bigStepSemantics e2 state
    return (BoolVal (b1 || b2))
  
  Not e1 -> do
    BoolVal b <- bigStepSemantics e1 state
    return (BoolVal (not b))
  
  -- 条件语句
  If cond e1 e2 -> do
    BoolVal b <- bigStepSemantics cond state
    if b 
    then bigStepSemantics e1 state
    else bigStepSemantics e2 state
  
  -- 函数抽象
  Lambda x body -> 
    Just (FuncVal x body state)
  
  -- 函数应用
  App func arg -> do
    FuncVal x body env <- bigStepSemantics func state
    argVal <- bigStepSemantics arg state
    bigStepSemantics body ((x, argVal) : env)
  
  -- 变量绑定
  Let x e1 e2 -> do
    v1 <- bigStepSemantics e1 state
    bigStepSemantics e2 ((x, v1) : state)
  
  -- 序列
  Seq e1 e2 -> do
    _ <- bigStepSemantics e1 state
    bigStepSemantics e2 state
  
  -- 赋值
  Assign x e1 -> do
    v <- bigStepSemantics e1 state
    return UnitVal  -- 赋值返回单位值
  
  -- 跳过
  Skip -> Just UnitVal
  
  -- 循环
  While cond body -> 
    case bigStepSemantics cond state of
      Just (BoolVal True) -> do
        _ <- bigStepSemantics body state
        bigStepSemantics (While cond body) state
      Just (BoolVal False) -> Just UnitVal
      _ -> Nothing

-- 大步语义执行
executeBigStep :: Expression -> State -> Maybe Value
executeBigStep = bigStepSemantics

-- 大步语义示例
bigStepExample :: IO ()
bigStepExample = do
  let expr = Add (LitInt 3) (Mul (LitInt 4) (LitInt 5))
      state = []
      result = executeBigStep expr state
  
  putStrLn "Big-step execution:"
  case result of
    Just v -> print v
    Nothing -> putStrLn "Error: Cannot evaluate"
```

## 4. 自然语义 (Natural Semantics)

### 4.1 自然语义定义

**定义 4.1 (自然语义)**
自然语义是结构化操作语义的一种形式，使用推理规则来描述程序执行：
$$\frac{\text{premises}}{\text{conclusion}}$$

**定义 4.2 (推理规则)**
推理规则包括：

1. **公理规则**：无前提的规则
2. **推理规则**：有前提的规则
3. **归纳规则**：递归定义的规则

**定义 4.3 (证明树)**
证明树是推理规则的树形结构，表示语义推导过程。

### 4.2 Haskell 实现：自然语义

```haskell
-- 推理规则
data InferenceRule = 
  Axiom String |
  Rule String [InferenceRule]

-- 证明树
data ProofTree = 
  Leaf String |
  Node String [ProofTree]

-- 自然语义规则
naturalSemantics :: Expression -> State -> Maybe (Value, ProofTree)
naturalSemantics expr state = case expr of
  -- 公理规则
  LitInt n -> 
    Just (IntVal n, Leaf "LitInt")
  
  LitBool b -> 
    Just (BoolVal b, Leaf "LitBool")
  
  Var x -> 
    case lookup x state of
      Just v -> Just (v, Leaf "Var")
      Nothing -> Nothing
  
  -- 推理规则
  Add e1 e2 -> do
    (IntVal n1, proof1) <- naturalSemantics e1 state
    (IntVal n2, proof2) <- naturalSemantics e2 state
    let proof = Node "Add" [proof1, proof2]
    return (IntVal (n1 + n2), proof)
  
  Sub e1 e2 -> do
    (IntVal n1, proof1) <- naturalSemantics e1 state
    (IntVal n2, proof2) <- naturalSemantics e2 state
    let proof = Node "Sub" [proof1, proof2]
    return (IntVal (n1 - n2), proof)
  
  Mul e1 e2 -> do
    (IntVal n1, proof1) <- naturalSemantics e1 state
    (IntVal n2, proof2) <- naturalSemantics e2 state
    let proof = Node "Mul" [proof1, proof2]
    return (IntVal (n1 * n2), proof)
  
  Div e1 e2 -> do
    (IntVal n1, proof1) <- naturalSemantics e1 state
    (IntVal n2, proof2) <- naturalSemantics e2 state
    if n2 == 0 
    then Nothing
    else do
      let proof = Node "Div" [proof1, proof2]
      return (IntVal (n1 `div` n2), proof)
  
  And e1 e2 -> do
    (BoolVal b1, proof1) <- naturalSemantics e1 state
    (BoolVal b2, proof2) <- naturalSemantics e2 state
    let proof = Node "And" [proof1, proof2]
    return (BoolVal (b1 && b2), proof)
  
  Or e1 e2 -> do
    (BoolVal b1, proof1) <- naturalSemantics e1 state
    (BoolVal b2, proof2) <- naturalSemantics e2 state
    let proof = Node "Or" [proof1, proof2]
    return (BoolVal (b1 || b2), proof)
  
  Not e1 -> do
    (BoolVal b, proof1) <- naturalSemantics e1 state
    let proof = Node "Not" [proof1]
    return (BoolVal (not b), proof)
  
  If cond e1 e2 -> do
    (BoolVal b, proofCond) <- naturalSemantics cond state
    if b 
    then do
      (v, proof1) <- naturalSemantics e1 state
      let proof = Node "If-True" [proofCond, proof1]
      return (v, proof)
    else do
      (v, proof2) <- naturalSemantics e2 state
      let proof = Node "If-False" [proofCond, proof2]
      return (v, proof)
  
  Lambda x body -> 
    let proof = Leaf "Lambda"
    in Just (FuncVal x body state, proof)
  
  App func arg -> do
    (FuncVal x body env, proofFunc) <- naturalSemantics func state
    (argVal, proofArg) <- naturalSemantics arg state
    (result, proofBody) <- naturalSemantics body ((x, argVal) : env)
    let proof = Node "App" [proofFunc, proofArg, proofBody]
    return (result, proof)
  
  Let x e1 e2 -> do
    (v1, proof1) <- naturalSemantics e1 state
    (v2, proof2) <- naturalSemantics e2 ((x, v1) : state)
    let proof = Node "Let" [proof1, proof2]
    return (v2, proof)
  
  Seq e1 e2 -> do
    (_, proof1) <- naturalSemantics e1 state
    (v2, proof2) <- naturalSemantics e2 state
    let proof = Node "Seq" [proof1, proof2]
    return (v2, proof)
  
  Assign x e1 -> do
    (v, proof1) <- naturalSemantics e1 state
    let proof = Node "Assign" [proof1]
    return (UnitVal, proof)
  
  Skip -> 
    Just (UnitVal, Leaf "Skip")
  
  While cond body -> 
    case naturalSemantics cond state of
      Just (BoolVal True, proofCond) -> do
        (_, proofBody) <- naturalSemantics body state
        (result, proofWhile) <- naturalSemantics (While cond body) state
        let proof = Node "While-True" [proofCond, proofBody, proofWhile]
        return (result, proof)
      Just (BoolVal False, proofCond) -> 
        let proof = Node "While-False" [proofCond]
        in Just (UnitVal, proof)
      _ -> Nothing

-- 证明树打印
printProofTree :: ProofTree -> String
printProofTree (Leaf rule) = rule
printProofTree (Node rule children) = 
  rule ++ "(" ++ intercalate ", " (map printProofTree children) ++ ")"

-- 自然语义示例
naturalSemanticsExample :: IO ()
naturalSemanticsExample = do
  let expr = Add (LitInt 3) (Mul (LitInt 4) (LitInt 5))
      state = []
      result = naturalSemantics expr state
  
  putStrLn "Natural semantics execution:"
  case result of
    Just (v, proof) -> do
      putStrLn $ "Result: " ++ show v
      putStrLn $ "Proof: " ++ printProofTree proof
    Nothing -> putStrLn "Error: Cannot evaluate"
```

## 5. 抽象机器语义

### 5.1 抽象机器

**定义 5.1 (抽象机器)**
抽象机器是程序执行的形式化模型，包含：

1. **状态**：机器当前状态
2. **指令**：执行的基本操作
3. **转换函数**：状态转换规则

**定义 5.2 (栈机器)**
栈机器使用栈来存储中间结果：
$$\langle \text{code}, \text{stack}, \text{env} \rangle \rightarrow \langle \text{code}', \text{stack}', \text{env}' \rangle$$

**定义 5.3 (寄存器机器)**
寄存器机器使用寄存器来存储值：
$$\langle \text{code}, \text{registers}, \text{memory} \rangle \rightarrow \langle \text{code}', \text{registers}', \text{memory}' \rangle$$

### 5.2 Haskell 实现：抽象机器语义

```haskell
-- 指令
data Instruction = 
  PushInt Integer |
  PushBool Bool |
  Load String |
  Store String |
  Add |
  Sub |
  Mul |
  Div |
  And |
  Or |
  Not |
  Jump Integer |
  JumpIfTrue Integer |
  JumpIfFalse Integer |
  Call |
  Return |
  Halt

-- 栈机器状态
data StackMachineState = StackState {
  code :: [Instruction],
  stack :: [Value],
  environment :: Environment,
  programCounter :: Integer
}

-- 栈机器语义
stackMachineSemantics :: StackMachineState -> Maybe StackMachineState
stackMachineSemantics (StackState code stack env pc) = case code of
  [] -> Nothing
  
  (PushInt n : rest) -> 
    Just (StackState rest (IntVal n : stack) env (pc + 1))
  
  (PushBool b : rest) -> 
    Just (StackState rest (BoolVal b : stack) env (pc + 1))
  
  (Load x : rest) -> 
    case lookup x env of
      Just v -> Just (StackState rest (v : stack) env (pc + 1))
      Nothing -> Nothing
  
  (Store x : rest) -> 
    case stack of
      (v : restStack) -> 
        Just (StackState rest restStack ((x, v) : env) (pc + 1))
      [] -> Nothing
  
  (Add : rest) -> 
    case stack of
      (IntVal n2 : IntVal n1 : restStack) -> 
        Just (StackState rest (IntVal (n1 + n2) : restStack) env (pc + 1))
      _ -> Nothing
  
  (Sub : rest) -> 
    case stack of
      (IntVal n2 : IntVal n1 : restStack) -> 
        Just (StackState rest (IntVal (n1 - n2) : restStack) env (pc + 1))
      _ -> Nothing
  
  (Mul : rest) -> 
    case stack of
      (IntVal n2 : IntVal n1 : restStack) -> 
        Just (StackState rest (IntVal (n1 * n2) : restStack) env (pc + 1))
      _ -> Nothing
  
  (Div : rest) -> 
    case stack of
      (IntVal n2 : IntVal n1 : restStack) -> 
        if n2 == 0 
        then Nothing
        else Just (StackState rest (IntVal (n1 `div` n2) : restStack) env (pc + 1))
      _ -> Nothing
  
  (And : rest) -> 
    case stack of
      (BoolVal b2 : BoolVal b1 : restStack) -> 
        Just (StackState rest (BoolVal (b1 && b2) : restStack) env (pc + 1))
      _ -> Nothing
  
  (Or : rest) -> 
    case stack of
      (BoolVal b2 : BoolVal b1 : restStack) -> 
        Just (StackState rest (BoolVal (b1 || b2) : restStack) env (pc + 1))
      _ -> Nothing
  
  (Not : rest) -> 
    case stack of
      (BoolVal b : restStack) -> 
        Just (StackState rest (BoolVal (not b) : restStack) env (pc + 1))
      _ -> Nothing
  
  (Jump offset : rest) -> 
    Just (StackState rest stack env (pc + offset))
  
  (JumpIfTrue offset : rest) -> 
    case stack of
      (BoolVal True : restStack) -> 
        Just (StackState rest restStack env (pc + offset))
      (BoolVal False : restStack) -> 
        Just (StackState rest restStack env (pc + 1))
      _ -> Nothing
  
  (JumpIfFalse offset : rest) -> 
    case stack of
      (BoolVal False : restStack) -> 
        Just (StackState rest restStack env (pc + offset))
      (BoolVal True : restStack) -> 
        Just (StackState rest restStack env (pc + 1))
      _ -> Nothing
  
  (Halt : _) -> 
    Nothing

-- 栈机器执行
executeStackMachine :: [Instruction] -> Environment -> [StackMachineState]
executeStackMachine code env = 
  let initialState = StackState code [] env 0
      step state = 
        case stackMachineSemantics state of
          Just next -> state : step next
          Nothing -> [state]
  in step initialState

-- 表达式到指令编译
compileExpression :: Expression -> [Instruction]
compileExpression expr = case expr of
  LitInt n -> [PushInt n]
  LitBool b -> [PushBool b]
  Var x -> [Load x]
  Add e1 e2 -> compileExpression e1 ++ compileExpression e2 ++ [Add]
  Sub e1 e2 -> compileExpression e1 ++ compileExpression e2 ++ [Sub]
  Mul e1 e2 -> compileExpression e1 ++ compileExpression e2 ++ [Mul]
  Div e1 e2 -> compileExpression e1 ++ compileExpression e2 ++ [Div]
  And e1 e2 -> compileExpression e1 ++ compileExpression e2 ++ [And]
  Or e1 e2 -> compileExpression e1 ++ compileExpression e2 ++ [Or]
  Not e1 -> compileExpression e1 ++ [Not]
  If cond e1 e2 -> 
    let condCode = compileExpression cond
        e1Code = compileExpression e1
        e2Code = compileExpression e2
        jumpOverE1 = [JumpIfFalse (fromIntegral (length e1Code + 1))]
        jumpOverE2 = [Jump (fromIntegral (length e2Code))]
    in condCode ++ jumpOverE1 ++ e1Code ++ jumpOverE2 ++ e2Code
  _ -> [Halt]  -- 简化实现

-- 抽象机器示例
abstractMachineExample :: IO ()
abstractMachineExample = do
  let expr = Add (LitInt 3) (Mul (LitInt 4) (LitInt 5))
      code = compileExpression expr
      env = []
      states = executeStackMachine code env
  
  putStrLn "Abstract machine execution:"
  mapM_ print states
```

## 6. 并发操作语义

### 6.1 并发配置

**定义 6.1 (并发配置)**
并发配置包含多个进程的状态：
$$\langle P_1 \parallel P_2 \parallel \cdots \parallel P_n, \sigma \rangle$$

**定义 6.2 (并发转换)**
并发转换允许任意进程执行：
$$\frac{\langle P_i, \sigma \rangle \rightarrow \langle P_i', \sigma' \rangle}{\langle P_1 \parallel \cdots \parallel P_i \parallel \cdots \parallel P_n, \sigma \rangle \rightarrow \langle P_1 \parallel \cdots \parallel P_i' \parallel \cdots \parallel P_n, \sigma' \rangle}$$

**定义 6.3 (同步通信)**
同步通信通过消息传递实现：
$$\frac{\langle P_1, \sigma \rangle \rightarrow \langle P_1', \sigma' \rangle \quad \langle P_2, \sigma \rangle \rightarrow \langle P_2', \sigma' \rangle}{\langle P_1 \parallel P_2, \sigma \rangle \rightarrow \langle P_1' \parallel P_2', \sigma' \rangle}$$

### 6.2 Haskell 实现：并发操作语义

```haskell
-- 进程
data Process = 
  ProcessSkip |
  ProcessAssign String Expression |
  ProcessSeq Process Process |
  ProcessPar Process Process |
  ProcessIf Expression Process Process |
  ProcessWhile Expression Process |
  ProcessSend ProcessId ProcessId Expression |
  ProcessReceive ProcessId ProcessId String

-- 进程标识符
type ProcessId = Integer

-- 并发配置
data ConcurrentConfiguration = ConcurrentConfig {
  processes :: [(ProcessId, Process)],
  sharedState :: State,
  messages :: [(ProcessId, ProcessId, Value)]
}

-- 并发操作语义
concurrentOperationalSemantics :: ConcurrentConfiguration -> Maybe ConcurrentConfiguration
concurrentOperationalSemantics config = 
  let processSteps = concatMap (stepProcess config) (processes config)
  in case processSteps of
       (step:_) -> Just step
       [] -> Nothing

-- 进程步骤
stepProcess :: ConcurrentConfiguration -> (ProcessId, Process) -> [ConcurrentConfiguration]
stepProcess config (pid, proc) = case proc of
  ProcessSkip -> []
  
  ProcessAssign x e -> 
    case bigStepSemantics e (sharedState config) of
      Just v -> 
        let newState = updateState (sharedState config) x v
            newProcesses = updateProcess pid ProcessSkip (processes config)
        in [config { processes = newProcesses, sharedState = newState }]
      Nothing -> []
  
  ProcessSeq p1 p2 -> 
    case p1 of
      ProcessSkip -> 
        let newProcesses = updateProcess pid p2 (processes config)
        in [config { processes = newProcesses }]
      _ -> 
        let p1Steps = stepProcess config (pid, p1)
        in map (\c -> c { processes = updateProcess pid (ProcessSeq (getProcess pid c) p2) (processes c) }) p1Steps
  
  ProcessPar p1 p2 -> 
    let p1Steps = stepProcess config (pid, p1)
        p2Steps = stepProcess config (pid, p2)
    in p1Steps ++ p2Steps
  
  ProcessIf cond p1 p2 -> 
    case bigStepSemantics cond (sharedState config) of
      Just (BoolVal True) -> 
        let newProcesses = updateProcess pid p1 (processes config)
        in [config { processes = newProcesses }]
      Just (BoolVal False) -> 
        let newProcesses = updateProcess pid p2 (processes config)
        in [config { processes = newProcesses }]
      _ -> []
  
  ProcessWhile cond body -> 
    case bigStepSemantics cond (sharedState config) of
      Just (BoolVal True) -> 
        let newProcesses = updateProcess pid (ProcessSeq body (ProcessWhile cond body)) (processes config)
        in [config { processes = newProcesses }]
      Just (BoolVal False) -> 
        let newProcesses = updateProcess pid ProcessSkip (processes config)
        in [config { processes = newProcesses }]
      _ -> []
  
  ProcessSend fromPid toPid e -> 
    case bigStepSemantics e (sharedState config) of
      Just v -> 
        let newMessages = (fromPid, toPid, v) : messages config
            newProcesses = updateProcess pid ProcessSkip (processes config)
        in [config { processes = newProcesses, messages = newMessages }]
      Nothing -> []
  
  ProcessReceive fromPid toPid x -> 
    let matchingMessages = filter (\(f, t, _) -> f == fromPid && t == toPid) (messages config)
    in case matchingMessages of
         ((_, _, v) : _) -> 
           let newState = updateState (sharedState config) x v
               newMessages = filter (/= head matchingMessages) (messages config)
               newProcesses = updateProcess pid ProcessSkip (processes config)
           in [config { processes = newProcesses, sharedState = newState, messages = newMessages }]
         [] -> []

-- 辅助函数
updateProcess :: ProcessId -> Process -> [(ProcessId, Process)] -> [(ProcessId, Process)]
updateProcess pid proc procs = 
  (pid, proc) : filter ((/= pid) . fst) procs

getProcess :: ProcessId -> ConcurrentConfiguration -> Process
getProcess pid config = 
  case lookup pid (processes config) of
    Just proc -> proc
    Nothing -> ProcessSkip

-- 并发执行
executeConcurrent :: ConcurrentConfiguration -> [ConcurrentConfiguration]
executeConcurrent config = 
  let step config' = 
        case concurrentOperationalSemantics config' of
          Just next -> config' : step next
          Nothing -> [config']
  in step config

-- 并发示例
concurrentExample :: IO ()
concurrentExample = do
  let proc1 = ProcessAssign "x" (LitInt 5)
      proc2 = ProcessAssign "y" (LitInt 10)
      config = ConcurrentConfig {
        processes = [(1, proc1), (2, proc2)],
        sharedState = [],
        messages = []
      }
      states = executeConcurrent config
  
  putStrLn "Concurrent execution:"
  mapM_ print states
```

## 7. 高级主题

### 7.1 操作语义与指称语义的关系

**定理 7.1 (语义等价性)**
对于确定性程序，操作语义和指称语义是等价的：
$$\langle e, \sigma \rangle \rightarrow^* \langle v, \sigma' \rangle \Leftrightarrow \llbracket e \rrbracket \sigma = v$$

**证明：** 通过结构归纳：

1. **基础情况**：字面量和变量
2. **归纳步骤**：复合表达式
3. **终止性**：确保语义定义的一致性

### 7.2 操作语义与类型系统

**定义 7.1 (类型化操作语义)**
类型化操作语义结合类型检查和操作语义：
$$\frac{\Gamma \vdash e : \tau \quad \langle e, \sigma \rangle \rightarrow \langle e', \sigma' \rangle}{\Gamma \vdash e' : \tau}$$

**定理 7.2 (类型保持)**
操作语义保持类型：
如果 $\Gamma \vdash e : \tau$ 且 $\langle e, \sigma \rangle \rightarrow^* \langle v, \sigma' \rangle$，则 $\Gamma \vdash v : \tau$。

```haskell
-- 类型化操作语义
typedOperationalSemantics :: Expression -> Type -> State -> Maybe (Value, State)
typedOperationalSemantics expr typ state = do
  -- 类型检查
  guard (typeCheck expr typ)
  
  -- 操作语义执行
  case bigStepSemantics expr state of
    Just v -> 
      -- 类型验证
      guard (typeCompatible v typ)
      return (v, state)
    Nothing -> Nothing

-- 类型检查
typeCheck :: Expression -> Type -> Bool
typeCheck (LitInt _) IntType = True
typeCheck (LitBool _) BoolType = True
typeCheck (Var x) typ = True  -- 简化：假设所有变量都有正确类型
typeCheck (Add e1 e2) IntType = 
  typeCheck e1 IntType && typeCheck e2 IntType
typeCheck (Sub e1 e2) IntType = 
  typeCheck e1 IntType && typeCheck e2 IntType
typeCheck (Mul e1 e2) IntType = 
  typeCheck e1 IntType && typeCheck e2 IntType
typeCheck (Div e1 e2) IntType = 
  typeCheck e1 IntType && typeCheck e2 IntType
typeCheck (And e1 e2) BoolType = 
  typeCheck e1 BoolType && typeCheck e2 BoolType
typeCheck (Or e1 e2) BoolType = 
  typeCheck e1 BoolType && typeCheck e2 BoolType
typeCheck (Not e1) BoolType = 
  typeCheck e1 BoolType
typeCheck (If cond e1 e2) typ = 
  typeCheck cond BoolType && typeCheck e1 typ && typeCheck e2 typ
typeCheck _ _ = False

-- 类型兼容性
typeCompatible :: Value -> Type -> Bool
typeCompatible (IntVal _) IntType = True
typeCompatible (BoolVal _) BoolType = True
typeCompatible (FuncVal _ _ _) (FunctionType _ _) = True
typeCompatible _ _ = False
```

## 8. 总结

操作语义为程序语言提供了执行行为的精确描述。通过不同的语义风格（小步、大步、自然语义），它能够：

1. **精确描述**：程序执行的每个步骤
2. **形式化分析**：程序行为的数学性质
3. **实现指导**：为解释器和编译器提供规范
4. **验证基础**：程序正确性证明的基础

操作语义在程序语言理论、编译器设计、程序验证等领域得到了广泛应用，为构建可靠的软件系统提供了理论基础。

---

**相关文档：**

- [[001-Linear-Type-Theory]] - 线性类型理论
- [[002-Affine-Type-Theory]] - 仿射类型理论
- [[003-Temporal-Type-Theory]] - 时态类型理论
- [[004-Quantum-Type-Theory]] - 量子类型理论
- [[005-Denotational-Semantics]] - 指称语义
- [[007-Axiomatic-Semantics]] - 公理语义
- [[008-Category-Semantics]] - 范畴语义
- [[haskell/02-Type-System]] - Haskell 类型系统

**参考文献：**

1. Plotkin, G. D. (1981). A structural approach to operational semantics. Technical report, DAIMI FN-19, Computer Science Department, Aarhus University.
2. Kahn, G. (1987). Natural semantics. In International Symposium on Theoretical Aspects of Computer Software (pp. 22-39). Springer.
3. Milner, R. (1989). Communication and concurrency. Prentice-Hall.
4. Pierce, B. C. (2002). Types and programming languages. MIT press.
