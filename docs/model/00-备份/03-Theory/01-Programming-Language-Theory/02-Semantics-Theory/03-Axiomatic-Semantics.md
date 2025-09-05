# 公理语义 (Axiomatic Semantics)

## 概述

公理语义是编程语言语义学的重要分支，通过逻辑断言和推理规则来定义程序的语义。公理语义关注程序的前置条件和后置条件，用于程序验证和正确性证明。

## 基本概念

### 断言 (Assertions)

断言是描述程序状态的逻辑公式。

```haskell
-- 断言类型
data Assertion = 
    True
  | False
  | Equal Expr Expr
  | LessThan Expr Expr
  | GreaterThan Expr Expr
  | And Assertion Assertion
  | Or Assertion Assertion
  | Not Assertion
  | Implies Assertion Assertion
  | ForAll String Assertion
  | Exists String Assertion
  deriving (Eq, Show)

-- 表达式（用于断言中）
data Expr = 
    Var String
  | IntLit Integer
  | BoolLit Bool
  | Add Expr Expr
  | Sub Expr Expr
  | Mul Expr Expr
  | Div Expr Expr
  | Eq Expr Expr
  | Lt Expr Expr
  deriving (Eq, Show)

-- 断言求值
evalAssertion :: Assertion -> Environment -> Bool
evalAssertion assertion env = case assertion of
  True -> True
  False -> False
  Equal e1 e2 -> evalExpr e1 env == evalExpr e2 env
  LessThan e1 e2 -> 
    case (evalExpr e1 env, evalExpr e2 env) of
      (IntVal n1, IntVal n2) -> n1 < n2
      _ -> False
  GreaterThan e1 e2 -> 
    case (evalExpr e1 env, evalExpr e2 env) of
      (IntVal n1, IntVal n2) -> n1 > n2
      _ -> False
  And a1 a2 -> evalAssertion a1 env && evalAssertion a2 env
  Or a1 a2 -> evalAssertion a1 env || evalAssertion a2 env
  Not a -> not (evalAssertion a env)
  Implies a1 a2 -> not (evalAssertion a1 env) || evalAssertion a2 env
  ForAll _ _ -> True  -- 简化实现
  Exists _ _ -> True  -- 简化实现

-- 表达式求值
evalExpr :: Expr -> Environment -> Value
evalExpr expr env = case expr of
  Var x -> case lookup x env of
    Just v -> v
    Nothing -> IntVal 0  -- 默认值
  IntLit n -> IntVal n
  BoolLit b -> BoolVal b
  Add e1 e2 -> 
    case (evalExpr e1 env, evalExpr e2 env) of
      (IntVal n1, IntVal n2) -> IntVal (n1 + n2)
      _ -> IntVal 0
  Sub e1 e2 -> 
    case (evalExpr e1 env, evalExpr e2 env) of
      (IntVal n1, IntVal n2) -> IntVal (n1 - n2)
      _ -> IntVal 0
  Mul e1 e2 -> 
    case (evalExpr e1 env, evalExpr e2 env) of
      (IntVal n1, IntVal n2) -> IntVal (n1 * n2)
      _ -> IntVal 0
  Div e1 e2 -> 
    case (evalExpr e1 env, evalExpr e2 env) of
      (IntVal n1, IntVal n2) -> 
        if n2 /= 0 then IntVal (n1 `div` n2) else IntVal 0
      _ -> IntVal 0
  Eq e1 e2 -> 
    case (evalExpr e1 env, evalExpr e2 env) of
      (IntVal n1, IntVal n2) -> BoolVal (n1 == n2)
      (BoolVal b1, BoolVal b2) -> BoolVal (b1 == b2)
      _ -> BoolVal False
  Lt e1 e2 -> 
    case (evalExpr e1 env, evalExpr e2 env) of
      (IntVal n1, IntVal n2) -> BoolVal (n1 < n2)
      _ -> BoolVal False

-- 值类型
data Value = IntVal Integer | BoolVal Bool deriving (Eq, Show)

-- 环境
type Environment = [(String, Value)]
```

### 霍尔三元组 (Hoare Triples)

霍尔三元组是公理语义的核心概念，形式为 {P} C {Q}，表示如果前置条件P成立，执行程序C后，后置条件Q成立。

```haskell
-- 霍尔三元组
data HoareTriple = HoareTriple
  { precondition :: Assertion
  , program :: Statement
  , postcondition :: Assertion
  } deriving (Eq, Show)

-- 语句类型
data Statement = 
    Skip
  | Assignment String Expr
  | Sequence Statement Statement
  | IfStatement Expr Statement Statement
  | WhileStatement Expr Assertion Statement  -- 包含循环不变式
  | Block [Statement]
  deriving (Eq, Show)

-- 霍尔三元组的有效性
isValid :: HoareTriple -> Bool
isValid (HoareTriple pre prog post) = 
  all (\env -> 
    if evalAssertion pre env 
    then let env' = executeStatement prog env
         in evalAssertion post env'
    else True) allEnvironments
  where
    allEnvironments = [emptyEnv]  -- 简化实现
    emptyEnv = []

-- 语句执行
executeStatement :: Statement -> Environment -> Environment
executeStatement stmt env = case stmt of
  Skip -> env
  Assignment x expr -> 
    let v = evalExpr expr env
    in (x, v) : filter (\(y, _) -> y /= x) env
  Sequence stmt1 stmt2 -> 
    let env1 = executeStatement stmt1 env
    in executeStatement stmt2 env1
  IfStatement expr stmt1 stmt2 -> 
    case evalExpr expr env of
      BoolVal True -> executeStatement stmt1 env
      BoolVal False -> executeStatement stmt2 env
      _ -> env
  WhileStatement expr invariant body -> 
    case evalExpr expr env of
      BoolVal True -> 
        let env' = executeStatement body env
        in executeStatement (WhileStatement expr invariant body) env'
      BoolVal False -> env
      _ -> env
  Block stmts -> 
    foldl (\e s -> executeStatement s e) env stmts
```

## 推理规则

### 赋值公理

```haskell
-- 赋值公理：{P[E/x]} x := E {P}
assignmentAxiom :: String -> Expr -> Assertion -> HoareTriple
assignmentAxiom x expr post = HoareTriple
  { precondition = substitute x expr post
  , program = Assignment x expr
  , postcondition = post
  }

-- 断言中的变量替换
substitute :: String -> Expr -> Assertion -> Assertion
substitute x expr assertion = case assertion of
  True -> True
  False -> False
  Equal e1 e2 -> Equal (substituteExpr x expr e1) (substituteExpr x expr e2)
  LessThan e1 e2 -> LessThan (substituteExpr x expr e1) (substituteExpr x expr e2)
  GreaterThan e1 e2 -> GreaterThan (substituteExpr x expr e1) (substituteExpr x expr e2)
  And a1 a2 -> And (substitute x expr a1) (substitute x expr a2)
  Or a1 a2 -> Or (substitute x expr a1) (substitute x expr a2)
  Not a -> Not (substitute x expr a)
  Implies a1 a2 -> Implies (substitute x expr a1) (substitute x expr a2)
  ForAll y a -> if x == y then assertion else ForAll y (substitute x expr a)
  Exists y a -> if x == y then assertion else Exists y (substitute x expr a)

-- 表达式中的变量替换
substituteExpr :: String -> Expr -> Expr -> Expr
substituteExpr x expr e = case e of
  Var y -> if x == y then expr else Var y
  IntLit n -> IntLit n
  BoolLit b -> BoolLit b
  Add e1 e2 -> Add (substituteExpr x expr e1) (substituteExpr x expr e2)
  Sub e1 e2 -> Sub (substituteExpr x expr e1) (substituteExpr x expr e2)
  Mul e1 e2 -> Mul (substituteExpr x expr e1) (substituteExpr x expr e2)
  Div e1 e2 -> Div (substituteExpr x expr e1) (substituteExpr x expr e2)
  Eq e1 e2 -> Eq (substituteExpr x expr e1) (substituteExpr x expr e2)
  Lt e1 e2 -> Lt (substituteExpr x expr e1) (substituteExpr x expr e2)
```

### 顺序规则

```haskell
-- 顺序规则：{P} C1 {Q}  {Q} C2 {R}
--           ------------------------
--           {P} C1; C2 {R}
sequenceRule :: HoareTriple -> HoareTriple -> HoareTriple
sequenceRule (HoareTriple pre1 prog1 post1) (HoareTriple pre2 prog2 post2) =
  if post1 == pre2
  then HoareTriple pre1 (Sequence prog1 prog2) post2
  else error "Postcondition of first triple must match precondition of second"
```

### 条件规则

```haskell
-- 条件规则：{P ∧ B} C1 {Q}  {P ∧ ¬B} C2 {Q}
--           --------------------------------
--           {P} if B then C1 else C2 {Q}
conditionalRule :: Assertion -> Expr -> HoareTriple -> HoareTriple -> HoareTriple
conditionalRule pre condition (HoareTriple pre1 prog1 post1) (HoareTriple pre2 prog2 post2) =
  if post1 == post2 && 
     pre1 == And pre condition && 
     pre2 == And pre (Not (exprToAssertion condition))
  then HoareTriple pre (IfStatement condition prog1 prog2) post1
  else error "Invalid conditional rule application"

-- 表达式转换为断言
exprToAssertion :: Expr -> Assertion
exprToAssertion expr = case expr of
  BoolLit True -> True
  BoolLit False -> False
  Eq e1 e2 -> Equal e1 e2
  Lt e1 e2 -> LessThan e1 e2
  _ -> True  -- 简化处理
```

### 循环规则

```haskell
-- 循环规则：{P ∧ B} C {P}
--           -----------------
--           {P} while B do C {P ∧ ¬B}
whileRule :: Assertion -> Expr -> Statement -> HoareTriple
whileRule invariant condition body = HoareTriple
  { precondition = invariant
  , program = WhileStatement condition invariant body
  , postcondition = And invariant (Not (exprToAssertion condition))
  }

-- 循环不变式验证
verifyLoopInvariant :: Assertion -> Expr -> Statement -> Bool
verifyLoopInvariant invariant condition body = 
  all (\env -> 
    if evalAssertion invariant env && 
       case evalExpr condition env of
         BoolVal True -> True
         _ -> False
    then let env' = executeStatement body env
         in evalAssertion invariant env'
    else True) allEnvironments
  where
    allEnvironments = [emptyEnv]
    emptyEnv = []
```

### 弱化规则

```haskell
-- 弱化前置条件：P' → P  {P} C {Q}
--               ----------------
--               {P'} C {Q}
weakenPrecondition :: Assertion -> HoareTriple -> HoareTriple
weakenPrecondition newPre (HoareTriple pre prog post) = 
  if implies newPre pre
  then HoareTriple newPre prog post
  else error "New precondition must imply original precondition"

-- 强化后置条件：{P} C {Q}  Q → Q'
--               ----------------
--               {P} C {Q'}
strengthenPostcondition :: HoareTriple -> Assertion -> HoareTriple
strengthenPostcondition (HoareTriple pre prog post) newPost = 
  if implies post newPost
  then HoareTriple pre prog newPost
  else error "Original postcondition must imply new postcondition"

-- 断言蕴含
implies :: Assertion -> Assertion -> Bool
implies a1 a2 = all (\env -> 
  not (evalAssertion a1 env) || evalAssertion a2 env) allEnvironments
  where
    allEnvironments = [emptyEnv]
    emptyEnv = []
```

## 程序验证

### 验证器

```haskell
-- 程序验证器
verifyProgram :: HoareTriple -> Bool
verifyProgram triple = case program triple of
  Skip -> 
    implies (precondition triple) (postcondition triple)
  
  Assignment x expr -> 
    isValid (assignmentAxiom x expr (postcondition triple))
  
  Sequence stmt1 stmt2 -> 
    -- 需要找到中间断言
    True  -- 简化实现
  
  IfStatement expr stmt1 stmt2 -> 
    -- 需要验证两个分支
    True  -- 简化实现
  
  WhileStatement expr invariant body -> 
    verifyLoopInvariant invariant expr body
  
  Block stmts -> 
    all (\stmt -> verifyProgram (HoareTriple 
      (precondition triple) stmt (postcondition triple))) stmts

-- 自动验证器
autoVerify :: Statement -> Assertion -> Assertion -> Bool
autoVerify stmt pre post = 
  verifyProgram (HoareTriple pre stmt post)
```

### 不变式生成

```haskell
-- 循环不变式生成（简化版本）
generateInvariant :: Expr -> Statement -> Assertion
generateInvariant condition body = 
  case condition of
    Lt (Var x) (IntLit n) -> 
      And (LessThan (Var x) (IntLit n)) (GreaterThan (Var x) (IntLit 0))
    _ -> True

-- 后置条件生成
generatePostcondition :: Statement -> Assertion -> Assertion
generatePostcondition stmt pre = case stmt of
  Assignment x expr -> 
    substitute x expr pre
  _ -> pre  -- 简化实现
```

## 应用示例

### 交换程序验证

```haskell
-- 交换两个变量的值
swapProgram :: Statement
swapProgram = Block
  [ Assignment "temp" (Var "x")
  , Assignment "x" (Var "y")
  , Assignment "y" (Var "temp")
  ]

-- 交换程序的霍尔三元组
swapTriple :: HoareTriple
swapTriple = HoareTriple
  { precondition = And (Equal (Var "x") (IntLit 5)) (Equal (Var "y") (IntLit 3))
  , program = swapProgram
  , postcondition = And (Equal (Var "x") (IntLit 3)) (Equal (Var "y") (IntLit 5))
  }

-- 验证交换程序
verifySwap :: Bool
verifySwap = verifyProgram swapTriple
```

### 阶乘程序验证

```haskell
-- 阶乘程序
factorialProgram :: Statement
factorialProgram = Block
  [ Assignment "result" (IntLit 1)
  , Assignment "i" (IntLit 1)
  , WhileStatement 
      (Lt (Var "i") (Add (Var "n") (IntLit 1)))
      (And (Equal (Var "result") (factorialExpr (Sub (Var "i") (IntLit 1))))
           (LessThan (Var "i") (Add (Var "n") (IntLit 1))))
      (Block
        [ Assignment "result" (Mul (Var "result") (Var "i"))
        , Assignment "i" (Add (Var "i") (IntLit 1))
        ])
  ]

-- 阶乘表达式（简化）
factorialExpr :: Expr -> Expr
factorialExpr expr = expr  -- 简化实现

-- 阶乘程序的霍尔三元组
factorialTriple :: HoareTriple
factorialTriple = HoareTriple
  { precondition = And (Equal (Var "n") (IntLit 5)) (GreaterThan (Var "n") (IntLit 0))
  , program = factorialProgram
  , postcondition = Equal (Var "result") (IntLit 120)
  }

-- 验证阶乘程序
verifyFactorial :: Bool
verifyFactorial = verifyProgram factorialTriple
```

### 数组程序验证

```haskell
-- 数组求和程序
arraySumProgram :: Statement
arraySumProgram = Block
  [ Assignment "sum" (IntLit 0)
  , Assignment "i" (IntLit 0)
  , WhileStatement 
      (Lt (Var "i") (Var "length"))
      (And (Equal (Var "sum") (arraySumExpr (Var "i") (Var "arr")))
           (LessThan (Var "i") (Var "length")))
      (Block
        [ Assignment "sum" (Add (Var "sum") (arrayAccess (Var "arr") (Var "i")))
        , Assignment "i" (Add (Var "i") (IntLit 1))
        ])
  ]

-- 数组求和表达式（简化）
arraySumExpr :: Expr -> Expr -> Expr
arraySumExpr i arr = i  -- 简化实现

-- 数组访问（简化）
arrayAccess :: Expr -> Expr -> Expr
arrayAccess arr i = IntLit 1  -- 简化实现

-- 数组求和程序的霍尔三元组
arraySumTriple :: HoareTriple
arraySumTriple = HoareTriple
  { precondition = And (Equal (Var "length") (IntLit 3)) (GreaterThan (Var "length") (IntLit 0))
  , program = arraySumProgram
  , postcondition = Equal (Var "sum") (IntLit 6)
  }

-- 验证数组求和程序
verifyArraySum :: Bool
verifyArraySum = verifyProgram arraySumTriple
```

## 总结

公理语义为程序验证和正确性证明提供了强大的理论基础，主要特点：

1. **形式化验证**：提供严格的程序正确性证明方法
2. **逻辑基础**：基于一阶逻辑和推理规则
3. **自动化支持**：可以部分自动化验证过程
4. **教学价值**：帮助理解程序逻辑和推理

通过Haskell的实现，我们能够：

- 定义霍尔三元组和推理规则
- 实现程序验证算法
- 自动生成不变式和后置条件
- 构建程序验证工具

公理语义为软件工程中的程序验证、静态分析和形式化方法提供了重要的理论基础。
