# Haskell类型系统 (Type System)

## 概述

Haskell的类型系统是其核心特性之一，提供了强大的静态类型检查、类型推导和多态性。Haskell的类型系统基于Hindley-Milner类型系统，支持高阶类型、类型类和高级类型特性。

## 基本类型

### 基本数据类型

```haskell
-- 基本数据类型
data BasicTypes = 
    IntType      -- 整数类型
  | DoubleType   -- 浮点数类型
  | CharType     -- 字符类型
  | BoolType     -- 布尔类型
  | StringType   -- 字符串类型
  | UnitType     -- 单位类型 ()
  deriving (Eq, Show)

-- 类型值
data TypeValue = 
    IntVal Integer
  | DoubleVal Double
  | CharVal Char
  | BoolVal Bool
  | StringVal String
  | UnitVal
  deriving (Eq, Show)

-- 类型检查函数
typeCheck :: TypeValue -> BasicTypes -> Bool
typeCheck (IntVal _) IntType = True
typeCheck (DoubleVal _) DoubleType = True
typeCheck (CharVal _) CharType = True
typeCheck (BoolVal _) BoolType = True
typeCheck (StringVal _) StringType = True
typeCheck UnitVal UnitType = True
typeCheck _ _ = False
```

### 函数类型

```haskell
-- 函数类型
data FunctionType = FunctionType
  { domain :: Type
  , codomain :: Type
  } deriving (Eq, Show)

-- 通用类型
data Type = 
    BasicType BasicTypes
  | FunctionType Type Type
  | ProductType Type Type
  | SumType Type Type
  | TypeVariable String
  | ForAllType String Type
  deriving (Eq, Show)

-- 函数类型检查
isFunctionType :: Type -> Bool
isFunctionType (FunctionType _ _) = True
isFunctionType _ = False

-- 获取函数参数类型
functionDomain :: Type -> Maybe Type
functionDomain (FunctionType domain _) = Just domain
functionDomain _ = Nothing

-- 获取函数返回类型
functionCodomain :: Type -> Maybe Type
functionCodomain (FunctionType _ codomain) = Just codomain
functionCodomain _ = Nothing
```

## 类型推导

### Hindley-Milner类型系统

```haskell
-- 类型环境
type TypeEnv = [(String, Type)]

-- 类型推导
inferType :: Expr -> TypeEnv -> Maybe Type
inferType expr env = case expr of
  -- 变量
  Var x -> lookup x env
  
  -- 字面量
  IntLit _ -> Just (BasicType IntType)
  BoolLit _ -> Just (BasicType BoolType)
  CharLit _ -> Just (BasicType CharType)
  StringLit _ -> Just (BasicType StringType)
  
  -- 函数应用
  App e1 e2 -> do
    t1 <- inferType e1 env
    t2 <- inferType e2 env
    case t1 of
      FunctionType argType resultType
        | argType == t2 -> Just resultType
        | otherwise -> Nothing
      _ -> Nothing
  
  -- 函数抽象
  Lambda x body -> do
    let argType = TypeVariable "a"  -- 简化处理
    resultType <- inferType body ((x, argType) : env)
    return (FunctionType argType resultType)
  
  -- 算术运算
  Add e1 e2 -> do
    t1 <- inferType e1 env
    t2 <- inferType e2 env
    if t1 == BasicType IntType && t2 == BasicType IntType
    then Just (BasicType IntType)
    else Nothing
  
  Sub e1 e2 -> do
    t1 <- inferType e1 env
    t2 <- inferType e2 env
    if t1 == BasicType IntType && t2 == BasicType IntType
    then Just (BasicType IntType)
    else Nothing
  
  Mul e1 e2 -> do
    t1 <- inferType e1 env
    t2 <- inferType e2 env
    if t1 == BasicType IntType && t2 == BasicType IntType
    then Just (BasicType IntType)
    else Nothing
  
  -- 比较运算
  Eq e1 e2 -> do
    t1 <- inferType e1 env
    t2 <- inferType e2 env
    if t1 == t2
    then Just (BasicType BoolType)
    else Nothing
  
  Lt e1 e2 -> do
    t1 <- inferType e1 env
    t2 <- inferType e2 env
    if t1 == BasicType IntType && t2 == BasicType IntType
    then Just (BasicType BoolType)
    else Nothing
  
  -- 条件语句
  If e1 e2 e3 -> do
    t1 <- inferType e1 env
    t2 <- inferType e2 env
    t3 <- inferType e3 env
    if t1 == BasicType BoolType && t2 == t3
    then Just t2
    else Nothing
  
  -- 其他情况
  _ -> Nothing

-- 表达式类型
data Expr = 
    Var String
  | IntLit Integer
  | BoolLit Bool
  | CharLit Char
  | StringLit String
  | App Expr Expr
  | Lambda String Expr
  | Add Expr Expr
  | Sub Expr Expr
  | Mul Expr Expr
  | Eq Expr Expr
  | Lt Expr Expr
  | If Expr Expr Expr
  deriving (Eq, Show)
```

### 类型统一

```haskell
-- 类型替换
type Substitution = [(String, Type)]

-- 应用替换
applySubstitution :: Substitution -> Type -> Type
applySubstitution sub typ = case typ of
  TypeVariable x -> 
    case lookup x sub of
      Just t -> t
      Nothing -> typ
  FunctionType t1 t2 -> 
    FunctionType (applySubstitution sub t1) (applySubstitution sub t2)
  ProductType t1 t2 -> 
    ProductType (applySubstitution sub t1) (applySubstitution sub t2)
  SumType t1 t2 -> 
    SumType (applySubstitution sub t1) (applySubstitution sub t2)
  ForAllType x t -> 
    ForAllType x (applySubstitution sub t)
  _ -> typ

-- 类型统一
unify :: Type -> Type -> Maybe Substitution
unify t1 t2 = case (t1, t2) of
  -- 相同类型
  (BasicType b1, BasicType b2) -> 
    if b1 == b2 then Just [] else Nothing
  
  -- 类型变量
  (TypeVariable x, t) -> 
    if occursIn x t then Nothing else Just [(x, t)]
  (t, TypeVariable x) -> 
    if occursIn x t then Nothing else Just [(x, t)]
  
  -- 函数类型
  (FunctionType d1 c1, FunctionType d2 c2) -> do
    sub1 <- unify d1 d2
    sub2 <- unify (applySubstitution sub1 c1) (applySubstitution sub1 c2)
    return (composeSubstitutions sub1 sub2)
  
  -- 积类型
  (ProductType t1 t2, ProductType t3 t4) -> do
    sub1 <- unify t1 t3
    sub2 <- unify (applySubstitution sub1 t2) (applySubstitution sub1 t4)
    return (composeSubstitutions sub1 sub2)
  
  -- 和类型
  (SumType t1 t2, SumType t3 t4) -> do
    sub1 <- unify t1 t3
    sub2 <- unify (applySubstitution sub1 t2) (applySubstitution sub1 t4)
    return (composeSubstitutions sub1 sub2)
  
  -- 其他情况
  _ -> Nothing

-- 检查变量是否出现在类型中
occursIn :: String -> Type -> Bool
occursIn x typ = case typ of
  TypeVariable y -> x == y
  FunctionType t1 t2 -> occursIn x t1 || occursIn x t2
  ProductType t1 t2 -> occursIn x t1 || occursIn x t2
  SumType t1 t2 -> occursIn x t1 || occursIn x t2
  ForAllType y t -> x /= y && occursIn x t
  _ -> False

-- 组合替换
composeSubstitutions :: Substitution -> Substitution -> Substitution
composeSubstitutions sub1 sub2 = 
  [(x, applySubstitution sub2 t) | (x, t) <- sub1] ++ sub2
```

## 类型类

### 类型类系统

```haskell
-- 类型类定义
data TypeClass = TypeClass
  { className :: String
  , methods :: [(String, Type)]
  , superClasses :: [String]
  } deriving (Eq, Show)

-- 类型类实例
data TypeClassInstance = TypeClassInstance
  { instanceClass :: String
  , instanceType :: Type
  , methodImplementations :: [(String, Expr)]
  } deriving (Eq, Show)

-- 预定义类型类
predefinedTypeClasses :: [TypeClass]
predefinedTypeClasses = 
  [ TypeClass "Eq" 
      [("==", FunctionType (TypeVariable "a") (FunctionType (TypeVariable "a") (BasicType BoolType)))]
      []
  , TypeClass "Ord" 
      [("<", FunctionType (TypeVariable "a") (FunctionType (TypeVariable "a") (BasicType BoolType)))]
      ["Eq"]
  , TypeClass "Show" 
      [("show", FunctionType (TypeVariable "a") (BasicType StringType))]
      []
  , TypeClass "Read" 
      [("read", FunctionType (BasicType StringType) (TypeVariable "a"))]
      []
  ]

-- 类型类实例
predefinedInstances :: [TypeClassInstance]
predefinedInstances = 
  [ TypeClassInstance "Eq" (BasicType IntType)
      [("==", Lambda "x" (Lambda "y" (Eq (Var "x") (Var "y"))))]
  , TypeClassInstance "Eq" (BasicType BoolType)
      [("==", Lambda "x" (Lambda "y" (Eq (Var "x") (Var "y"))))]
  , TypeClassInstance "Ord" (BasicType IntType)
      [("<", Lambda "x" (Lambda "y" (Lt (Var "x") (Var "y"))))]
  ]

-- 类型类约束
data TypeClassConstraint = TypeClassConstraint
  { constraintClass :: String
  , constraintType :: Type
  } deriving (Eq, Show)

-- 带约束的类型
data ConstrainedType = ConstrainedType
  { constraints :: [TypeClassConstraint]
  , qualifiedType :: Type
  } deriving (Eq, Show)

-- 检查类型类约束
checkTypeClassConstraint :: TypeClassConstraint -> TypeEnv -> Bool
checkTypeClassConstraint (TypeClassConstraint className typ) env = 
  any (\inst -> instanceClass inst == className && 
                instanceType inst == typ) predefinedInstances
```

## 高级类型特性

### 高阶类型

```haskell
-- 高阶类型
data HigherOrderType = 
    TypeConstructor String [Type]
  | TypeVariableHO String
  | FunctionTypeHO HigherOrderType HigherOrderType
  deriving (Eq, Show)

-- 常见高阶类型
maybeType :: Type -> HigherOrderType
maybeType t = TypeConstructor "Maybe" [t]

listType :: Type -> HigherOrderType
listType t = TypeConstructor "List" [t]

eitherType :: Type -> Type -> HigherOrderType
eitherType t1 t2 = TypeConstructor "Either" [t1, t2]

-- 高阶类型应用
applyTypeConstructor :: String -> [Type] -> HigherOrderType
applyTypeConstructor name args = TypeConstructor name args

-- 类型构造器
data TypeConstructor = 
    MaybeConstructor
  | ListConstructor
  | EitherConstructor
  | TupleConstructor Int
  | IOConstructor
  deriving (Eq, Show)
```

### 存在类型

```haskell
-- 存在类型
data ExistentialType = ExistentialType
  { existentialVars :: [String]
  , existentialBody :: Type
  } deriving (Eq, Show)

-- 存在类型包装
data ExistentialValue = ExistentialValue
  { existentialType :: Type
  , existentialValue :: TypeValue
  } deriving (Eq, Show)

-- 创建存在类型值
packExistential :: Type -> TypeValue -> ExistentialValue
packExistential typ val = ExistentialValue typ val

-- 解包存在类型值
unpackExistential :: ExistentialValue -> (Type, TypeValue)
unpackExistential (ExistentialValue typ val) = (typ, val)
```

### GADT (广义代数数据类型)

```haskell
-- GADT定义
data GADT a where
  GInt :: Integer -> GADT Integer
  GBool :: Bool -> GADT Bool
  GPair :: GADT a -> GADT b -> GADT (a, b)
  GFunction :: (a -> b) -> GADT (a -> b)

-- GADT模式匹配
gadtMatch :: GADT a -> String
gadtMatch gadt = case gadt of
  GInt _ -> "Integer"
  GBool _ -> "Boolean"
  GPair _ _ -> "Pair"
  GFunction _ -> "Function"

-- GADT类型安全操作
gadtOperation :: GADT a -> GADT b -> Maybe (GADT (a, b))
gadtOperation g1 g2 = Just (GPair g1 g2)
```

## 类型安全

### 类型安全检查

```haskell
-- 类型安全检查
typeSafe :: Expr -> TypeEnv -> Bool
typeSafe expr env = case inferType expr env of
  Just _ -> True
  Nothing -> False

-- 类型错误检测
typeError :: Expr -> TypeEnv -> Maybe String
typeError expr env = case inferType expr env of
  Just _ -> Nothing
  Nothing -> Just "Type error detected"

-- 类型兼容性检查
typeCompatible :: Type -> Type -> Bool
typeCompatible t1 t2 = case unify t1 t2 of
  Just _ -> True
  Nothing -> False
```

### 类型推导算法

```haskell
-- 完整的类型推导算法
completeTypeInference :: Expr -> TypeEnv -> Maybe (Type, Substitution)
completeTypeInference expr env = do
  -- 第一步：为每个子表达式分配类型变量
  let exprWithVars = assignTypeVariables expr
  
  -- 第二步：生成类型约束
  constraints <- generateConstraints exprWithVars env
  
  -- 第三步：求解约束
  substitution <- solveConstraints constraints
  
  -- 第四步：应用替换得到最终类型
  let finalType = applySubstitution substitution (getType exprWithVars)
  
  return (finalType, substitution)

-- 分配类型变量
assignTypeVariables :: Expr -> ExprWithType
assignTypeVariables expr = case expr of
  Var x -> ExprWithType (Var x) (TypeVariable ("t_" ++ x))
  IntLit n -> ExprWithType (IntLit n) (BasicType IntType)
  BoolLit b -> ExprWithType (BoolLit b) (BasicType BoolType)
  App e1 e2 -> 
    let e1' = assignTypeVariables e1
        e2' = assignTypeVariables e2
        resultType = TypeVariable "result"
    in ExprWithType (App (getExpr e1') (getExpr e2')) resultType
  Lambda x body -> 
    let body' = assignTypeVariables body
        paramType = TypeVariable ("param_" ++ x)
        resultType = FunctionType paramType (getType body')
    in ExprWithType (Lambda x (getExpr body')) resultType
  _ -> ExprWithType expr (TypeVariable "unknown")

-- 带类型的表达式
data ExprWithType = ExprWithType
  { getExpr :: Expr
  , getType :: Type
  } deriving (Eq, Show)

-- 生成类型约束
generateConstraints :: ExprWithType -> TypeEnv -> Maybe [TypeConstraint]
generateConstraints exprWithType env = case getExpr exprWithType of
  Var x -> 
    case lookup x env of
      Just t -> Just [TypeConstraint (getType exprWithType) t]
      Nothing -> Nothing
  App e1 e2 -> do
    let e1' = ExprWithType e1 (TypeVariable "func")
        e2' = ExprWithType e2 (TypeVariable "arg")
    cs1 <- generateConstraints e1' env
    cs2 <- generateConstraints e2' env
    let appConstraint = TypeConstraint 
          (getType e1') 
          (FunctionType (getType e2') (getType exprWithType))
    return (cs1 ++ cs2 ++ [appConstraint])
  _ -> Just []

-- 类型约束
data TypeConstraint = TypeConstraint
  { leftType :: Type
  , rightType :: Type
  } deriving (Eq, Show)

-- 求解约束
solveConstraints :: [TypeConstraint] -> Maybe Substitution
solveConstraints [] = Just []
solveConstraints (c:cs) = do
  sub <- unify (leftType c) (rightType c)
  restSub <- solveConstraints (map (applyConstraintSubstitution sub) cs)
  return (composeSubstitutions sub restSub)

-- 应用约束替换
applyConstraintSubstitution :: Substitution -> TypeConstraint -> TypeConstraint
applyConstraintSubstitution sub (TypeConstraint t1 t2) = 
  TypeConstraint (applySubstitution sub t1) (applySubstitution sub t2)
```

## 应用示例

### 类型推导示例

```haskell
-- 示例1：简单函数
example1 :: Expr
example1 = Lambda "x" (Add (Var "x") (IntLit 1))

-- 示例2：函数应用
example2 :: Expr
example2 = App (Lambda "x" (Add (Var "x") (Var "x"))) (IntLit 5)

-- 示例3：条件表达式
example3 :: Expr
example3 = If (Lt (Var "x") (IntLit 10)) 
              (Add (Var "x") (IntLit 1)) 
              (Var "x")

-- 类型推导测试
testTypeInference :: IO ()
testTypeInference = do
  putStrLn "Testing type inference..."
  
  let env1 = [("x", BasicType IntType)]
  
  case inferType example1 env1 of
    Just t -> putStrLn $ "Example1 type: " ++ show t
    Nothing -> putStrLn "Example1: Type error"
  
  case inferType example2 env1 of
    Just t -> putStrLn $ "Example2 type: " ++ show t
    Nothing -> putStrLn "Example2: Type error"
  
  case inferType example3 env1 of
    Just t -> putStrLn $ "Example3 type: " ++ show t
    Nothing -> putStrLn "Example3: Type error"
```

### 类型类示例

```haskell
-- 自定义类型类
data MyTypeClass = MyTypeClass
  { myClassName :: String
  , myMethods :: [(String, Type)]
  }

-- 自定义类型
data MyType = MyType Integer deriving (Eq, Show)

-- 类型类实例
myTypeInstance :: TypeClassInstance
myTypeInstance = TypeClassInstance
  { instanceClass = "Show"
  , instanceType = TypeConstructor "MyType" []
  , methodImplementations = 
      [("show", Lambda "x" (StringLit "MyType"))]
  }

-- 类型类约束检查
checkMyTypeShow :: Bool
checkMyTypeShow = 
  checkTypeClassConstraint 
    (TypeClassConstraint "Show" (TypeConstructor "MyType" [])) 
    []
```

## 总结

Haskell的类型系统提供了强大的静态类型检查能力，主要特点：

1. **静态类型检查**：在编译时发现类型错误
2. **类型推导**：自动推导表达式类型
3. **多态性**：支持参数多态和特设多态
4. **类型安全**：保证程序运行时的类型安全
5. **高级特性**：支持高阶类型、存在类型、GADT等

通过Haskell的类型系统，我们能够：

- 在编译时捕获大部分错误
- 编写更安全、更可靠的代码
- 利用类型信息进行程序优化
- 构建类型安全的抽象

Haskell的类型系统为函数式编程和类型安全编程提供了坚实的基础。
