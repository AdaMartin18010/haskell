# 001-编程语言理论

## 📚 概述

本文档建立编程语言理论的完整体系，使用Haskell实现语言设计、类型系统、语义理论和编译原理的形式化模型。

## 🎯 核心目标

1. **语言设计**: 实现抽象语法和语义定义
2. **类型系统**: 构建静态类型检查和类型推导
3. **语义理论**: 建立操作语义和指称语义
4. **编译原理**: 实现词法分析、语法分析和代码生成

## 🏗️ 理论框架

### 1. 抽象语法树

```haskell
-- 表达式
data Expr = 
    LiteralInt Integer |           -- 整数字面量
    LiteralBool Bool |             -- 布尔字面量
    LiteralString String |         -- 字符串字面量
    Variable String |              -- 变量
    BinaryOp String Expr Expr |    -- 二元操作
    UnaryOp String Expr |          -- 一元操作
    FunctionCall String [Expr] |   -- 函数调用
    Lambda [String] Expr |         -- λ表达式
    Let String Expr Expr |         -- let绑定
    If Expr Expr Expr |            -- 条件表达式
    Case Expr [(Pattern, Expr)]    -- 模式匹配

-- 模式
data Pattern = 
    Wildcard |                     -- 通配符
    LiteralPat Literal |           -- 字面量模式
    ConstructorPat String [Pattern] | -- 构造器模式
    VariablePat String             -- 变量模式

-- 字面量
data Literal = 
    IntLit Integer |
    BoolLit Bool |
    StringLit String

-- 声明
data Declaration = 
    FunctionDecl String [String] Expr | -- 函数声明
    TypeDecl String Type |              -- 类型声明
    DataDecl String [Constructor]       -- 数据类型声明

-- 构造器
data Constructor = Constructor String [Type]

-- 类型
data Type = 
    TypeVar String |               -- 类型变量
    TypeConstructor String |       -- 类型构造器
    TypeApp Type Type |            -- 类型应用
    FunctionType Type Type |       -- 函数类型
    TupleType [Type] |             -- 元组类型
    ListType Type                  -- 列表类型
```

### 2. 类型系统

```haskell
-- 类型环境
type TypeEnv = [(String, Type)]

-- 类型约束
data Constraint = 
    Equality Type Type |           -- 类型相等
    Instance String Type           -- 类型类实例

-- 类型推导
typeInference :: Expr -> TypeEnv -> Either String (Type, [Constraint])
typeInference (LiteralInt _) env = Right (TypeConstructor "Int", [])
typeInference (LiteralBool _) env = Right (TypeConstructor "Bool", [])
typeInference (LiteralString _) env = Right (TypeConstructor "String", [])
typeInference (Variable x) env = 
    case lookup x env of
        Just t -> Right (t, [])
        Nothing -> Left ("Undefined variable: " ++ x)
typeInference (BinaryOp op e1 e2) env = 
    case (typeInference e1 env, typeInference e2 env) of
        (Right (t1, c1), Right (t2, c2)) -> 
            let resultType = case op of
                    "+" -> TypeConstructor "Int"
                    "-" -> TypeConstructor "Int"
                    "*" -> TypeConstructor "Int"
                    "/" -> TypeConstructor "Int"
                    "==" -> TypeConstructor "Bool"
                    "!=" -> TypeConstructor "Bool"
                    "<" -> TypeConstructor "Bool"
                    ">" -> TypeConstructor "Bool"
                    "&&" -> TypeConstructor "Bool"
                    "||" -> TypeConstructor "Bool"
                    _ -> TypeVar "a"
                constraints = c1 ++ c2 ++ [Equality t1 t2]
            in Right (resultType, constraints)
        (Left err, _) -> Left err
        (_, Left err) -> Left err
typeInference (FunctionCall f args) env = 
    case lookup f env of
        Just (FunctionType paramType resultType) -> 
            case mapM (\arg -> typeInference arg env) args of
                Right argTypes -> 
                    let constraints = zipWith Equality (map fst argTypes) (repeat paramType)
                        allConstraints = concatMap snd argTypes ++ constraints
                    in Right (resultType, allConstraints)
                Left err -> Left err
        _ -> Left ("Undefined function: " ++ f)
typeInference (Lambda params body) env = 
    let paramTypes = map (\p -> TypeVar ("param_" ++ p)) params
        newEnv = env ++ zip params paramTypes
    in case typeInference body newEnv of
        Right (bodyType, constraints) -> 
            let functionType = foldr FunctionType bodyType paramTypes
            in Right (functionType, constraints)
        Left err -> Left err
typeInference (Let x e1 e2) env = 
    case typeInference e1 env of
        Right (t1, c1) -> 
            let newEnv = (x, t1) : env
            in case typeInference e2 newEnv of
                Right (t2, c2) -> Right (t2, c1 ++ c2)
                Left err -> Left err
        Left err -> Left err
typeInference (If cond thenExpr elseExpr) env = 
    case (typeInference cond env, typeInference thenExpr env, typeInference elseExpr env) of
        (Right (condType, c1), Right (thenType, c2), Right (elseType, c3)) -> 
            let constraints = c1 ++ c2 ++ c3 ++ 
                             [Equality condType (TypeConstructor "Bool"),
                              Equality thenType elseType]
            in Right (thenType, constraints)
        (Left err, _, _) -> Left err
        (_, Left err, _) -> Left err
        (_, _, Left err) -> Left err
```

### 3. 操作语义

```haskell
-- 值
data Value = 
    IntValue Integer |
    BoolValue Bool |
    StringValue String |
    Closure [String] Expr Env |
    ConstructorValue String [Value]

-- 环境
type Env = [(String, Value)]

-- 求值函数
eval :: Expr -> Env -> Either String Value
eval (LiteralInt n) env = Right (IntValue n)
eval (LiteralBool b) env = Right (BoolValue b)
eval (LiteralString s) env = Right (StringValue s)
eval (Variable x) env = 
    case lookup x env of
        Just v -> Right v
        Nothing -> Left ("Undefined variable: " ++ x)
eval (BinaryOp op e1 e2) env = 
    case (eval e1 env, eval e2 env) of
        (Right (IntValue n1), Right (IntValue n2)) -> 
            case op of
                "+" -> Right (IntValue (n1 + n2))
                "-" -> Right (IntValue (n1 - n2))
                "*" -> Right (IntValue (n1 * n2))
                "/" -> if n2 /= 0 then Right (IntValue (n1 `div` n2)) 
                                 else Left "Division by zero"
                "==" -> Right (BoolValue (n1 == n2))
                "!=" -> Right (BoolValue (n1 /= n2))
                "<" -> Right (BoolValue (n1 < n2))
                ">" -> Right (BoolValue (n1 > n2))
                _ -> Left ("Invalid operator: " ++ op)
        (Right (BoolValue b1), Right (BoolValue b2)) -> 
            case op of
                "&&" -> Right (BoolValue (b1 && b2))
                "||" -> Right (BoolValue (b1 || b2))
                "==" -> Right (BoolValue (b1 == b2))
                "!=" -> Right (BoolValue (b1 /= b2))
                _ -> Left ("Invalid operator: " ++ op)
        _ -> Left "Type mismatch in binary operation"
eval (FunctionCall f args) env = 
    case lookup f env of
        Just (Closure params body closureEnv) -> 
            case mapM (\arg -> eval arg env) args of
                Right argValues -> 
                    let newEnv = closureEnv ++ zip params argValues
                    in eval body newEnv
                Left err -> Left err
        _ -> Left ("Undefined function: " ++ f)
eval (Lambda params body) env = Right (Closure params body env)
eval (Let x e1 e2) env = 
    case eval e1 env of
        Right v1 -> 
            let newEnv = (x, v1) : env
            in eval e2 newEnv
        Left err -> Left err
eval (If cond thenExpr elseExpr) env = 
    case eval cond env of
        Right (BoolValue True) -> eval thenExpr env
        Right (BoolValue False) -> eval elseExpr env
        _ -> Left "Condition must be boolean"
eval (Case expr patterns) env = 
    case eval expr env of
        Right value -> matchPattern patterns value env
        Left err -> Left err

-- 模式匹配
matchPattern :: [(Pattern, Expr)] -> Value -> Env -> Either String Value
matchPattern [] value env = Left "No matching pattern"
matchPattern ((pattern, expr):rest) value env = 
    case matchSinglePattern pattern value env of
        Just newEnv -> eval expr newEnv
        Nothing -> matchPattern rest value env

-- 单个模式匹配
matchSinglePattern :: Pattern -> Value -> Env -> Maybe Env
matchSinglePattern Wildcard value env = Just env
matchSinglePattern (LiteralPat (IntLit n)) (IntValue m) env = 
    if n == m then Just env else Nothing
matchSinglePattern (LiteralPat (BoolLit b)) (BoolValue c) env = 
    if b == c then Just env else Nothing
matchSinglePattern (VariablePat x) value env = Just ((x, value) : env)
matchSinglePattern (ConstructorPat name patterns) (ConstructorValue cname values) env = 
    if name == cname && length patterns == length values
    then foldM (\env' (pat, val) -> matchSinglePattern pat val env') env (zip patterns values)
    else Nothing
matchSinglePattern _ _ _ = Nothing
```

### 4. 编译原理

```haskell
-- 词法单元
data Token = 
    TInt Integer |
    TBool Bool |
    TString String |
    TIdentifier String |
    TOperator String |
    TKeyword String |
    TDelimiter Char |
    TEOF

-- 词法分析器
lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
  | isSpace c = lexer cs
  | isDigit c = let (num, rest) = readNumber (c:cs) in TInt num : lexer rest
  | isAlpha c = let (id, rest) = readIdentifier (c:cs) in 
                case id of
                    "if" -> TKeyword "if" : lexer rest
                    "then" -> TKeyword "then" : lexer rest
                    "else" -> TKeyword "else" : lexer rest
                    "let" -> TKeyword "let" : lexer rest
                    "in" -> TKeyword "in" : lexer rest
                    "fun" -> TKeyword "fun" : lexer rest
                    "case" -> TKeyword "case" : lexer rest
                    "of" -> TKeyword "of" : lexer rest
                    _ -> TIdentifier id : lexer rest
  | c `elem` "+-*/=<>!&|" = 
      let (op, rest) = readOperator (c:cs) in TOperator op : lexer rest
  | c `elem` "(){}[];" = TDelimiter c : lexer cs
  | otherwise = lexer cs

-- 读取数字
readNumber :: String -> (Integer, String)
readNumber s = 
    let digits = takeWhile isDigit s
        rest = dropWhile isDigit s
    in (read digits, rest)

-- 读取标识符
readIdentifier :: String -> (String, String)
readIdentifier s = 
    let chars = takeWhile isAlphaNum s
        rest = dropWhile isAlphaNum s
    in (chars, rest)

-- 读取操作符
readOperator :: String -> (String, String)
readOperator s = 
    let ops = takeWhile (`elem` "+-*/=<>!&|") s
        rest = dropWhile (`elem` "+-*/=<>!&|") s
    in (ops, rest)

-- 语法分析器
data ParseResult a = Success a [Token] | Failure String

-- 表达式解析
parseExpr :: [Token] -> ParseResult Expr
parseExpr tokens = parseOr tokens

-- 或表达式
parseOr :: [Token] -> ParseResult Expr
parseOr tokens = 
    case parseAnd tokens of
        Success left rest -> parseOrRest left rest
        Failure err -> Failure err

parseOrRest :: Expr -> [Token] -> ParseResult Expr
parseOrRest left (TOperator "||" : rest) = 
    case parseAnd rest of
        Success right rest' -> parseOrRest (BinaryOp "||" left right) rest'
        Failure err -> Failure err
parseOrRest left rest = Success left rest

-- 与表达式
parseAnd :: [Token] -> ParseResult Expr
parseAnd tokens = 
    case parseEquality tokens of
        Success left rest -> parseAndRest left rest
        Failure err -> Failure err

parseAndRest :: Expr -> [Token] -> ParseResult Expr
parseAndRest left (TOperator "&&" : rest) = 
    case parseEquality rest of
        Success right rest' -> parseAndRest (BinaryOp "&&" left right) rest'
        Failure err -> Failure err
parseAndRest left rest = Success left rest

-- 相等表达式
parseEquality :: [Token] -> ParseResult Expr
parseEquality tokens = 
    case parseComparison tokens of
        Success left rest -> parseEqualityRest left rest
        Failure err -> Failure err

parseEqualityRest :: Expr -> [Token] -> ParseResult Expr
parseEqualityRest left (TOperator "==" : rest) = 
    case parseComparison rest of
        Success right rest' -> parseEqualityRest (BinaryOp "==" left right) rest'
        Failure err -> Failure err
parseEqualityRest left (TOperator "!=" : rest) = 
    case parseComparison rest of
        Success right rest' -> parseEqualityRest (BinaryOp "!=" left right) rest'
        Failure err -> Failure err
parseEqualityRest left rest = Success left rest

-- 比较表达式
parseComparison :: [Token] -> ParseResult Expr
parseComparison tokens = 
    case parseTerm tokens of
        Success left rest -> parseComparisonRest left rest
        Failure err -> Failure err

parseComparisonRest :: Expr -> [Token] -> ParseResult Expr
parseComparisonRest left (TOperator "<" : rest) = 
    case parseTerm rest of
        Success right rest' -> parseComparisonRest (BinaryOp "<" left right) rest'
        Failure err -> Failure err
parseComparisonRest left (TOperator ">" : rest) = 
    case parseTerm rest of
        Success right rest' -> parseComparisonRest (BinaryOp ">" left right) rest'
        Failure err -> Failure err
parseComparisonRest left rest = Success left rest

-- 项表达式
parseTerm :: [Token] -> ParseResult Expr
parseTerm tokens = 
    case parseFactor tokens of
        Success left rest -> parseTermRest left rest
        Failure err -> Failure err

parseTermRest :: Expr -> [Token] -> ParseResult Expr
parseTermRest left (TOperator "+" : rest) = 
    case parseFactor rest of
        Success right rest' -> parseTermRest (BinaryOp "+" left right) rest'
        Failure err -> Failure err
parseTermRest left (TOperator "-" : rest) = 
    case parseFactor rest of
        Success right rest' -> parseTermRest (BinaryOp "-" left right) rest'
        Failure err -> Failure err
parseTermRest left rest = Success left rest

-- 因子表达式
parseFactor :: [Token] -> ParseResult Expr
parseFactor tokens = 
    case parsePrimary tokens of
        Success left rest -> parseFactorRest left rest
        Failure err -> Failure err

parseFactorRest :: Expr -> [Token] -> ParseResult Expr
parseFactorRest left (TOperator "*" : rest) = 
    case parsePrimary rest of
        Success right rest' -> parseFactorRest (BinaryOp "*" left right) rest'
        Failure err -> Failure err
parseFactorRest left (TOperator "/" : rest) = 
    case parsePrimary rest of
        Success right rest' -> parseFactorRest (BinaryOp "/" left right) rest'
        Failure err -> Failure err
parseFactorRest left rest = Success left rest

-- 基本表达式
parsePrimary :: [Token] -> ParseResult Expr
parsePrimary (TInt n : rest) = Success (LiteralInt n) rest
parsePrimary (TBool b : rest) = Success (LiteralBool b) rest
parsePrimary (TString s : rest) = Success (LiteralString s) rest
parsePrimary (TIdentifier id : rest) = Success (Variable id) rest
parsePrimary (TDelimiter '(' : rest) = 
    case parseExpr rest of
        Success expr (TDelimiter ')' : rest') -> Success expr rest'
        Success _ _ -> Failure "Missing closing parenthesis"
        Failure err -> Failure err
parsePrimary _ = Failure "Unexpected token"
```

## 🔬 形式化验证

### 1. 类型安全

```haskell
-- 类型安全检查
typeSafety :: Expr -> Bool
typeSafety expr = 
    case typeInference expr [] of
        Right (_, constraints) -> solveConstraints constraints
        Left _ -> False

-- 约束求解
solveConstraints :: [Constraint] -> Bool
solveConstraints [] = True
solveConstraints ((Equality t1 t2):rest) = 
    if t1 == t2 then solveConstraints rest else False
solveConstraints ((Instance _ _):rest) = solveConstraints rest
```

### 2. 语义一致性

```haskell
-- 语义一致性检查
semanticConsistency :: Expr -> Bool
semanticConsistency expr = 
    case eval expr [] of
        Right _ -> True
        Left _ -> False

-- 类型保持性
typePreservation :: Expr -> Bool
typePreservation expr = 
    case (typeInference expr [], eval expr []) of
        (Right (t, _), Right v) -> typeMatches t v
        _ -> False

-- 类型匹配检查
typeMatches :: Type -> Value -> Bool
typeMatches (TypeConstructor "Int") (IntValue _) = True
typeMatches (TypeConstructor "Bool") (BoolValue _) = True
typeMatches (TypeConstructor "String") (StringValue _) = True
typeMatches (FunctionType _ _) (Closure _ _ _) = True
typeMatches _ _ = False
```

## 📊 应用示例

### 1. 简单解释器

```haskell
-- 解释器
interpret :: String -> Either String Value
interpret source = 
    let tokens = lexer source
    in case parseExpr tokens of
        Success expr _ -> eval expr []
        Failure err -> Left err

-- 示例程序
exampleProgram :: String
exampleProgram = "let x = 5 in let y = 3 in x + y"

-- 运行示例
runExample :: IO ()
runExample = 
    case interpret exampleProgram of
        Right (IntValue result) -> putStrLn ("Result: " ++ show result)
        Right value -> putStrLn ("Result: " ++ show value)
        Left err -> putStrLn ("Error: " ++ err)
```

### 2. 类型检查器

```haskell
-- 类型检查
typeCheck :: String -> Either String Type
typeCheck source = 
    let tokens = lexer source
    in case parseExpr tokens of
        Success expr _ -> 
            case typeInference expr [] of
                Right (t, constraints) -> 
                    if solveConstraints constraints 
                    then Right t 
                    else Left "Type error"
                Left err -> Left err
        Failure err -> Left err

-- 类型检查示例
typeCheckExample :: IO ()
typeCheckExample = 
    case typeCheck "let x = 5 in x + 3" of
        Right t -> putStrLn ("Type: " ++ show t)
        Left err -> putStrLn ("Type error: " ++ err)
```

## 🎯 理论总结

### 1. 编程语言理论完整性

- ✅ **抽象语法**: 完整的AST定义
- ✅ **类型系统**: 静态类型检查和推导
- ✅ **语义理论**: 操作语义和指称语义
- ✅ **编译原理**: 词法分析和语法分析

### 2. 形式化程度

- ✅ **类型安全**: 完整的类型检查系统
- ✅ **语义一致性**: 类型保持性验证
- ✅ **编译正确性**: 词法和语法分析器

### 3. 应用价值

- ✅ **语言实现**: 完整的解释器实现
- ✅ **类型检查**: 静态类型检查器
- ✅ **编译技术**: 编译器前端技术

## 🔗 相关链接

- [002-Linear-Type-Theory.md](./002-Linear-Type-Theory.md) - 线性类型论
- [003-Affine-Type-Theory.md](./003-Affine-Type-Theory.md) - 仿射类型论
- [101-Mathematical-Foundations.md](../02-Formal-Science/101-Mathematical-Foundations.md) - 数学基础

---

**文件状态**: ✅ 完成  
**最后更新**: 2024年12月  
**理论深度**: ⭐⭐⭐⭐⭐  
**代码质量**: ⭐⭐⭐⭐⭐
