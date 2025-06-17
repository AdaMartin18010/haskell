# Haskell 模板Haskell

## 概述

模板Haskell（Template Haskell）是Haskell的元编程系统，允许在编译时生成代码。它提供了强大的代码生成和抽象能力，是Haskell高级特性的重要组成部分。

## 1. 基本概念

### 1.1 什么是模板Haskell

```haskell
-- 模板Haskell允许编译时代码生成
-- 使用QuasiQuotes语法
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

-- 基本示例：生成简单的数据类型
generateSimpleType :: Q [Dec]
generateSimpleType = [d|
    data SimpleType = A | B | C
    deriving (Show, Eq)
  |]
```

### 1.2 编译时vs运行时

```haskell
-- 编译时代码生成
compileTimeGeneration :: Q [Dec]
compileTimeGeneration = do
    -- 在编译时生成代码
    return [DataD [] (mkName "GeneratedType") [] Nothing 
            [NormalC (mkName "Constructor") []] []]

-- 运行时反射（对比）
runtimeReflection :: Type -> String
runtimeReflection = show
```

## 2. 语法和结构

### 2.1 QuasiQuotes语法

```haskell
-- 使用QuasiQuotes进行代码生成
{-# LANGUAGE QuasiQuotes #-}

-- 生成数据类型
generatedDataType :: Q [Dec]
generatedDataType = [d|
    data GeneratedData = 
        Constructor1 Int String |
        Constructor2 Double |
        Constructor3
    deriving (Show, Eq, Ord)
  |]

-- 生成函数
generatedFunction :: Q [Dec]
generatedFunction = [d|
    generatedFunc :: Int -> String
    generatedFunc n = "Generated: " ++ show n
  |]

-- 生成类型类实例
generatedInstance :: Q [Dec]
generatedInstance = [d|
    instance Show GeneratedData where
        show Constructor1 = "Constructor1"
        show Constructor2 = "Constructor2"
        show Constructor3 = "Constructor3"
  |]
```

### 2.2 手动构建AST

```haskell
-- 手动构建抽象语法树
manualAST :: Q [Dec]
manualAST = do
    -- 创建类型名称
    let typeName = mkName "ManualType"
    
    -- 创建构造函数
    let constructor1 = NormalC (mkName "ManualConstructor1") 
                              [NotStrict, ConT ''Int]
    let constructor2 = NormalC (mkName "ManualConstructor2") 
                              [NotStrict, ConT ''String]
    
    -- 创建数据类型声明
    let dataDecl = DataD [] typeName [] Nothing 
                         [constructor1, constructor2] []
    
    return [dataDecl]

-- 生成函数定义
generateFunction :: String -> String -> Q [Dec]
generateFunction funcName body = do
    let name = mkName funcName
    let funcType = ArrowT `AppT` ConT ''Int `AppT` ConT ''String
    let funcBody = NormalB (VarE (mkName body))
    let funcClause = Clause [] funcBody []
    
    return [FunD name [funcClause]]
```

## 3. 常用模式

### 3.1 记录生成

```haskell
-- 生成记录类型
generateRecord :: String -> [(String, Type)] -> Q [Dec]
generateRecord typeName fields = do
    let name = mkName typeName
    
    -- 生成字段
    let recordFields = map (\(fieldName, fieldType) ->
        (mkName fieldName, NotStrict, fieldType)) fields
    
    -- 创建记录构造函数
    let recordConstructor = RecC name recordFields
    
    -- 生成数据类型
    let dataDecl = DataD [] name [] Nothing [recordConstructor] []
    
    return [dataDecl]

-- 使用示例
personRecord :: Q [Dec]
personRecord = generateRecord "Person" 
    [("name", ConT ''String), ("age", ConT ''Int)]
```

### 3.2 类型类实例生成

```haskell
-- 自动生成类型类实例
generateShowInstance :: Name -> Q [Dec]
generateShowInstance typeName = do
    -- 获取类型信息
    info <- reify typeName
    
    case info of
        TyConI (DataD _ _ _ _ constructors _) -> do
            -- 生成show函数子句
            clauses <- mapM generateShowClause constructors
            let showFunc = FunD (mkName "show") clauses
            
            -- 创建实例声明
            let instanceDecl = InstanceD Nothing [] 
                                (ConT ''Show `AppT` ConT typeName) 
                                [showFunc]
            
            return [instanceDecl]
        _ -> fail "Not a data type"

-- 生成show子句
generateShowClause :: Con -> Q Clause
generateShowClause (NormalC name []) = do
    let pattern = ConP name []
    let body = NormalB (LitE (StringL (nameBase name)))
    return $ Clause [pattern] body []
generateShowClause (RecC name fields) = do
    let fieldNames = map (\(n, _, _) -> n) fields
    let pattern = ConP name (map VarP fieldNames)
    let body = NormalB (LitE (StringL (nameBase name)))
    return $ Clause [pattern] body []
```

### 3.3 透镜生成

```haskell
-- 生成透镜
generateLenses :: Name -> Q [Dec]
generateLenses typeName = do
    info <- reify typeName
    
    case info of
        TyConI (DataD _ _ _ _ [RecC name fields] _) -> do
            -- 为每个字段生成透镜
            lenses <- mapM (generateLens typeName name) fields
            return lenses
        _ -> fail "Not a record type"

-- 为单个字段生成透镜
generateLens :: Name -> Name -> (Name, Strict, Type) -> Q Dec
generateLens typeName constructorName (fieldName, _, fieldType) = do
    let lensName = mkName (nameBase fieldName ++ "L")
    let lensType = ArrowT `AppT` ConT typeName 
                         `AppT` (ArrowT `AppT` fieldType `AppT` ConT typeName)
    
    -- 生成透镜函数体
    let getter = VarE fieldName
    let setter = LamE [VarP (mkName "newVal"), VarP (mkName "record")] 
                     (RecUpdE (VarE (mkName "record")) 
                              [(fieldName, VarE (mkName "newVal"))])
    
    let lensBody = NormalB (TupE [Just getter, Just setter])
    let lensClause = Clause [] lensBody []
    
    return $ FunD lensName [lensClause]
```

## 4. 高级特性

### 4.1 类型级编程

```haskell
-- 类型级编程与模板Haskell结合
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

-- 类型级自然数
data Nat = Zero | Succ Nat

-- 类型族
type family Length (xs :: [*]) :: Nat where
    Length '[] = 'Zero
    Length (x ': xs) = 'Succ (Length xs)

-- 生成向量类型
generateVector :: Q [Dec]
generateVector = do
    let vectorName = mkName "Vector"
    let lengthType = VarT (mkName "n")
    let elementType = VarT (mkName "a")
    
    -- 创建向量类型
    let vectorType = ForallT [PlainTV (mkName "n"), PlainTV (mkName "a")] 
                             [ConT ''Nat `AppT` lengthType]
                             (ConT vectorName `AppT` lengthType `AppT` elementType)
    
    -- 生成构造函数
    let nilConstructor = NormalC (mkName "VNil") []
    let consConstructor = NormalC (mkName "VCons") 
                                 [NotStrict, elementType, 
                                  NotStrict, ConT vectorName `AppT` 
                                  (ConT ''Succ `AppT` lengthType) `AppT` elementType]
    
    let dataDecl = DataD [] vectorName [lengthType, elementType] 
                         (Just vectorType) [nilConstructor, consConstructor] []
    
    return [dataDecl]
```

### 4.2 代码模板

```haskell
-- 创建代码模板
codeTemplate :: String -> [(String, String)] -> Q [Dec]
codeTemplate templateName replacements = do
    let template = unlines [
            "templateFunction :: String -> String",
            "templateFunction input = ",
            "    \"Template: \" ++ input ++ \" with replacements\""
        ]
    
    -- 应用替换
    let processedTemplate = foldr (\(old, new) acc -> 
        replace old new acc) template replacements
    
    -- 解析模板
    parsed <- runQ (parseDecs processedTemplate)
    return parsed

-- 替换函数
replace :: String -> String -> String -> String
replace old new = map (\c -> if c == head old then head new else c)
```

### 4.3 编译时代码检查

```haskell
-- 编译时代码检查
compileTimeCheck :: Q [Dec]
compileTimeCheck = do
    -- 检查类型是否存在
    maybeInfo <- lookupTypeName "SomeType"
    case maybeInfo of
        Just _ -> return []  -- 类型存在，继续
        Nothing -> fail "SomeType not found"
    
    -- 生成代码
    return [d|
        data CheckedType = CheckedConstructor
        deriving Show
      |]

-- 条件代码生成
conditionalGeneration :: Bool -> Q [Dec]
conditionalGeneration condition = do
    if condition
        then return [d|
            data ConditionalType = WhenTrue
            deriving Show
          |]
        else return [d|
            data ConditionalType = WhenFalse
            deriving Show
          |]
```

## 5. 实际应用

### 5.1 JSON序列化生成

```haskell
-- 自动生成JSON序列化
generateJSONInstance :: Name -> Q [Dec]
generateJSONInstance typeName = do
    info <- reify typeName
    
    case info of
        TyConI (DataD _ _ _ _ constructors _) -> do
            -- 生成toJSON函数
            toJSONClauses <- mapM generateToJSONClause constructors
            let toJSONFunc = FunD (mkName "toJSON") toJSONClauses
            
            -- 生成fromJSON函数
            fromJSONClauses <- mapM generateFromJSONClause constructors
            let fromJSONFunc = FunD (mkName "parseJSON") fromJSONClauses
            
            -- 创建实例
            let instanceDecl = InstanceD Nothing [] 
                                (ConT ''ToJSON `AppT` ConT typeName) 
                                [toJSONFunc]
            let parseInstanceDecl = InstanceD Nothing [] 
                                    (ConT ''FromJSON `AppT` ConT typeName) 
                                    [fromJSONFunc]
            
            return [instanceDecl, parseInstanceDecl]
        _ -> fail "Not a data type"

-- 生成toJSON子句
generateToJSONClause :: Con -> Q Clause
generateToJSONClause (NormalC name []) = do
    let pattern = ConP name []
    let body = NormalB (ConE (mkName "String") `AppE` 
                       LitE (StringL (nameBase name)))
    return $ Clause [pattern] body []
```

### 5.2 数据库模型生成

```haskell
-- 生成数据库模型
generateDBModel :: String -> [(String, String)] -> Q [Dec]
generateDBModel modelName fields = do
    -- 生成数据类型
    let typeName = mkName modelName
    let recordFields = map (\(fieldName, fieldType) ->
        (mkName fieldName, NotStrict, ConT (mkName fieldType))) fields
    
    let recordConstructor = RecC typeName recordFields
    let dataDecl = DataD [] typeName [] Nothing [recordConstructor] []
    
    -- 生成数据库操作函数
    let tableName = mkName (modelName ++ "Table")
    let insertFunc = FunD (mkName ("insert" ++ modelName)) 
                         [Clause [] (NormalB (LitE (StringL ("INSERT INTO " ++ modelName)))) []]
    
    return [dataDecl, insertFunc]
```

### 5.3 API路由生成

```haskell
-- 生成Web API路由
generateAPIRoutes :: String -> [String] -> Q [Dec]
generateAPIRoutes resourceName actions = do
    -- 生成路由函数
    routes <- mapM (generateRoute resourceName) actions
    
    -- 生成主路由函数
    let mainRoute = FunD (mkName ("routes" ++ resourceName)) 
                         [Clause [] (NormalB (ListE routes)) []]
    
    return (mainRoute : routes)

-- 生成单个路由
generateRoute :: String -> String -> Q Dec
generateRoute resource action = do
    let routeName = mkName (action ++ resource)
    let routeBody = NormalB (LitE (StringL ("/" ++ resource ++ "/" ++ action)))
    let routeClause = Clause [] routeBody []
    
    return $ FunD routeName [routeClause]
```

## 6. 调试和测试

### 6.1 调试模板Haskell

```haskell
-- 调试代码生成
debugTemplate :: Q [Dec]
debugTemplate = do
    -- 打印调试信息
    runIO $ putStrLn "Generating template..."
    
    -- 生成代码
    let result = [d|
        data DebugType = DebugConstructor
        deriving Show
      |]
    
    -- 打印生成的代码
    runIO $ putStrLn $ "Generated: " ++ show result
    
    return result

-- 条件调试
conditionalDebug :: Bool -> Q [Dec]
conditionalDebug debug = do
    when debug $ runIO $ putStrLn "Debug mode enabled"
    
    return [d|
        data ConditionalDebug = DebugOn | DebugOff
        deriving Show
      |]
```

### 6.2 测试生成的代码

```haskell
-- 测试生成的代码
testGeneratedCode :: Q [Dec]
testGeneratedCode = do
    -- 生成测试数据类型
    let testData = [d|
        data TestType = TestConstructor Int String
        deriving (Show, Eq)
      |]
    
    -- 生成测试函数
    let testFunction = [d|
        testGenerated :: TestType -> Bool
        testGenerated (TestConstructor n s) = n > 0 && not (null s)
      |]
    
    return (testData ++ testFunction)
```

## 7. 性能考虑

### 7.1 编译时优化

```haskell
-- 编译时优化
optimizedGeneration :: Q [Dec]
optimizedGeneration = do
    -- 使用严格求值
    let strictData = [d|
        data OptimizedType = OptimizedConstructor !Int !String
        deriving Show
      |]
    
    -- 生成内联函数
    let inlineFunction = [d|
        {-# INLINE optimizedFunction #-}
        optimizedFunction :: Int -> Int
        optimizedFunction x = x * 2 + 1
      |]
    
    return (strictData ++ inlineFunction)
```

### 7.2 内存优化

```haskell
-- 内存优化
memoryOptimizedGeneration :: Q [Dec]
memoryOptimizedGeneration = do
    -- 使用紧凑数据类型
    let compactData = [d|
        data CompactType = CompactConstructor {-# UNPACK #-} !Int
        deriving Show
      |]
    
    -- 生成内存高效的函数
    let efficientFunction = [d|
        efficientFunction :: [Int] -> Int
        efficientFunction = foldl' (+) 0
      |]
    
    return (compactData ++ [efficientFunction])
```

## 8. 最佳实践

### 8.1 代码组织

```haskell
-- 模块化模板Haskell
module TemplateUtils where

-- 通用生成函数
generateSimpleType :: String -> Q [Dec]
generateSimpleType typeName = do
    let name = mkName typeName
    let constructor = NormalC name []
    let dataDecl = DataD [] name [] Nothing [constructor] []
    return [dataDecl]

-- 组合生成函数
generateComplexType :: String -> [String] -> Q [Dec]
generateComplexType typeName constructors = do
    let name = mkName typeName
    let cons = map (\c -> NormalC (mkName c) []) constructors
    let dataDecl = DataD [] name [] Nothing cons []
    return [dataDecl]
```

### 8.2 错误处理

```haskell
-- 错误处理
safeGeneration :: String -> Q [Dec]
safeGeneration typeName = do
    -- 检查名称是否有效
    when (null typeName) $ fail "Type name cannot be empty"
    
    -- 检查名称是否已存在
    maybeInfo <- lookupTypeName typeName
    when (isJust maybeInfo) $ fail $ "Type " ++ typeName ++ " already exists"
    
    -- 安全生成
    return [d|
        data SafeType = SafeConstructor
        deriving Show
      |]
```

## 总结

模板Haskell提供了强大的编译时代码生成能力，包括：

1. **QuasiQuotes语法**：简洁的代码生成语法
2. **AST操作**：手动构建抽象语法树
3. **类型级编程**：结合类型系统的高级特性
4. **实际应用**：JSON序列化、数据库模型、API路由
5. **调试和测试**：开发工具和测试方法
6. **性能优化**：编译时和内存优化
7. **最佳实践**：代码组织和错误处理

这些特性使模板Haskell成为Haskell元编程的强大工具。

## 相关链接

- [GHC扩展](../10-Advanced-Features/02-GHC-Extensions.md)
- [高级类型](../05-Type-System/04-Advanced-Types.md)
- [设计模式](../06-Design-Patterns/01-Functional-Patterns.md)
- [性能优化](../10-Advanced-Features/03-Performance-Optimization.md)

---

**最后更新**: 2024年12月  
**版本**: 1.0.0
