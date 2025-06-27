# 01. 基本线性类型系统 (Basic Linear Type Systems)

## 概述

线性类型系统是基于线性逻辑的类型系统，它确保每个值被精确使用一次。这种类型系统在Haskell中得到了广泛应用，特别是在资源管理和并发编程中。

## 核心概念

### 1. 线性性 (Linearity)

一个值如果被标记为线性，那么它必须被精确使用一次，不能重复使用或丢弃。

### 2. 线性函数

线性函数 `A ⊸ B` 表示一个函数，它消耗一个 `A` 类型的值，产生一个 `B` 类型的值。

### 3. 线性积

线性积 `A ⊗ B` 表示同时拥有 `A` 和 `B` 类型的值，两个值都必须被使用。

## 形式化定义

### 类型语法

```
A, B ::= α | A ⊸ B | A ⊗ B | A ⊕ B | !A | 1 | 0
```

### 类型规则

#### 线性函数类型

```
Γ, x:A ⊢ M:B
───────────── (⊸I)
Γ ⊢ λx.M:A⊸B

Γ ⊢ M:A⊸B  Δ ⊢ N:A
────────────────── (⊸E)
Γ,Δ ⊢ M N:B
```

#### 线性积类型

```
Γ ⊢ M:A  Δ ⊢ N:B
──────────────── (⊗I)
Γ,Δ ⊢ (M,N):A⊗B

Γ ⊢ M:A⊗B  Δ,x:A,y:B ⊢ N:C
────────────────────────── (⊗E)
Γ,Δ ⊢ let (x,y) = M in N:C
```

#### 指数类型

```
Γ ⊢ M:A
─────── (!I)
Γ ⊢ !M:!A

Γ ⊢ M:!A  Δ,x:A ⊢ N:B
───────────────────── (!E)
Γ,Δ ⊢ let !x = M in N:B
```

## Haskell实现

### 基本线性类型定义

```haskell
-- 线性函数类型
type LinearFunction a b = a %1 -> b

-- 线性积类型
data LinearPair a b = LinearPair a b

-- 线性和类型
data LinearSum a b = Left a | Right b

-- 线性单位类型
data LinearUnit = LinearUnit

-- 线性零类型
data LinearVoid

-- 指数类型（可重用类型）
data Bang a = Bang a
```

### 线性类型类

```haskell
-- 线性函子
class LinearFunctor f where
    lmap :: (a %1 -> b) -> f a %1 -> f b

-- 线性应用函子
class LinearFunctor f => LinearApplicative f where
    lpure :: a -> f a
    l(<*>) :: f (a %1 -> b) %1 -> f a %1 -> f b

-- 线性单子
class LinearApplicative m => LinearMonad m where
    l(>>=) :: m a %1 -> (a %1 -> m b) %1 -> m b
```

### 线性类型实例

```haskell
-- 线性对实例
instance LinearFunctor (LinearPair a) where
    lmap f (LinearPair a b) = LinearPair a (f b)

-- 线性和实例
instance LinearFunctor LinearSum where
    lmap f (Left a) = Left (f a)
    lmap f (Right b) = Right (f b)
```

## 线性类型检查

### 线性上下文

线性类型检查器维护一个线性上下文，记录每个变量的使用情况：

```haskell
-- 线性上下文
type LinearContext = Map String Usage

-- 使用情况
data Usage = Unused | Used | Consumed

-- 线性类型检查器
class LinearTypeChecker where
    checkLinear :: LinearContext -> Expr -> Type -> Bool
    updateContext :: LinearContext -> String -> Usage -> LinearContext
```

### 线性性检查规则

```haskell
-- 变量使用检查
checkVariable :: LinearContext -> String -> Type -> Bool
checkVariable ctx name typ = case lookup name ctx of
    Just Unused -> True
    Just Used -> False  -- 重复使用
    Just Consumed -> False  -- 已消耗
    Nothing -> False

-- 函数应用检查
checkApplication :: LinearContext -> Expr -> Expr -> Type -> Bool
checkApplication ctx fun arg result = 
    checkLinear ctx fun (LinearFunction argType resultType) &&
    checkLinear ctx arg argType &&
    mergeContexts ctx fun arg
```

## 线性类型推断

### 线性类型推断算法

```haskell
-- 线性类型推断
inferLinearType :: LinearContext -> Expr -> Maybe (Type, LinearContext)

-- 变量推断
inferVariable :: LinearContext -> String -> Maybe (Type, LinearContext)
inferVariable ctx name = case lookup name ctx of
    Just (LinearType typ) -> Just (typ, markUsed ctx name)
    _ -> Nothing

-- 函数推断
inferLambda :: LinearContext -> String -> Expr -> Maybe (Type, LinearContext)
inferLambda ctx param body = do
    (bodyType, bodyCtx) <- inferLinearType (addVariable ctx param) body
    return (LinearFunction paramType bodyType, removeVariable bodyCtx param)
```

## 线性类型系统特性

### 1. 资源安全

```haskell
-- 确保资源被正确管理
data Resource a = Resource a

-- 线性资源操作
useResource :: Resource a %1 -> (Resource a, a)
consumeResource :: Resource a %1 -> a
```

### 2. 并发安全

```haskell
-- 线性通道
data Channel a = Channel (MVar a)

-- 线性发送和接收
send :: Channel a %1 -> a -> Channel a
receive :: Channel a %1 -> (Channel a, a)
```

### 3. 内存管理

```haskell
-- 线性内存分配
data LinearArray a = LinearArray (Array Int a)

-- 线性数组操作
readArray :: LinearArray a %1 -> Int -> (LinearArray a, a)
writeArray :: LinearArray a %1 -> Int -> a -> LinearArray a
```

## 线性类型系统扩展

### 1. 仿射类型

仿射类型允许值被使用一次或丢弃，但不能重复使用：

```haskell
-- 仿射函数类型
type AffineFunction a b = a %ω -> b

-- 仿射类型类
class AffineType a where
    discard :: a %ω -> ()
```

### 2. 相关类型

相关类型允许值被使用任意次数：

```haskell
-- 相关函数类型
type RelevantFunction a b = a %ω -> b

-- 相关类型类
class RelevantType a where
    duplicate :: a %ω -> (a, a)
```

### 3. 分级类型

分级类型系统允许更精细的使用控制：

```haskell
-- 分级类型
data Grade = Zero | One | Many | Omega

-- 分级函数类型
type GradedFunction a b = a %Grade -> b
```

## 应用示例

### 1. 文件系统操作

```haskell
-- 线性文件句柄
data FileHandle = FileHandle Handle

-- 线性文件操作
readFile :: FileHandle %1 -> (FileHandle, String)
writeFile :: FileHandle %1 -> String -> FileHandle
closeFile :: FileHandle %1 -> ()

-- 使用示例
processFile :: FileHandle %1 -> String
processFile handle = 
    let (handle', content) = readFile handle
        handle'' = writeFile handle' (process content)
    in closeFile handle''
```

### 2. 数据库连接

```haskell
-- 线性数据库连接
data DBConnection = DBConnection Connection

-- 线性数据库操作
executeQuery :: DBConnection %1 -> Query -> (DBConnection, Result)
closeConnection :: DBConnection %1 -> ()

-- 使用示例
runTransaction :: DBConnection %1 -> Query -> Result
runTransaction conn query = 
    let (conn', result) = executeQuery conn query
    in closeConnection conn' `seq` result
```

### 3. 网络协议

```haskell
-- 线性网络连接
data NetworkConnection = NetworkConnection Socket

-- 线性网络操作
sendData :: NetworkConnection %1 -> ByteString -> NetworkConnection
receiveData :: NetworkConnection %1 -> (NetworkConnection, ByteString)
closeConnection :: NetworkConnection %1 -> ()

-- 使用示例
echoServer :: NetworkConnection %1 -> ()
echoServer conn = 
    let (conn', data) = receiveData conn
        conn'' = sendData conn' data
    in closeConnection conn''
```

## 理论意义

1. **资源管理**: 提供精确的资源管理机制
2. **并发安全**: 确保并发程序的正确性
3. **性能优化**: 支持编译时优化
4. **形式化验证**: 为程序验证提供理论基础

## 研究方向

1. **线性类型推断**: 自动推导线性类型
2. **线性效应系统**: 结合效应系统的线性类型
3. **线性协议**: 通信协议的线性类型
4. **量子计算**: 量子信息的线性类型
