# 线性类型理论基础

## 📋 概述

线性类型理论是类型系统的重要扩展，基于线性逻辑，确保资源的安全使用和管理。本文档介绍线性类型系统的完整理论体系，包括线性逻辑、资源管理、内存安全和实际应用。

## 🎯 线性逻辑基础

### 定义 1.1 (线性上下文)

线性上下文 $\Gamma$ 是变量到类型的映射，其中每个变量必须恰好使用一次：
$$\Gamma : \text{Var} \rightarrow \text{Type}$$

```haskell
-- 线性上下文
type LinearContext = [(String, LinearType)]

-- 空线性上下文
emptyLinearContext :: LinearContext
emptyLinearContext = []

-- 添加线性绑定
addLinearBinding :: LinearContext -> String -> LinearType -> LinearContext
addLinearBinding ctx x t = (x, t) : ctx

-- 查找线性类型
lookupLinearType :: LinearContext -> String -> Maybe LinearType
lookupLinearType [] _ = Nothing
lookupLinearType ((x', t) : ctx) x
    | x' == x = Just t
    | otherwise = lookupLinearType ctx x
```

### 定义 1.2 (线性类型)

线性类型系统包含以下类型构造子：
$$\tau ::= \text{Base} \mid \tau_1 \multimap \tau_2 \mid \tau_1 \otimes \tau_2 \mid !\tau$$

其中：

- $\multimap$ 表示线性函数类型
- $\otimes$ 表示张量积类型
- $!$ 表示指数类型（可重复使用）

```haskell
-- 线性类型定义
data LinearType = 
    LBase String
    | LLinArrow LinearType LinearType  -- τ₁ ⊸ τ₂
    | LTensor LinearType LinearType    -- τ₁ ⊗ τ₂
    | LExponential LinearType          -- !τ
    deriving (Show, Eq)

-- 线性类型示例
linearFunctionType :: LinearType
linearFunctionType = LLinArrow (LBase "Int") (LBase "Bool")

tensorType :: LinearType
tensorType = LTensor (LBase "String") (LBase "Int")

exponentialType :: LinearType
exponentialType = LExponential (LBase "Int")
```

### 公理 1.1 (线性变量规则)

$$\frac{x : \tau \in \Gamma}{\Gamma \vdash x : \tau}$$

### 公理 1.2 (线性抽象)

$$\frac{\Gamma, x : \tau_1 \vdash e : \tau_2}{\Gamma \vdash \lambda x.e : \tau_1 \multimap \tau_2}$$

### 公理 1.3 (线性应用)

$$\frac{\Gamma_1 \vdash e_1 : \tau_1 \multimap \tau_2 \quad \Gamma_2 \vdash e_2 : \tau_1}{\Gamma_1, \Gamma_2 \vdash e_1 e_2 : \tau_2}$$

```haskell
-- 线性表达式
data LinearExpr = 
    LVar String
    | LLambda String LinearType LinearExpr
    | LApp LinearExpr LinearExpr
    | LTensorPair LinearExpr LinearExpr
    | LLet LinearExpr String String LinearExpr
    | LPromote LinearExpr
    | LDerelict LinearExpr
    deriving (Show, Eq)

-- 线性类型检查器
linearTypeCheck :: LinearContext -> LinearExpr -> Either String LinearType
linearTypeCheck ctx (LVar x) = case lookupLinearType ctx x of
    Just t -> Right t
    Nothing -> Left ("Unbound linear variable: " ++ x)

linearTypeCheck ctx (LLambda x t1 e) = do
    t2 <- linearTypeCheck (addLinearBinding ctx x t1) e
    return (LLinArrow t1 t2)

linearTypeCheck ctx (LApp e1 e2) = do
    t1 <- linearTypeCheck ctx e1
    t2 <- linearTypeCheck ctx e2
    case t1 of
        LLinArrow t1' t2' | t1' == t2 -> Right t2'
        _ -> Left "Type mismatch in linear function application"

linearTypeCheck ctx (LTensorPair e1 e2) = do
    t1 <- linearTypeCheck ctx e1
    t2 <- linearTypeCheck ctx e2
    return (LTensor t1 t2)

linearTypeCheck ctx (LLet e1 x y e2) = do
    t1 <- linearTypeCheck ctx e1
    case t1 of
        LTensor t1' t2' -> do
            t3 <- linearTypeCheck (addLinearBinding (addLinearBinding ctx x t1') y t2') e2
            return t3
        _ -> Left "Let requires tensor type"

linearTypeCheck ctx (LPromote e) = do
    t <- linearTypeCheck ctx e
    return (LExponential t)

linearTypeCheck ctx (LDerelict e) = do
    t <- linearTypeCheck ctx e
    case t of
        LExponential t' -> Right t'
        _ -> Left "Derelict requires exponential type"
```

## 🔧 线性性约束

### 定理 1.1 (线性性保持)

在线性类型系统中，如果 $\Gamma \vdash e : \tau$，则 $\Gamma$ 中的每个变量在 $e$ 中恰好出现一次。

**证明：** 通过结构归纳法证明。对于每个语法构造：

1. **变量**：直接满足线性性
2. **抽象**：通过归纳假设，变量在体中恰好出现一次
3. **应用**：通过上下文分离，确保变量不重复使用

### 定理 1.2 (上下文分离)

如果 $\Gamma_1, \Gamma_2 \vdash e : \tau$，则 $\Gamma_1$ 和 $\Gamma_2$ 中的变量集合不相交。

```haskell
-- 线性性检查
checkLinearity :: LinearContext -> LinearExpr -> Bool
checkLinearity ctx expr = 
    let usedVars = collectUsedVars expr
        declaredVars = Set.fromList (map fst ctx)
    in usedVars == declaredVars && noDuplicates usedVars

-- 收集使用的变量
collectUsedVars :: LinearExpr -> Set String
collectUsedVars (LVar x) = Set.singleton x
collectUsedVars (LLambda x _ e) = collectUsedVars e
collectUsedVars (LApp e1 e2) = Set.union (collectUsedVars e1) (collectUsedVars e2)
collectUsedVars (LTensorPair e1 e2) = Set.union (collectUsedVars e1) (collectUsedVars e2)
collectUsedVars (LLet e1 x y e2) = Set.union (collectUsedVars e1) (collectUsedVars e2)
collectUsedVars (LPromote e) = collectUsedVars e
collectUsedVars (LDerelict e) = collectUsedVars e

-- 检查无重复
noDuplicates :: Set String -> Bool
noDuplicates = id  -- Set自动保证无重复
```

## 📊 资源管理理论

### 定义 2.1 (资源类型)

资源类型表示需要精确管理的系统资源：
$$\text{Resource} ::= \text{FileHandle} \mid \text{MemoryRef} \mid \text{NetworkConn} \mid \text{DatabaseConn}$$

```haskell
-- 资源类型
data ResourceType = 
    FileHandle
    | MemoryRef
    | NetworkConn
    | DatabaseConn
    deriving (Show, Eq)

-- 资源值
data Resource = 
    RFileHandle FilePath
    | RMemoryRef Int
    | RNetworkConn String
    | RDatabaseConn String
    deriving (Show, Eq)

-- 资源操作
data ResourceOp a where
    Create :: ResourceType -> ResourceOp Resource
    Use :: Resource -> (a -> b) -> ResourceOp b
    Destroy :: Resource -> ResourceOp ()
```

### 定理 2.1 (资源安全)

在线性类型系统中，资源不会被重复释放或遗忘。

**证明：** 通过线性性约束：

1. 每个资源变量必须恰好使用一次
2. 资源销毁操作消耗资源变量
3. 无法重复访问已销毁的资源

```haskell
-- 资源管理器
class ResourceManager r where
    createResource :: ResourceType -> IO r
    useResource :: r -> (a -> IO b) -> IO b
    destroyResource :: r -> IO ()

-- 文件句柄管理器
instance ResourceManager FilePath where
    createResource FileHandle = do
        path <- getTempFileName
        return path
    useResource path action = do
        handle <- openFile path ReadMode
        result <- action handle
        hClose handle
        return result
    destroyResource path = removeFile path

-- 内存引用管理器
instance ResourceManager (IORef a) where
    createResource MemoryRef = newIORef undefined
    useResource ref action = action ref
    destroyResource _ = return ()  -- 垃圾回收处理
```

### 定义 2.2 (线性引用)

线性引用确保内存安全：

```haskell
-- 线性引用
data LinearRef a where
    NewRef :: a -> LinearRef a
    ReadRef :: LinearRef a -> (a, LinearRef a)
    WriteRef :: LinearRef a -> a -> LinearRef a
    FreeRef :: LinearRef a -> ()

-- 线性引用操作
newLinearRef :: a -> LinearRef a
newLinearRef = NewRef

readLinearRef :: LinearRef a -> (a, LinearRef a)
readLinearRef = ReadRef

writeLinearRef :: LinearRef a -> a -> LinearRef a
writeLinearRef = WriteRef

freeLinearRef :: LinearRef a -> ()
freeLinearRef = FreeRef
```

### 定理 2.2 (内存安全)

线性引用系统保证：

1. 不会出现悬空指针
2. 不会重复释放内存
3. 不会出现数据竞争

**证明：** 通过线性类型系统的性质：

1. 每个引用最多使用一次
2. 读取操作返回新的引用
3. 释放操作消耗引用

## 🔍 线性逻辑的语义

### 定义 3.1 (线性函数空间)

线性函数空间 $A \multimap B$ 的语义：
$$\llbracket A \multimap B \rrbracket = \llbracket A \rrbracket \rightarrow \llbracket B \rrbracket$$

### 定义 3.2 (张量积语义)

张量积 $A \otimes B$ 的语义：
$$\llbracket A \otimes B \rrbracket = \llbracket A \rrbracket \times \llbracket B \rrbracket$$

```haskell
-- 线性语义域
data LinearValue = 
    LVBool Bool
    | LVInt Int
    | LVString String
    | LVClosure String LinearExpr LinearContext
    | LVTuple LinearValue LinearValue
    deriving Show

-- 线性语义解释
linearEval :: LinearContext -> LinearExpr -> Either String LinearValue
linearEval ctx (LVar x) = case lookupLinearType ctx x of
    Just _ -> Left "Cannot evaluate variable"
    Nothing -> Left "Unbound variable"

linearEval ctx (LLambda x t e) = Right (LVClosure x e ctx)

linearEval ctx (LApp e1 e2) = do
    v1 <- linearEval ctx e1
    v2 <- linearEval ctx e2
    case v1 of
        LVClosure x e ctx' -> linearEval (addLinearBinding ctx' x (getType v2)) e
        _ -> Left "Type error in linear application"

linearEval ctx (LTensorPair e1 e2) = do
    v1 <- linearEval ctx e1
    v2 <- linearEval ctx e2
    return (LVTuple v1 v2)

linearEval ctx (LLet e1 x y e2) = do
    v1 <- linearEval ctx e1
    case v1 of
        LVTuple v1' v2' -> linearEval (addLinearBinding (addLinearBinding ctx x (getType v1')) y (getType v2')) e2
        _ -> Left "Let requires tuple value"

linearEval ctx (LPromote e) = linearEval ctx e

linearEval ctx (LDerelict e) = linearEval ctx e

-- 获取值的类型
getType :: LinearValue -> LinearType
getType (LVBool _) = LBase "Bool"
getType (LVInt _) = LBase "Int"
getType (LVString _) = LBase "String"
getType (LVClosure _ _ _) = error "Cannot get type of closure"
getType (LVTuple v1 v2) = LTensor (getType v1) (getType v2)
```

### 定义 3.3 (线性归约)

线性归约规则：
$$(\lambda x.e) v \rightarrow e[v/x]$$

### 定理 3.1 (线性归约保持类型)

如果 $\Gamma \vdash e : \tau$ 且 $e \rightarrow e'$，则 $\Gamma \vdash e' : \tau$。

```haskell
-- 线性归约
linearStep :: LinearExpr -> Maybe LinearExpr
linearStep (LApp (LLambda x _ e1) e2) = Just (linearSubstitute x e2 e1)
linearStep (LApp e1 e2) = case linearStep e1 of
    Just e1' -> Just (LApp e1' e2)
    Nothing -> case linearStep e2 of
        Just e2' -> Just (LApp e1 e2')
        Nothing -> Nothing
linearStep (LLet (LTensorPair e1 e2) x y e3) = Just (linearSubstitute x e1 (linearSubstitute y e2 e3))
linearStep _ = Nothing

-- 线性替换
linearSubstitute :: String -> LinearExpr -> LinearExpr -> LinearExpr
linearSubstitute x e (LVar y)
    | x == y = e
    | otherwise = LVar y
linearSubstitute x e (LLambda y t e1)
    | x == y = LLambda y t e1
    | otherwise = LLambda y t (linearSubstitute x e e1)
linearSubstitute x e (LApp e1 e2) = LApp (linearSubstitute x e e1) (linearSubstitute x e e2)
linearSubstitute x e (LTensorPair e1 e2) = LTensorPair (linearSubstitute x e e1) (linearSubstitute x e e2)
linearSubstitute x e (LLet e1 y z e2) = LLet (linearSubstitute x e e1) y z (linearSubstitute x e e2)
linearSubstitute x e (LPromote e1) = LPromote (linearSubstitute x e e1)
linearSubstitute x e (LDerelict e1) = LDerelict (linearSubstitute x e e1)
```

## 📈 指数类型 (!)

### 公理 4.1 (弱化)

$$\frac{\Gamma \vdash e : \tau}{\Gamma, x : !\tau \vdash e : \tau}$$

### 公理 4.2 (收缩)

$$\frac{\Gamma, x : !\tau, y : !\tau \vdash e : \sigma}{\Gamma, z : !\tau \vdash e[z/x, z/y] : \sigma}$$

### 公理 4.3 (提升)

$$\frac{!\Gamma \vdash e : \tau}{!\Gamma \vdash !e : !\tau}$$

### 定义 4.1 (指数类型语义)

指数类型 $!A$ 的语义：
$$\llbracket !A \rrbracket = \text{Comonad}(\llbracket A \rrbracket)$$

### 定理 4.1 (指数类型性质)

指数类型满足：

1. 可重复使用
2. 支持弱化和收缩
3. 形成余单子结构

```haskell
-- 指数类型操作
class Exponential a where
    weaken :: a -> a
    contract :: a -> (a, a)
    promote :: a -> a

-- 指数类型实例
instance Exponential (LExponential LinearType) where
    weaken = id
    contract t = (t, t)
    promote = id
```

## 🔧 线性类型系统的扩展

### 定义 5.1 (仿射类型)

仿射类型允许变量最多使用一次：
$$\tau ::= \text{Base} \mid \tau_1 \rightarrow \tau_2 \mid \tau_1 \& \tau_2$$

### 公理 5.1 (仿射弱化)

$$\frac{\Gamma \vdash e : \tau}{\Gamma, x : \tau' \vdash e : \tau}$$

```haskell
-- 仿射类型
data AffineType = 
    ABase String
    | AArrow AffineType AffineType
    | AWith AffineType AffineType  -- τ₁ & τ₂
    deriving (Show, Eq)

-- 仿射表达式
data AffineExpr = 
    AVar String
    | ALambda String AffineType AffineExpr
    | AApp AffineExpr AffineExpr
    | AWithPair AffineExpr AffineExpr
    | AProj1 AffineExpr
    | AProj2 AffineExpr
    deriving (Show, Eq)
```

### 定义 5.2 (相关类型)

相关类型允许变量至少使用一次：
$$\tau ::= \text{Base} \mid \tau_1 \rightarrow \tau_2 \mid \tau_1 \oplus \tau_2$$

```haskell
-- 相关类型
data RelevantType = 
    RBase String
    | RArrow RelevantType RelevantType
    | RPlus RelevantType RelevantType  -- τ₁ ⊕ τ₂
    deriving (Show, Eq)

-- 相关表达式
data RelevantExpr = 
    RVar String
    | RLambda String RelevantType RelevantExpr
    | RApp RelevantExpr RelevantExpr
    | RInl RelevantExpr
    | RInr RelevantExpr
    | RCase RelevantExpr String RelevantExpr String RelevantExpr
    deriving (Show, Eq)
```

## 🚀 实际应用

### Rust 的所有权系统

Rust 的所有权系统基于线性类型理论：

```rust
fn consume_string(s: String) {
    // s 被消费，无法再次使用
}

fn main() {
    let s = String::from("hello");
    consume_string(s);
    // 这里无法使用 s，因为它已经被消费
}
```

### 定理 6.1 (Rust 内存安全)

Rust 的所有权系统保证内存安全。

**证明：** 通过线性类型系统的性质：

1. 每个值最多有一个所有者
2. 移动操作转移所有权
3. 借用检查防止数据竞争

```haskell
-- Rust风格的所有权系统模拟
class Owned a where
    move :: a -> a
    borrow :: a -> &a
    drop :: a -> ()

-- 所有权类型
data Owned a = Owned a

instance Owned a where
    move (Owned x) = Owned x
    borrow (Owned x) = &x
    drop (Owned _) = ()
```

### 函数式编程中的线性类型

```haskell
-- 线性函数类
class Linear a where
    consume :: a -> ()
    duplicate :: a -> (a, a)  -- 仅对非线性类型可用

-- 线性类型实例
instance Linear (LinearRef a) where
    consume = freeLinearRef
    duplicate = error "Cannot duplicate linear reference"

instance Linear Bool where
    consume _ = ()
    duplicate x = (x, x)  -- 布尔值可以复制
```

### 定理 6.2 (线性函数性质)

线性函数满足：

1. 资源安全：不会重复释放资源
2. 内存安全：不会出现悬空指针
3. 并发安全：不会出现数据竞争

## 🔗 相关链接

### 理论基础

- [简单类型理论](./001-Simple-Type-Theory.md)
- [范畴论](../03-Category-Theory/001-Basic-Concepts.md)
- [线性逻辑](../02-Formal-Logic/001-Propositional-Logic.md)

### 高级类型理论

- [仿射类型理论](./003-Affine-Type-Theory.md)
- [相关类型理论](./004-Relevant-Type-Theory.md)
- [量子类型理论](./005-Quantum-Type-Theory.md)

### 实际应用

- [Rust编程](../haskell/15-Advanced-Architecture/001-Ownership-System.md)
- [内存管理](../haskell/12-System-Programming/001-Memory-Management.md)
- [并发编程](../haskell/08-Concurrency/001-Thread-Safety.md)

---

**最后更新**: 2024年12月
**版本**: 1.0
**状态**: ✅ 完成
**维护者**: 形式化知识体系团队
