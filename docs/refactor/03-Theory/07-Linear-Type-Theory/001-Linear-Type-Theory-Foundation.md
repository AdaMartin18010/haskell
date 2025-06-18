# 线性类型理论基础

## 📚 快速导航

### 相关理论
- [形式语言理论](../01-Programming-Language-Theory/001-Syntax-Theory.md)
- [类型系统理论](../04-Type-Theory/001-Simple-Type-Theory.md)
- [范畴论基础](../02-Formal-Science/03-Category-Theory/001-Basic-Concepts.md)

### 实现示例
- [Haskell实现](../../haskell/04-Type-System/001-Type-System-Foundation.md)
- [形式化验证](../../haskell/13-Formal-Verification/001-Formal-Verification-Foundation.md)

### 应用领域
- [资源管理](../../06-Architecture/01-Design-Patterns/001-Creational-Patterns.md)
- [内存安全](../../07-Implementation/01-Compiler-Design/001-Lexical-Analysis.md)

## 🎯 概述

线性类型理论是现代编程语言理论的核心组成部分，它基于线性逻辑，确保资源的安全管理和使用。本文档提供线性类型理论的严格数学定义、形式化语义和Haskell实现。

## 📖 1. 线性逻辑基础

### 1.1 线性上下文

**定义 1.1 (线性上下文)**
线性上下文 $\Gamma$ 是变量到类型的映射，其中每个变量必须恰好使用一次：

$$\Gamma : \text{Var} \rightarrow \text{Type}$$

**Haskell实现：**

```haskell
-- 线性上下文表示
type LinearContext = Map String Type

-- 空上下文
emptyContext :: LinearContext
emptyContext = Map.empty

-- 添加上下文
addToContext :: String -> Type -> LinearContext -> LinearContext
addToContext var ty ctx = Map.insert var ty ctx

-- 检查变量是否在上下文中
inContext :: String -> LinearContext -> Bool
inContext var ctx = Map.member var ctx
```

### 1.2 线性类型语法

**定义 1.2 (线性类型)**
线性类型系统包含以下类型构造子：

$$\tau ::= \text{Base} \mid \tau_1 \multimap \tau_2 \mid \tau_1 \otimes \tau_2 \mid !\tau$$

其中：
- $\multimap$ 表示线性函数类型
- $\otimes$ 表示张量积类型  
- $!$ 表示指数类型（可重复使用）

**Haskell实现：**

```haskell
-- 线性类型定义
data LinearType where
  BaseType :: String -> LinearType
  LinearArrow :: LinearType -> LinearType -> LinearType  -- ⊸
  Tensor :: LinearType -> LinearType -> LinearType       -- ⊗
  Exponential :: LinearType -> LinearType                -- !
  deriving (Eq, Show)

-- 类型构造器
infixr 0 ⊸
(⊸) :: LinearType -> LinearType -> LinearType
(⊸) = LinearArrow

infixr 1 ⊗
(⊗) :: LinearType -> LinearType -> LinearType
(⊗) = Tensor

-- 指数类型构造器
bang :: LinearType -> LinearType
bang = Exponential
```

### 1.3 线性类型规则

**公理 1.1 (线性变量规则)**
$$\frac{x : \tau \in \Gamma}{\Gamma \vdash x : \tau}$$

**公理 1.2 (线性抽象)**
$$\frac{\Gamma, x : \tau_1 \vdash e : \tau_2}{\Gamma \vdash \lambda x.e : \tau_1 \multimap \tau_2}$$

**公理 1.3 (线性应用)**
$$\frac{\Gamma_1 \vdash e_1 : \tau_1 \multimap \tau_2 \quad \Gamma_2 \vdash e_2 : \tau_1}{\Gamma_1, \Gamma_2 \vdash e_1 e_2 : \tau_2}$$

**Haskell实现：**

```haskell
-- 类型推导系统
data TypeJudgment = TypeJudgment LinearContext Expr LinearType

-- 类型推导规则
class TypeInference a where
  inferType :: LinearContext -> a -> Maybe TypeJudgment

-- 变量规则
varRule :: String -> LinearType -> LinearContext -> TypeJudgment
varRule var ty ctx = TypeJudgment ctx (Var var) ty

-- 抽象规则
absRule :: String -> LinearType -> Expr -> LinearType -> TypeJudgment -> TypeJudgment
absRule var ty1 body ty2 (TypeJudgment ctx _ _) = 
  TypeJudgment (Map.delete var ctx) (Lambda var body) (ty1 ⊸ ty2)

-- 应用规则
appRule :: TypeJudgment -> TypeJudgment -> Maybe TypeJudgment
appRule (TypeJudgment ctx1 e1 (LinearArrow ty1 ty2)) 
        (TypeJudgment ctx2 e2 ty1') 
  | ty1 == ty1' && disjoint ctx1 ctx2 = 
      Just $ TypeJudgment (ctx1 `union` ctx2) (App e1 e2) ty2
  | otherwise = Nothing
```

## 🔧 2. 线性性约束

### 2.1 线性性保持定理

**定理 1.1 (线性性保持)**
在线性类型系统中，如果 $\Gamma \vdash e : \tau$，则 $\Gamma$ 中的每个变量在 $e$ 中恰好出现一次。

**证明：** 通过结构归纳法证明。对于每个语法构造：

1. **变量**：直接满足线性性
2. **抽象**：通过归纳假设，变量在体中恰好出现一次
3. **应用**：通过上下文分离，确保变量不重复使用

**Haskell实现：**

```haskell
-- 线性性检查
class LinearCheck a where
  isLinear :: a -> Bool
  freeVars :: a -> Set String

-- 表达式线性性检查
instance LinearCheck Expr where
  isLinear (Var x) = True
  isLinear (Lambda x e) = isLinear e
  isLinear (App e1 e2) = 
    isLinear e1 && isLinear e2 && 
    Set.disjoint (freeVars e1) (freeVars e2)
  
  freeVars (Var x) = Set.singleton x
  freeVars (Lambda x e) = Set.delete x (freeVars e)
  freeVars (App e1 e2) = Set.union (freeVars e1) (freeVars e2)

-- 线性性验证
validateLinearity :: TypeJudgment -> Bool
validateLinearity (TypeJudgment ctx expr ty) = 
  let ctxVars = Set.fromList (Map.keys ctx)
      exprVars = freeVars expr
  in ctxVars == exprVars && isLinear expr
```

### 2.2 上下文分离定理

**定理 1.2 (上下文分离)**
如果 $\Gamma_1, \Gamma_2 \vdash e : \tau$，则 $\Gamma_1$ 和 $\Gamma_2$ 中的变量集合不相交。

**Haskell实现：**

```haskell
-- 上下文分离检查
disjoint :: LinearContext -> LinearContext -> Bool
disjoint ctx1 ctx2 = 
  Set.disjoint (Set.fromList (Map.keys ctx1)) 
               (Set.fromList (Map.keys ctx2))

-- 上下文合并
union :: LinearContext -> LinearContext -> LinearContext
union ctx1 ctx2 = Map.union ctx1 ctx2

-- 上下文分离验证
validateContextSeparation :: TypeJudgment -> Bool
validateContextSeparation (TypeJudgment ctx expr ty) = 
  case expr of
    App e1 e2 -> 
      let (ctx1, ctx2) = splitContext ctx expr
      in disjoint ctx1 ctx2
    _ -> True
```

## 💾 3. 资源管理理论

### 3.1 资源类型系统

**定义 2.1 (资源类型)**
资源类型表示需要精确管理的系统资源：

$$\text{Resource} ::= \text{FileHandle} \mid \text{MemoryRef} \mid \text{NetworkConn} \mid \text{DatabaseConn}$$

**Haskell实现：**

```haskell
-- 资源类型定义
data ResourceType where
  FileHandle :: ResourceType
  MemoryRef :: ResourceType
  NetworkConn :: ResourceType
  DatabaseConn :: ResourceType
  deriving (Eq, Show)

-- 资源操作
data ResourceOp a where
  Create :: ResourceType -> ResourceOp Resource
  Use    :: Resource -> (a -> b) -> ResourceOp b
  Destroy :: Resource -> ResourceOp ()

-- 资源抽象
newtype Resource = Resource { resourceId :: Int }
  deriving (Eq, Show)

-- 资源管理器
class ResourceManager m where
  createResource :: ResourceType -> m Resource
  useResource :: Resource -> (a -> b) -> m b
  destroyResource :: Resource -> m ()
```

### 3.2 资源安全定理

**定理 2.1 (资源安全)**
在线性类型系统中，资源不会被重复释放或遗忘。

**证明：** 通过线性性约束：

1. 每个资源变量必须恰好使用一次
2. 资源销毁操作消耗资源变量
3. 无法重复访问已销毁的资源

**Haskell实现：**

```haskell
-- 线性资源类型
newtype LinearResource a = LinearResource { unResource :: a }

-- 资源操作的安全包装
class LinearResource a where
  consume :: LinearResource a -> a
  duplicate :: LinearResource a -> (LinearResource a, LinearResource a)  -- 仅对非线性类型

-- 文件句柄的线性管理
newtype LinearFileHandle = LinearFileHandle FilePath

instance LinearResource LinearFileHandle where
  consume (LinearFileHandle path) = LinearFileHandle path
  -- 文件句柄不支持重复，因此没有duplicate实现

-- 安全的文件操作
safeFileOperation :: LinearFileHandle -> (FilePath -> IO a) -> IO a
safeFileOperation (LinearFileHandle path) op = op path
```

---

**继续阅读**：[线性类型理论第二部分](./002-Linear-Type-Theory-Advanced.md) 