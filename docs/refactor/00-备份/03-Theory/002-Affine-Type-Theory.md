# 仿射类型理论 (Affine Type Theory)

## 📚 概述

仿射类型理论是线性类型理论的扩展，它允许变量最多使用一次，为资源管理和内存安全提供了更灵活的形式化基础。本文档提供了仿射类型理论的完整数学形式化，包括公理系统、语义模型和 Haskell 实现。

**相关文档：**

- [[001-Linear-Type-Theory]] - 线性类型理论
- [[003-Temporal-Type-Theory]] - 时态类型理论
- [[004-Quantum-Type-Theory]] - 量子类型理论
- [[haskell/02-Type-System]] - Haskell 类型系统

## 1. 仿射逻辑基础

### 1.1 仿射逻辑公理系统

**定义 1.1 (仿射上下文)**
仿射上下文 $\Gamma$ 是变量到类型的映射，其中每个变量最多使用一次：
$$\Gamma : \text{Var} \rightarrow \text{Type}$$

**定义 1.2 (仿射类型)**
仿射类型系统包含以下类型构造子：
$$\tau ::= \text{Base} \mid \tau_1 \rightarrow \tau_2 \mid \tau_1 \& \tau_2 \mid \tau_1 \oplus \tau_2$$

其中：

- $\rightarrow$ 表示仿射函数类型
- $\&$ 表示加法积类型（with）
- $\oplus$ 表示加法类型（plus）

**公理 1.1 (仿射变量规则)**
$$\frac{x : \tau \in \Gamma}{\Gamma \vdash x : \tau}$$

**公理 1.2 (仿射抽象)**
$$\frac{\Gamma, x : \tau_1 \vdash e : \tau_2}{\Gamma \vdash \lambda x.e : \tau_1 \rightarrow \tau_2}$$

**公理 1.3 (仿射应用)**
$$\frac{\Gamma_1 \vdash e_1 : \tau_1 \rightarrow \tau_2 \quad \Gamma_2 \vdash e_2 : \tau_1}{\Gamma_1, \Gamma_2 \vdash e_1 e_2 : \tau_2}$$

**公理 1.4 (弱化规则)**
$$\frac{\Gamma \vdash e : \tau}{\Gamma, x : \tau' \vdash e : \tau}$$

### 1.2 Haskell 实现：仿射类型系统

```haskell
-- 仿射类型系统的基础类型
data AffineType where
  Base :: String -> AffineType
  AffineFun :: AffineType -> AffineType -> AffineType
  With :: AffineType -> AffineType -> AffineType
  Plus :: AffineType -> AffineType -> AffineType

-- 仿射上下文
type AffineContext = [(String, AffineType)]

-- 仿射表达式
data AffineExpr where
  Var :: String -> AffineExpr
  Lambda :: String -> AffineExpr -> AffineExpr
  App :: AffineExpr -> AffineExpr -> AffineExpr
  WithPair :: AffineExpr -> AffineExpr -> AffineExpr
  LetWith :: String -> String -> AffineExpr -> AffineExpr -> AffineExpr
  Inl :: AffineExpr -> AffineExpr
  Inr :: AffineExpr -> AffineExpr
  Case :: AffineExpr -> String -> AffineExpr -> String -> AffineExpr -> AffineExpr

-- 类型检查器
typeCheck :: AffineContext -> AffineExpr -> Maybe AffineType
typeCheck ctx (Var x) = lookup x ctx
typeCheck ctx (Lambda x body) = do
  let ctx' = (x, Base "a") : ctx
  resultType <- typeCheck ctx' body
  return $ AffineFun (Base "a") resultType
typeCheck ctx (App f arg) = do
  AffineFun argType resultType <- typeCheck ctx f
  argType' <- typeCheck ctx arg
  if argType == argType' then return resultType else Nothing
typeCheck ctx (WithPair e1 e2) = do
  t1 <- typeCheck ctx e1
  t2 <- typeCheck ctx e2
  return $ With t1 t2
typeCheck ctx (Inl e) = do
  t <- typeCheck ctx e
  return $ Plus t (Base "b")
typeCheck ctx (Inr e) = do
  t <- typeCheck ctx e
  return $ Plus (Base "a") t
```

### 1.3 仿射性约束

**定理 1.1 (仿射性保持)**
在仿射类型系统中，如果 $\Gamma \vdash e : \tau$，则 $\Gamma$ 中的每个变量在 $e$ 中最多出现一次。

**证明：** 通过结构归纳法证明。对于每个语法构造：

1. **变量**：直接满足仿射性
2. **抽象**：通过归纳假设，变量在体中最多出现一次
3. **应用**：通过上下文分离，确保变量不重复使用
4. **弱化**：允许变量不出现

```haskell
-- 仿射性检查器
checkAffinity :: AffineContext -> AffineExpr -> Bool
checkAffinity ctx expr = 
  let usedVars = collectVars expr
      ctxVars = map fst ctx
  in all (\v -> countOccurrences v usedVars <= 1) ctxVars

-- 收集表达式中的变量
collectVars :: AffineExpr -> [String]
collectVars (Var x) = [x]
collectVars (Lambda x body) = filter (/= x) (collectVars body)
collectVars (App f arg) = collectVars f ++ collectVars arg
collectVars (WithPair e1 e2) = collectVars e1 ++ collectVars e2
collectVars (LetWith x y body rest) = 
  filter (\v -> v /= x && v /= y) (collectVars body) ++ collectVars rest
collectVars (Inl e) = collectVars e
collectVars (Inr e) = collectVars e
collectVars (Case e x1 e1 x2 e2) = 
  collectVars e ++ 
  filter (/= x1) (collectVars e1) ++ 
  filter (/= x2) (collectVars e2)
```

**定理 1.2 (上下文分离)**
如果 $\Gamma_1, \Gamma_2 \vdash e : \tau$，则 $\Gamma_1$ 和 $\Gamma_2$ 中的变量集合不相交。

## 2. 所有权系统

### 2.1 所有权类型

**定义 2.1 (所有权类型)**
所有权类型表示对资源的独占控制：

```haskell
-- 所有权类型
data Ownership a where
  Owned :: a -> Ownership a
  Borrowed :: a -> Ownership a
  Shared :: a -> Ownership a

-- 所有权转移
transfer :: Ownership a -> (a -> b) -> Ownership b
transfer (Owned a) f = Owned (f a)
transfer (Borrowed a) f = Borrowed (f a)
transfer (Shared a) f = Shared (f a)

-- 所有权移动
move :: Ownership a -> a
move (Owned a) = a
move (Borrowed a) = a
move (Shared a) = a

-- 所有权借用
borrow :: Ownership a -> Borrowed a
borrow (Owned a) = Borrowed a
borrow (Borrowed a) = Borrowed a
borrow (Shared a) = Shared a
```

**定理 2.1 (所有权唯一性)**
在仿射类型系统中，每个资源最多有一个所有者。

**证明：** 通过仿射性约束：

1. 每个所有权变量最多使用一次
2. 转移操作消耗原所有权
3. 无法同时拥有多个所有权

### 2.2 生命周期管理

**定义 2.2 (生命周期)**
生命周期表示变量的有效作用域：

```haskell
-- 生命周期类型
data Lifetime where
  Static :: Lifetime
  Scope :: Lifetime -> Lifetime
  Region :: Lifetime -> Lifetime

-- 生命周期约束
data LifetimeConstraint where
  Outlives :: Lifetime -> Lifetime -> LifetimeConstraint
  SameRegion :: Lifetime -> Lifetime -> LifetimeConstraint

-- 生命周期检查器
checkLifetime :: LifetimeConstraint -> Bool
checkLifetime (Outlives l1 l2) = l1 /= l2
checkLifetime (SameRegion l1 l2) = l1 == l2

-- 生命周期管理
class LifetimeManager a where
  getLifetime :: a -> Lifetime
  checkLifetimeConstraint :: a -> a -> LifetimeConstraint -> Bool
```

**定理 2.2 (生命周期安全)**
在仿射类型系统中，不会出现悬空引用。

**证明：** 通过生命周期约束：

1. 每个引用都有明确的生命周期
2. 生命周期约束确保引用有效性
3. 编译器检查生命周期一致性

## 3. 内存管理理论

### 3.1 仿射引用

**定义 3.1 (仿射引用)**
仿射引用确保内存安全：

```haskell
-- 仿射引用类型
data AffineRef a where
  NewRef :: a -> AffineRef a
  ReadRef :: AffineRef a -> (a, AffineRef a)
  WriteRef :: AffineRef a -> a -> AffineRef a
  DropRef :: AffineRef a -> ()

-- 仿射引用的 Haskell 实现
newtype AffineRef' a = AffineRef' { unAffineRef :: IORef a }

-- 创建新引用
newAffineRef :: a -> IO (AffineRef' a)
newAffineRef value = AffineRef' <$> newIORef value

-- 读取引用（返回新引用）
readAffineRef :: AffineRef' a -> IO (a, AffineRef' a)
readAffineRef ref = do
  value <- readIORef (unAffineRef ref)
  newRef <- newIORef value
  return (value, AffineRef' newRef)

-- 写入引用
writeAffineRef :: AffineRef' a -> a -> IO (AffineRef' a)
writeAffineRef ref value = do
  writeIORef (unAffineRef ref) value
  newRef <- newIORef value
  return (AffineRef' newRef)

-- 丢弃引用
dropAffineRef :: AffineRef' a -> IO ()
dropAffineRef _ = return ()  -- 在 Haskell 中由 GC 处理
```

**定理 3.1 (内存安全)**
仿射引用系统保证：

1. 不会出现悬空指针
2. 不会重复释放内存
3. 不会出现数据竞争

**证明：** 通过仿射类型系统的性质：

1. 每个引用最多使用一次
2. 读取操作返回新的引用
3. 释放操作消耗引用

### 3.2 借用检查

**定义 3.2 (借用规则)**
借用检查规则：

```haskell
-- 借用类型
data Borrow where
  ImmutableBorrow :: AffineRef a -> Borrow a
  MutableBorrow :: AffineRef a -> Borrow a
  ReleaseBorrow :: Borrow a -> AffineRef a

-- 借用检查器
class BorrowChecker a where
  borrowImmutable :: a -> Borrow a
  borrowMutable :: a -> Borrow a
  releaseBorrow :: Borrow a -> a

-- 借用状态跟踪
data BorrowState = 
  NoBorrow | 
  ImmutableBorrows Int | 
  MutableBorrow

-- 借用管理器
newtype BorrowManager a = BorrowManager { unBorrowManager :: IORef (a, BorrowState) }

-- 创建借用管理器
newBorrowManager :: a -> IO (BorrowManager a)
newBorrowManager a = BorrowManager <$> newIORef (a, NoBorrow)

-- 不可变借用
borrowImmutable' :: BorrowManager a -> IO (Maybe (Borrow a))
borrowImmutable' (BorrowManager ref) = do
  (a, state) <- readIORef ref
  case state of
    NoBorrow -> do
      writeIORef ref (a, ImmutableBorrows 1)
      return $ Just (ImmutableBorrow undefined)
    ImmutableBorrows n -> do
      writeIORef ref (a, ImmutableBorrows (n + 1))
      return $ Just (ImmutableBorrow undefined)
    MutableBorrow -> return Nothing

-- 可变借用
borrowMutable' :: BorrowManager a -> IO (Maybe (Borrow a))
borrowMutable' (BorrowManager ref) = do
  (a, state) <- readIORef ref
  case state of
    NoBorrow -> do
      writeIORef ref (a, MutableBorrow)
      return $ Just (MutableBorrow undefined)
    _ -> return Nothing
```

**定理 3.2 (借用安全)**
借用系统保证：

1. 同时只能有一个可变借用或多个不可变借用
2. 借用不能超过被借用对象的生命周期
3. 借用释放后可以重新借用

## 4. 仿射逻辑的语义

### 4.1 指称语义

**定义 4.1 (仿射函数空间)**
仿射函数空间 $A \rightarrow B$ 的语义：
$$\llbracket A \rightarrow B \rrbracket = \llbracket A \rrbracket \rightarrow \llbracket B \rrbracket$$

**定义 4.2 (加法积语义)**
加法积 $A \& B$ 的语义：
$$\llbracket A \& B \rrbracket = \llbracket A \rrbracket \times \llbracket B \rrbracket$$

### 4.2 操作语义

**定义 4.3 (仿射归约)**
仿射归约规则：
$$(\lambda x.e) v \rightarrow e[v/x]$$

```haskell
-- 仿射归约实现
data AffineValue where
  LambdaVal :: String -> AffineExpr -> AffineValue
  WithVal :: AffineValue -> AffineValue -> AffineValue
  InlVal :: AffineValue -> AffineValue
  InrVal :: AffineValue -> AffineValue

-- 归约函数
reduce :: AffineExpr -> Maybe AffineExpr
reduce (App (Lambda x body) arg) = Just (substitute x arg body)
reduce (LetWith x y (WithPair e1 e2) body) = 
  Just (substitute x e1 (substitute y e2 body))
reduce (Case (Inl e) x1 e1 x2 e2) = Just (substitute x1 e e1)
reduce (Case (Inr e) x1 e1 x2 e2) = Just (substitute x2 e e2)
reduce _ = Nothing

-- 变量替换
substitute :: String -> AffineExpr -> AffineExpr -> AffineExpr
substitute x replacement (Var y) = 
  if x == y then replacement else Var y
substitute x replacement (Lambda y body) = 
  if x == y then Lambda y body 
  else Lambda y (substitute x replacement body)
substitute x replacement (App f arg) = 
  App (substitute x replacement f) (substitute x replacement arg)
substitute x replacement (WithPair e1 e2) = 
  WithPair (substitute x replacement e1) (substitute x replacement e2)
substitute x replacement (LetWith y z body rest) = 
  if x == y || x == z then LetWith y z body rest
  else LetWith y z (substitute x replacement body) (substitute x replacement rest)
substitute x replacement (Inl e) = Inl (substitute x replacement e)
substitute x replacement (Inr e) = Inr (substitute x replacement e)
substitute x replacement (Case e y1 e1 y2 e2) = 
  Case (substitute x replacement e) y1 e1 y2 e2
```

**定理 4.1 (仿射归约保持类型)**
如果 $\Gamma \vdash e : \tau$ 且 $e \rightarrow e'$，则 $\Gamma \vdash e' : \tau$。

## 5. 与线性类型的比较

### 5.1 类型系统对比

| 特性 | 线性类型 | 仿射类型 |
|------|----------|----------|
| 变量使用 | 恰好一次 | 最多一次 |
| 弱化规则 | 不允许 | 允许 |
| 资源管理 | 严格 | 灵活 |
| 内存安全 | 完全保证 | 完全保证 |

### 5.2 表达能力

**定理 5.1 (表达能力关系)**
仿射类型系统比线性类型系统更灵活，但表达能力相当。

**证明：** 通过类型系统嵌入：

1. 线性类型可以嵌入仿射类型
2. 仿射类型通过弱化规则提供更多灵活性
3. 两者都能保证内存安全

```haskell
-- 线性类型到仿射类型的嵌入
embedLinear :: LinearType -> AffineType
embedLinear (Base s) = Base s
embedLinear (LinearFun t1 t2) = AffineFun (embedLinear t1) (embedLinear t2)
embedLinear (Tensor t1 t2) = With (embedLinear t1) (embedLinear t2)
embedLinear (Exponential t) = embedLinear t

-- 仿射类型到线性类型的投影（部分）
projectAffine :: AffineType -> Maybe LinearType
projectAffine (Base s) = Just (Base s)
projectAffine (AffineFun t1 t2) = do
  lt1 <- projectAffine t1
  lt2 <- projectAffine t2
  return (LinearFun lt1 lt2)
projectAffine (With t1 t2) = do
  lt1 <- projectAffine t1
  lt2 <- projectAffine t2
  return (Tensor lt1 lt2)
projectAffine (Plus _ _) = Nothing  -- 无法投影
```

## 6. 实际应用

### 6.1 Rust 的所有权系统

Rust 的所有权系统基于仿射类型理论：

```rust
fn main() {
    let s = String::from("hello");
    let s2 = s;  // s 被移动到 s2，s 不再可用
    // println!("{}", s);  // 编译错误：s 已被移动
    println!("{}", s2);  // 正常工作
}
```

**定理 6.1 (Rust 内存安全)**
Rust 的所有权系统保证内存安全。

**证明：** 通过仿射类型系统的性质：

1. 每个值最多有一个所有者
2. 移动操作转移所有权
3. 借用检查防止数据竞争

### 6.2 Haskell 中的仿射类型

**定义 6.1 (仿射类型类)**:

```haskell
-- 仿射类型类
class Affine a where
  discard :: a -> ()
  useOnce :: a -> (a -> b) -> b

-- 仿射类型的实例
instance Affine FileHandle where
  discard handle = closeFile handle
  useOnce handle f = f handle

instance Affine (IORef a) where
  discard ref = writeIORef ref undefined
  useOnce ref f = f ref

-- 非线性类型的实例
instance Affine Int where
  discard _ = ()
  useOnce x f = f x

instance Affine String where
  discard _ = ()
  useOnce s f = f s

-- 仿射对类型
data AffinePair a b = AffinePair a b

-- 仿射对操作
fstAffine :: AffinePair a b -> a
fstAffine (AffinePair a _) = a

sndAffine :: AffinePair a b -> b
sndAffine (AffinePair _ b) = b

-- 仿射对构造
pairAffine :: a -> b -> AffinePair a b
pairAffine a b = AffinePair a b
```

**定理 6.2 (仿射函数性质)**
仿射函数满足：

1. 每个输入最多使用一次
2. 资源正确管理
3. 内存安全保证

## 7. 高级主题

### 7.1 仿射逻辑与范畴论

**定义 7.1 (仿射逻辑范畴)**
仿射逻辑范畴 $\mathcal{A}$ 是一个对称幺半范畴，满足：

1. **张量积**：$A \otimes B$
2. **内部 Hom**：$A \rightarrow B$
3. **单位对象**：$I$
4. **弱化**：$A \otimes I \cong A$

**定理 7.1 (仿射逻辑的范畴语义)**
仿射逻辑的范畴语义由对称幺半范畴给出。

### 7.2 仿射类型与并发

**定义 7.2 (仿射并发类型)**
仿射并发类型系统：

```haskell
-- 仿射通道
data AffineChannel a where
  NewChannel :: AffineChannel a
  Send :: AffineChannel a -> a -> AffineChannel ()
  Receive :: AffineChannel a -> (a, AffineChannel a)
  Close :: AffineChannel a -> ()

-- 仿射并发计算
newtype AffineConcurrent a = AffineConcurrent { runAffineConcurrent :: IO a }

instance Monad AffineConcurrent where
  return = AffineConcurrent . return
  AffineConcurrent m >>= f = AffineConcurrent $ m >>= runAffineConcurrent . f

-- 创建通道
newAffineChannel :: AffineConcurrent (AffineChannel a)
newAffineChannel = AffineConcurrent $ return NewChannel

-- 发送数据
sendAffine :: AffineChannel a -> a -> AffineConcurrent (AffineChannel ())
sendAffine channel value = AffineConcurrent $ do
  putStrLn $ "Sending: " ++ show value
  return (Send channel value)

-- 接收数据
receiveAffine :: AffineChannel a -> AffineConcurrent (a, AffineChannel a)
receiveAffine channel = AffineConcurrent $ do
  value <- return undefined  -- 实际实现中会从通道读取
  putStrLn $ "Received: " ++ show value
  return (value, Receive channel value)
```

## 8. 总结

仿射类型理论为资源管理和内存安全提供了灵活而强大的形式化基础。通过允许变量最多使用一次的约束，它确保了：

1. **资源安全**：每个资源最多使用一次
2. **内存安全**：避免悬空指针和数据竞争
3. **类型安全**：编译时检查资源使用模式
4. **灵活性**：支持弱化规则，提供更多编程便利

仿射类型理论在 Rust、Haskell 等现代编程语言中得到了广泛应用，为构建安全可靠的系统软件提供了理论基础。

---

**相关文档：**

- [[001-Linear-Type-Theory]] - 线性类型理论
- [[003-Temporal-Type-Theory]] - 时态类型理论
- [[004-Quantum-Type-Theory]] - 量子类型理论
- [[haskell/02-Type-System]] - Haskell 类型系统

**参考文献：**

1. Girard, J. Y. (1987). Linear logic. Theoretical computer science, 50(1), 1-101.
2. Wadler, P. (1990). Linear types can change the world! Programming concepts and methods, 546-566.
3. Rust Programming Language. (2021). The Rust Programming Language Book.
4. Peyton Jones, S. (2003). The Haskell 98 Language and Libraries: The Revised Report. Cambridge University Press.

---

**文档状态**：✅ 完成  
**最后更新**：2024-12-19  
**版本**：1.0
