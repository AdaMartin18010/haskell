# 仿射类型理论

## 概述

仿射类型理论允许值最多使用一次，比线性类型更灵活，但仍保证资源安全。

## 核心概念

### 仿射类型

```haskell
-- 仿射类型允许值最多使用一次
data Affine a = Affine a

-- 仿射函数
affineId :: Affine a -> Affine a
affineId (Affine x) = Affine x

-- 可以丢弃，但不能复制
discard :: Affine a -> ()
discard (Affine _) = ()

-- 不能复制
-- duplicate :: Affine a -> (Affine a, Affine a) -- 类型错误
```

### 在Rust中的实现

```rust
// Rust的借用系统实现仿射类型
fn main() {
    let mut s = String::from("hello");
    let r1 = &s; // 不可变借用
    let r2 = &s; // 不可变借用
    // let r3 = &mut s; // 编译错误：不能同时有可变和不可变借用
}
```

## 应用场景

### 资源管理

```haskell
-- 仿射文件句柄
data AffineFileHandle = AffineFileHandle FilePath

openFile :: FilePath -> IO (AffineFileHandle)
openFile path = do
  handle <- openFile' path
  return (AffineFileHandle path)

closeFile :: AffineFileHandle -> IO ()
closeFile (AffineFileHandle path) = closeFile' path

-- 可以选择关闭或不关闭
maybeClose :: AffineFileHandle -> Bool -> IO ()
maybeClose handle shouldClose = 
  if shouldClose then closeFile handle else discard handle
```

### 内存管理

```haskell
-- 仿射数组
data AffineArray a = AffineArray [a]

-- 可以读取一次或丢弃
readOrDiscard :: AffineArray a -> Int -> Either (AffineArray a, a) ()
readOrDiscard (AffineArray xs) i = 
  if i < length xs 
  then Left (AffineArray xs, xs !! i)
  else Right ()
```

## 类型系统

### 仿射逻辑

```haskell
-- 仿射逻辑连接词
-- A & B : 可以选择A或B
-- A ⊸ B : 消耗A产生B
-- !A : 可以任意次使用的A

-- 在Haskell中模拟
data With a b = With a b
data AffineArrow a b = AffineArrow (a -> b)
data Bang a = Bang a
```

### 类型检查

```haskell
-- 仿射类型检查器
type AffineContext = [(String, AffineType)]

data AffineType = AInt | ABool | AWith AffineType AffineType | AArrow AffineType AffineType

-- 仿射类型检查
affineTypeCheck :: AffineContext -> Term -> Maybe AffineType
affineTypeCheck ctx (Var x) = lookup x ctx
affineTypeCheck ctx (Lam x t body) = do
  bodyType <- affineTypeCheck ((x, t) : ctx) body
  return $ AArrow t bodyType
affineTypeCheck ctx (App f arg) = do
  fType <- affineTypeCheck ctx f
  argType <- affineTypeCheck ctx arg
  case fType of
    AArrow t1 t2 | t1 == argType -> Just t2
    _ -> Nothing
```

## 实际应用

### 并发编程

```haskell
-- 仿射锁
data AffineLock = AffineLock (MVar ())

newLock :: IO AffineLock
newLock = do
  mv <- newMVar ()
  return (AffineLock mv)

acquire :: AffineLock -> IO ()
acquire (AffineLock mv) = takeMVar mv

release :: AffineLock -> IO ()
release (AffineLock mv) = putMVar mv ()

-- 可以选择释放或不释放
withLock :: AffineLock -> IO a -> IO a
withLock lock action = do
  acquire lock
  result <- action
  release lock
  return result
```

### 数据库事务

```haskell
-- 仿射事务
data AffineTransaction = AffineTransaction Connection

beginTransaction :: Connection -> IO AffineTransaction
beginTransaction conn = do
  begin' conn
  return (AffineTransaction conn)

commit :: AffineTransaction -> IO ()
commit (AffineTransaction conn) = commit' conn

rollback :: AffineTransaction -> IO ()
rollback (AffineTransaction conn) = rollback' conn

-- 可以选择提交或回滚
withTransaction :: Connection -> (AffineTransaction -> IO a) -> IO a
withTransaction conn action = do
  trans <- beginTransaction conn
  result <- action trans
  commit trans
  return result
```

## 与线性类型的比较

| 特性 | 线性类型 | 仿射类型 |
|------|----------|----------|
| 使用次数 | 恰好一次 | 最多一次 |
| 灵活性 | 严格 | 较灵活 |
| 资源管理 | 强制 | 可选 |
| 实现复杂度 | 高 | 中等 |

## 优势

- **灵活性**: 允许丢弃值
- **资源安全**: 防止资源泄漏
- **并发安全**: 防止数据竞争
- **性能**: 零成本抽象

## 挑战

- **类型系统**: 复杂的类型检查
- **编程模型**: 需要适应新的编程模式
- **工具支持**: 需要专门的编译器支持

---

**相关链接**：

- [编程语言理论](./001-Programming-Language-Theory.md)
- [线性类型理论](./002-Linear-Type-Theory.md)
