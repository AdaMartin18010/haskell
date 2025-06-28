# 线性类型理论

## 概述

线性类型理论确保每个值恰好被使用一次，用于资源管理和内存安全。

## 核心概念

### 线性类型
```haskell
-- 线性类型确保值只使用一次
data Linear a = Linear a

-- 线性函数
linearId :: Linear a -> Linear a
linearId (Linear x) = Linear x

-- 不能复制线性值
-- duplicate :: Linear a -> (Linear a, Linear a) -- 类型错误
```

### 在Rust中的实现
```rust
// Rust的所有权系统实现线性类型
fn main() {
    let s1 = String::from("hello");
    let s2 = s1; // 所有权转移，s1不能再使用
    // println!("{}", s1); // 编译错误
}
```

## 应用场景

### 资源管理
```haskell
-- 文件句柄的线性使用
data FileHandle = FileHandle FilePath

openFile :: FilePath -> IO (Linear FileHandle)
openFile path = do
  handle <- openFile' path
  return (Linear handle)

closeFile :: Linear FileHandle -> IO ()
closeFile (Linear handle) = closeFile' handle

-- 确保文件被关闭
withFile :: FilePath -> (Linear FileHandle -> IO a) -> IO a
withFile path action = do
  handle <- openFile path
  result <- action handle
  closeFile handle
  return result
```

### 内存安全
```haskell
-- 线性数组
data LinearArray a = LinearArray [a]

-- 只能使用一次
readArray :: LinearArray a -> Int -> (LinearArray a, a)
readArray (LinearArray xs) i = (LinearArray xs, xs !! i)

-- 不能同时读取和修改
-- modifyArray :: LinearArray a -> Int -> a -> LinearArray a -- 需要更复杂的类型
```

## 类型系统

### 线性逻辑
```haskell
-- 线性逻辑连接词
-- A ⊗ B : 同时拥有A和B
-- A ⊸ B : 消耗A产生B
-- !A : 可以任意次使用的A

-- 在Haskell中模拟
data Tensor a b = Tensor a b
data Lollipop a b = Lollipop (a -> b)
data Bang a = Bang a
```

### 类型检查
```haskell
-- 线性类型检查器
type LinearContext = [(String, LinearType)]

data LinearType = LInt | LBool | LTensor LinearType LinearType | LLollipop LinearType LinearType

-- 线性类型检查
linearTypeCheck :: LinearContext -> Term -> Maybe LinearType
linearTypeCheck ctx (Var x) = lookup x ctx
linearTypeCheck ctx (Lam x t body) = do
  bodyType <- linearTypeCheck ((x, t) : ctx) body
  return $ LLollipop t bodyType
linearTypeCheck ctx (App f arg) = do
  fType <- linearTypeCheck ctx f
  argType <- linearTypeCheck ctx arg
  case fType of
    LLollipop t1 t2 | t1 == argType -> Just t2
    _ -> Nothing
```

## 实际应用

### 并发编程
```haskell
-- 线性通道
data LinearChannel a = LinearChannel (Chan a)

newChannel :: IO (LinearChannel a)
newChannel = do
  chan <- newChan
  return (LinearChannel chan)

send :: LinearChannel a -> a -> IO ()
send (LinearChannel chan) x = writeChan chan x

receive :: LinearChannel a -> IO a
receive (LinearChannel chan) = readChan chan
```

### 数据库连接
```haskell
-- 线性数据库连接
data LinearConnection = LinearConnection Connection

connect :: ConnectionString -> IO (LinearConnection)
connect connStr = do
  conn <- connect' connStr
  return (LinearConnection conn)

disconnect :: LinearConnection -> IO ()
disconnect (LinearConnection conn) = disconnect' conn

-- 确保连接被正确关闭
withConnection :: ConnectionString -> (LinearConnection -> IO a) -> IO a
withConnection connStr action = do
  conn <- connect connStr
  result <- action conn
  disconnect conn
  return result
```

## 优势

- **内存安全**: 防止内存泄漏
- **资源管理**: 确保资源正确释放
- **并发安全**: 防止数据竞争
- **性能优化**: 零成本抽象

## 挑战

- **学习曲线**: 概念复杂
- **编程模型**: 需要改变编程思维
- **生态系统**: 工具支持有限

---

**相关链接**：
- [编程语言理论](./001-Programming-Language-Theory.md)
- [仿射类型理论](./003-Affine-Type-Theory.md) 