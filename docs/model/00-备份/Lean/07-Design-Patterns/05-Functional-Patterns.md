# Lean 函数式设计模式

## 🎯 概述

函数式设计模式是Lean的核心特色，通过Monad、Applicative、Arrow等抽象实现类型安全、可组合的函数式编程模式。

## 🔄 Monad模式

### 基础Monad

```lean
-- Monad模式
namespace MonadPattern

-- Monad类型类
class Monad (m : Type → Type) where
  pure : α → m α
  bind : m α → (α → m β) → m β

-- Maybe Monad
instance : Monad Option where
  pure := some
  bind := Option.bind

-- List Monad
instance : Monad List where
  pure x := [x]
  bind xs f := List.join (List.map f xs)

-- IO Monad
instance : Monad IO where
  pure := IO.pure
  bind := IO.bind

-- Monad使用示例
def safeDivide (x y : Float) : Option Float :=
  if y == 0.0 then none else some (x / y)

def monadExample : Option Float := do
  let a ← safeDivide 10.0 2.0
  let b ← safeDivide a 3.0
  return b

-- 错误处理Monad
def Result (α β : Type) := α ⊕ β

instance : Monad (Result α) where
  pure := Sum.inl
  bind := fun ma f =>
    match ma with
    | Sum.inl a => f a
    | Sum.inr e => Sum.inr e

end MonadPattern
```

### Monad变换器

```lean
-- Monad变换器
namespace MonadTransformer

-- MaybeT变换器
structure MaybeT (m : Type → Type) (α : Type) where
  runMaybeT : m (Option α)

instance [Monad m] : Monad (MaybeT m) where
  pure x := { runMaybeT := pure (some x) }
  bind ma f := 
    { runMaybeT := do
        let a ← ma.runMaybeT
        match a with
        | none => pure none
        | some x => (f x).runMaybeT }

-- ReaderT变换器
structure ReaderT (r : Type) (m : Type → Type) (α : Type) where
  runReaderT : r → m α

instance [Monad m] : Monad (ReaderT r m) where
  pure x := { runReaderT := fun _ => pure x }
  bind ma f := 
    { runReaderT := fun r => do
        let a ← ma.runReaderT r
        (f a).runReaderT r }

-- StateT变换器
structure StateT (s : Type) (m : Type → Type) (α : Type) where
  runStateT : s → m (α × s)

instance [Monad m] : Monad (StateT s m) where
  pure x := { runStateT := fun s => pure (x, s) }
  bind ma f := 
    { runStateT := fun s => do
        let (a, s') ← ma.runStateT s
        (f a).runStateT s' }

-- 组合Monad
def AppM := StateT String (ReaderT Int IO)

instance : Monad AppM where
  pure := Monad.pure
  bind := Monad.bind

end MonadTransformer
```

## ⚡ Applicative模式

### 基础Applicative

```lean
-- Applicative模式
namespace ApplicativePattern

-- Applicative类型类
class Applicative (f : Type → Type) extends Functor f where
  pure : α → f α
  seq : f (α → β) → f α → f β

-- Maybe Applicative
instance : Applicative Option where
  pure := some
  seq := fun f x =>
    match f, x with
    | some g, some a => some (g a)
    | _, _ => none

-- List Applicative
instance : Applicative List where
  pure x := [x]
  seq := fun fs xs => 
    List.join (List.map (fun f => List.map f xs) fs)

-- 函数Applicative
instance : Applicative (fun r => r → α) where
  pure x := fun _ => x
  seq := fun f g r => f r (g r)

-- Applicative使用示例
def applicativeExample : Option Int :=
  pure (· + ·) <*> some 5 <*> some 3

def listApplicative : List Int :=
  pure (· + ·) <*> [1, 2] <*> [10, 20]

end ApplicativePattern
```

### Applicative组合

```lean
-- Applicative组合
namespace ApplicativeComposition

-- 组合Applicative
def Compose (f g : Type → Type) (α : Type) := f (g α)

instance [Applicative f] [Applicative g] : Applicative (Compose f g) where
  pure x := pure (pure x)
  seq := fun f x => 
    pure (· <*> ·) <*> f <*> x

-- 验证Applicative
def Validation (e α : Type) := e ⊕ α

instance [Semigroup e] : Applicative (Validation e) where
  pure := Sum.inr
  seq := fun f x =>
    match f, x with
    | Sum.inl e1, Sum.inl e2 => Sum.inl (e1 <> e2)
    | Sum.inl e, Sum.inr _ => Sum.inl e
    | Sum.inr _, Sum.inl e => Sum.inl e
    | Sum.inr g, Sum.inr a => Sum.inr (g a)

-- 使用验证Applicative
def validateName (name : String) : Validation String String :=
  if name.length > 0 then Sum.inr name else Sum.inl "Name cannot be empty"

def validateAge (age : Int) : Validation String Int :=
  if age > 0 then Sum.inr age else Sum.inl "Age must be positive"

def validateUser (name : String) (age : Int) : Validation String (String × Int) :=
  pure (·, ·) <*> validateName name <*> validateAge age

end ApplicativeComposition
```

## 🏹 Arrow模式

### 基础Arrow

```lean
-- Arrow模式
namespace ArrowPattern

-- Arrow类型类
class Arrow (arr : Type → Type → Type) where
  arr : (α → β) → arr α β
  first : arr α β → arr (α × γ) (β × γ)
  second : arr α β → arr (γ × α) (γ × β)
  (>>>) : arr α β → arr β γ → arr α γ

-- 函数Arrow
instance : Arrow (fun α β => α → β) where
  arr f := f
  first f := fun (a, c) => (f a, c)
  second f := fun (c, a) => (c, f a)
  (>>>) f g := g ∘ f

-- Kleisli Arrow
structure Kleisli (m : Type → Type) (α β : Type) where
  runKleisli : α → m β

instance [Monad m] : Arrow (Kleisli m) where
  arr f := { runKleisli := fun x => pure (f x) }
  first f := { runKleisli := fun (a, c) => do
    let b ← f.runKleisli a
    return (b, c) }
  second f := { runKleisli := fun (c, a) => do
    let b ← f.runKleisli a
    return (c, b) }
  (>>>) f g := { runKleisli := fun x => do
    let y ← f.runKleisli x
    g.runKleisli y }

-- Arrow使用示例
def arrowExample : Kleisli Option Int String :=
  arr (· * 2) >>> arr toString >>> arr (· ++ "!")

def result := arrowExample.runKleisli 5

end ArrowPattern
```

### Arrow组合

```lean
-- Arrow组合
namespace ArrowComposition

-- Arrow选择
class ArrowChoice (arr : Type → Type → Type) extends Arrow arr where
  left : arr α β → arr (α ⊕ γ) (β ⊕ γ)
  right : arr α β → arr (γ ⊕ α) (γ ⊕ β)

instance : ArrowChoice (fun α β => α → β) where
  left f := fun x =>
    match x with
    | Sum.inl a => Sum.inl (f a)
    | Sum.inr c => Sum.inr c
  right f := fun x =>
    match x with
    | Sum.inl c => Sum.inl c
    | Sum.inr a => Sum.inr (f a)

-- Arrow应用
class ArrowApply (arr : Type → Type → Type) extends Arrow arr where
  app : arr (arr α β × α) β

instance : ArrowApply (fun α β => α → β) where
  app := fun (f, a) => f a

-- 使用Arrow组合
def processData : Kleisli Option Int String :=
  arr (· * 2) >>> arr toString

def validateInput : Kleisli Option Int Int :=
  arr (fun x => if x > 0 then x else 0)

def pipeline := validateInput >>> processData

end ArrowComposition
```

## 🎭 Free Monad模式

### 基础Free Monad

```lean
-- Free Monad模式
namespace FreeMonad

-- Free Monad定义
inductive Free (f : Type → Type) (α : Type)
  | Pure : α → Free f α
  | Free : f (Free f α) → Free f α

instance [Functor f] : Functor (Free f) where
  fmap f := fun x =>
    match x with
    | Free.Pure a => Free.Pure (f a)
    | Free.Free fa => Free.Free (fmap (fmap f) fa)

instance [Functor f] : Applicative (Free f) where
  pure := Free.Pure
  seq := fun f x =>
    match f, x with
    | Free.Pure g, Free.Pure a => Free.Pure (g a)
    | Free.Pure g, Free.Free fa => Free.Free (fmap (fmap g) fa)
    | Free.Free ff, a => Free.Free (fmap (fun f' => f' <*> a) ff)

instance [Functor f] : Monad (Free f) where
  pure := Free.Pure
  bind := fun ma k =>
    match ma with
    | Free.Pure a => k a
    | Free.Free fa => Free.Free (fmap (fun ma' => ma' >>= k) fa)

-- 代数效应
data FileSystemF a
  | ReadFile : String → (String → a) → FileSystemF a
  | WriteFile : String → String → a → FileSystemF a
  | DeleteFile : String → a → FileSystemF a

instance : Functor FileSystemF where
  fmap f := fun x =>
    match x with
    | FileSystemF.ReadFile path k => FileSystemF.ReadFile path (f ∘ k)
    | FileSystemF.WriteFile path content a => FileSystemF.WriteFile path content (f a)
    | FileSystemF.DeleteFile path a => FileSystemF.DeleteFile path (f a)

type FileSystem = Free FileSystemF

-- 智能构造函数
def readFile (path : String) : FileSystem String :=
  Free.Free (FileSystemF.ReadFile path Free.Pure)

def writeFile (path : String) (content : String) : FileSystem Unit :=
  Free.Free (FileSystemF.WriteFile path content (Free.Pure ()))

def deleteFile (path : String) : FileSystem Unit :=
  Free.Free (FileSystemF.DeleteFile path (Free.Pure ()))

-- 解释器
def interpretFileSystem : FileSystem α → IO α
  | Free.Pure a => pure a
  | Free.Free fa =>
    match fa with
    | FileSystemF.ReadFile path k => do
      let content ← IO.readFile path
      interpretFileSystem (k content)
    | FileSystemF.WriteFile path content a => do
      IO.writeFile path content
      interpretFileSystem a
    | FileSystemF.DeleteFile path a => do
      IO.removeFile path
      interpretFileSystem a

-- 使用Free Monad
def fileOperation : FileSystem String := do
  writeFile "test.txt" "Hello, World!"
  let content ← readFile "test.txt"
  deleteFile "test.txt"
  return content

def result ← interpretFileSystem fileOperation

end FreeMonad
```

## 🏷️ Tagless Final模式

### 基础Tagless Final

```lean
-- Tagless Final模式
namespace TaglessFinal

-- 代数接口
class Monad m => FileSystem m where
  readFile : String → m String
  writeFile : String → String → m Unit
  deleteFile : String → m Unit

class Monad m => Logger m where
  log : String → m Unit
  logError : String → m Unit

-- 具体实现
newtype IOFileSystem a := IOFileSystem { runIOFileSystem : IO a }

instance : Monad IOFileSystem where
  pure x := IOFileSystem (pure x)
  bind ma f := IOFileSystem do
    let a ← ma.runIOFileSystem
    (f a).runIOFileSystem

instance : FileSystem IOFileSystem where
  readFile path := IOFileSystem (IO.readFile path)
  writeFile path content := IOFileSystem (IO.writeFile path content)
  deleteFile path := IOFileSystem (IO.removeFile path)

-- 测试实现
newtype TestFileSystem a := TestFileSystem { runTestFileSystem : State (List (String × String)) a }

instance : Monad TestFileSystem where
  pure x := TestFileSystem (pure x)
  bind ma f := TestFileSystem do
    let a ← ma.runTestFileSystem
    (f a).runTestFileSystem

instance : FileSystem TestFileSystem where
  readFile path := TestFileSystem do
    let files ← get
    match List.find? files (fun (p, _) => p == path) with
    | some (_, content) => return content
    | none => return "File not found"
  writeFile path content := TestFileSystem do
    let files ← get
    put ((path, content) :: files)
  deleteFile path := TestFileSystem do
    let files ← get
    put (List.filter (fun (p, _) => p != path) files)

-- 业务逻辑
def processFile [FileSystem m] [Logger m] (path : String) : m String := do
  Logger.log s!"Processing file: {path}"
  let content ← FileSystem.readFile path
  Logger.log s!"File content length: {content.length}"
  return content

-- 使用不同实现
def ioProcess : IO String := do
  let fs := IOFileSystem {}
  let logger := IOFileSystem {}
  processFile "test.txt"

def testProcess : State (List (String × String)) String := do
  let fs := TestFileSystem {}
  let logger := TestFileSystem {}
  processFile "test.txt"

end TaglessFinal
```

## 🎯 应用场景

### 1. 错误处理

```lean
-- 错误处理应用
namespace ErrorHandling

-- 错误类型
data AppError
  | FileNotFound : String → AppError
  | ValidationError : String → AppError
  | NetworkError : String → AppError

-- 错误处理Monad
def AppM := Except AppError

instance : Monad AppM where
  pure := Except.ok
  bind := Except.bind

-- 文件操作
def safeReadFile (path : String) : AppM String :=
  if path.contains "error" then
    Except.error (AppError.FileNotFound path)
  else
    Except.ok "File content"

def validateContent (content : String) : AppM String :=
  if content.length > 0 then
    Except.ok content
  else
    Except.error (AppError.ValidationError "Empty content")

-- 组合操作
def processFile (path : String) : AppM String := do
  let content ← safeReadFile path
  validateContent content

end ErrorHandling
```

### 2. 配置管理

```lean
-- 配置管理应用
namespace ConfigManagement

-- 配置类型
structure Config where
  databaseUrl : String
  apiKey : String
  debugMode : Bool

-- Reader Monad
def ConfigM := Reader Config

instance : Monad ConfigM where
  pure x := { runReader := fun _ => x }
  bind ma f := { runReader := fun config => 
    let a := ma.runReader config
    (f a).runReader config }

-- 配置操作
def getDatabaseUrl : ConfigM String :=
  { runReader := fun config => config.databaseUrl }

def getApiKey : ConfigM String :=
  { runReader := fun config => config.apiKey }

def isDebugMode : ConfigM Bool :=
  { runReader := fun config => config.debugMode }

-- 使用配置
def connectDatabase : ConfigM String := do
  let url ← getDatabaseUrl
  let debug ← isDebugMode
  if debug then
    return s!"Debug: Connecting to {url}"
  else
    return s!"Connecting to {url}"

end ConfigManagement
```

## 🚀 最佳实践

### 1. 设计原则

- **组合性**: 优先使用可组合的抽象
- **类型安全**: 充分利用类型系统
- **不可变性**: 避免副作用

### 2. 实现策略

- **渐进式**: 从简单Monad开始
- **模块化**: 清晰的模块边界
- **可测试性**: 便于验证和测试

### 3. 性能考虑

- **惰性求值**: 利用惰性特性
- **内存管理**: 注意内存使用模式
- **编译优化**: 利用编译时优化

---

**下一节**: [类型级模式](./06-Type-Level-Patterns.md)

**相关链接**:

- [行为型模式](./04-Behavioral-Patterns.md)
- [设计模式基础](./01-Design-Patterns-Basics.md)
- [软件设计](../08-Software-Design/)
