# 005 备忘录模式

## 1. 理论基础

备忘录模式是一种行为型设计模式，在不破坏封装的前提下，捕获并外部化对象的内部状态，以便在需要时可以将对象恢复到之前的状态。

## 2. 接口设计

```haskell
-- Haskell接口设计
class Originator a where
  createMemento :: a -> Memento
  restoreFromMemento :: a -> Memento -> a

class Memento a where
  getState :: a -> State

-- 状态和备忘录
data State = State String
data Memento = Memento State
```

## 3. 多语言实现

### Haskell实现

```haskell
-- 状态类型
data State = State String deriving Show

-- 备忘录
data Memento = Memento State deriving Show

-- 发起人
data Originator = Originator State deriving Show

-- 备忘录操作
createMemento :: Originator -> Memento
createMemento (Originator state) = Memento state

restoreFromMemento :: Originator -> Memento -> Originator
restoreFromMemento _ (Memento state) = Originator state

-- 管理者
data Caretaker = Caretaker [Memento] deriving Show

-- 管理者操作
addMemento :: Caretaker -> Memento -> Caretaker
addMemento (Caretaker mementos) memento = Caretaker (memento : mementos)

getMemento :: Caretaker -> Int -> Maybe Memento
getMemento (Caretaker mementos) index = 
  if index >= 0 && index < length mementos
  then Just (mementos !! index)
  else Nothing

-- 使用示例
main :: IO ()
main = do
  let originator = Originator (State "Initial")
  let memento = createMemento originator
  let caretaker = Caretaker []
  let caretaker' = addMemento caretaker memento
  let restored = restoreFromMemento originator memento
  print restored
```

### Rust实现

```rust
// 状态
#[derive(Clone, Debug)]
struct State {
    content: String,
}

// 备忘录
#[derive(Clone, Debug)]
struct Memento {
    state: State,
}

impl Memento {
    fn new(state: State) -> Self {
        Memento { state }
    }
    
    fn get_state(&self) -> &State {
        &self.state
    }
}

// 发起人
#[derive(Debug)]
struct Originator {
    state: State,
}

impl Originator {
    fn new(content: &str) -> Self {
        Originator {
            state: State {
                content: content.to_string(),
            },
        }
    }
    
    fn create_memento(&self) -> Memento {
        Memento::new(self.state.clone())
    }
    
    fn restore_from_memento(&mut self, memento: &Memento) {
        self.state = memento.get_state().clone();
    }
    
    fn set_state(&mut self, content: &str) {
        self.state.content = content.to_string();
    }
    
    fn get_state(&self) -> &State {
        &self.state
    }
}

// 管理者
struct Caretaker {
    mementos: Vec<Memento>,
}

impl Caretaker {
    fn new() -> Self {
        Caretaker { mementos: Vec::new() }
    }
    
    fn add_memento(&mut self, memento: Memento) {
        self.mementos.push(memento);
    }
    
    fn get_memento(&self, index: usize) -> Option<&Memento> {
        self.mementos.get(index)
    }
}
```

### Lean实现

```lean
-- 状态类型
def State := String

-- 备忘录类型
def Memento := State

-- 发起人类型
def Originator := State

-- 备忘录操作
def createMemento : Originator → Memento := id

def restoreFromMemento : Originator → Memento → Originator :=
  fun _ memento => memento

-- 管理者类型
def Caretaker := List Memento

-- 管理者操作
def addMemento : Caretaker → Memento → Caretaker :=
  fun caretaker memento => memento :: caretaker

def getMemento : Caretaker → ℕ → Option Memento :=
  fun caretaker index => caretaker.nth index

-- 备忘录正确性定理
theorem memento_correctness :
  ∀ o : Originator, ∀ m : Memento,
  restoreFromMemento o m = m :=
  by simp [restoreFromMemento]
```

## 4. 工程实践

- 撤销/重做功能
- 状态恢复
- 事务回滚
- 快照管理

## 5. 性能优化

- 增量备忘录
- 压缩存储
- 垃圾回收
- 内存管理

## 6. 应用场景

- 文本编辑器
- 游戏状态
- 数据库事务
- 配置管理

## 7. 最佳实践

- 控制备忘录数量
- 实现清理机制
- 考虑内存使用
- 支持选择性恢复
