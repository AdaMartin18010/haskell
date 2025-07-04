# 备忘录模式（Memento Pattern）

## 概述

备忘录模式是一种行为型设计模式，在不破坏封装的前提下，捕获并外部化对象的内部状态，这样以后就可以将该对象恢复到原先保存的状态。

## 理论基础

- **状态保存**：保存对象内部状态
- **封装保护**：不破坏对象封装性
- **状态恢复**：支持状态回滚

## Rust实现示例

```rust
struct Originator {
    state: String,
}

impl Originator {
    fn new(state: String) -> Self {
        Self { state }
    }
    
    fn set_state(&mut self, state: String) {
        self.state = state;
    }
    
    fn get_state(&self) -> &str {
        &self.state
    }
    
    fn save_to_memento(&self) -> Memento {
        Memento::new(self.state.clone())
    }
    
    fn restore_from_memento(&mut self, memento: &Memento) {
        self.state = memento.get_state().clone();
    }
}

struct Memento {
    state: String,
}

impl Memento {
    fn new(state: String) -> Self {
        Self { state }
    }
    
    fn get_state(&self) -> &str {
        &self.state
    }
}

struct Caretaker {
    mementos: Vec<Memento>,
}

impl Caretaker {
    fn new() -> Self {
        Self { mementos: Vec::new() }
    }
    
    fn add_memento(&mut self, memento: Memento) {
        self.mementos.push(memento);
    }
    
    fn get_memento(&self, index: usize) -> Option<&Memento> {
        self.mementos.get(index)
    }
}

fn main() {
    let mut originator = Originator::new("初始状态".to_string());
    let mut caretaker = Caretaker::new();
    
    println!("初始状态: {}", originator.get_state());
    
    // 保存状态
    let memento1 = originator.save_to_memento();
    caretaker.add_memento(memento1);
    
    // 修改状态
    originator.set_state("修改后的状态".to_string());
    println!("修改后状态: {}", originator.get_state());
    
    // 保存第二个状态
    let memento2 = originator.save_to_memento();
    caretaker.add_memento(memento2);
    
    // 再次修改状态
    originator.set_state("最终状态".to_string());
    println!("最终状态: {}", originator.get_state());
    
    // 恢复到第一个状态
    if let Some(memento) = caretaker.get_memento(0) {
        originator.restore_from_memento(memento);
        println!("恢复到第一个状态: {}", originator.get_state());
    }
    
    // 恢复到第二个状态
    if let Some(memento) = caretaker.get_memento(1) {
        originator.restore_from_memento(memento);
        println!("恢复到第二个状态: {}", originator.get_state());
    }
}
```

## Haskell实现示例

```haskell
data Originator = Originator { state :: String }
newOriginator :: String -> Originator
newOriginator state = Originator state
setState :: Originator -> String -> Originator
setState originator newState = originator { state = newState }
getState :: Originator -> String
getState = state
saveToMemento :: Originator -> Memento
saveToMemento originator = Memento (state originator)
restoreFromMemento :: Originator -> Memento -> Originator
restoreFromMemento _ memento = Originator (getMementoState memento)

data Memento = Memento { mementoState :: String }
getMementoState :: Memento -> String
getMementoState = mementoState

data Caretaker = Caretaker [Memento]
newCaretaker :: Caretaker
newCaretaker = Caretaker []
addMemento :: Caretaker -> Memento -> Caretaker
addMemento (Caretaker mementos) memento = Caretaker (memento : mementos)
getMemento :: Caretaker -> Int -> Maybe Memento
getMemento (Caretaker mementos) index = 
    if index >= 0 && index < length mementos
    then Just (mementos !! index)
    else Nothing

main = do
    let originator = newOriginator "初始状态"
    let caretaker = newCaretaker
    
    putStrLn $ "初始状态: " ++ getState originator
    
    -- 保存状态
    let memento1 = saveToMemento originator
    let caretaker' = addMemento caretaker memento1
    
    -- 修改状态
    let originator' = setState originator "修改后的状态"
    putStrLn $ "修改后状态: " ++ getState originator'
    
    -- 保存第二个状态
    let memento2 = saveToMemento originator'
    let caretaker'' = addMemento caretaker' memento2
    
    -- 再次修改状态
    let originator'' = setState originator' "最终状态"
    putStrLn $ "最终状态: " ++ getState originator''
    
    -- 恢复到第一个状态
    case getMemento caretaker'' 0 of
        Just memento -> do
            let restored = restoreFromMemento originator'' memento
            putStrLn $ "恢复到第一个状态: " ++ getState restored
        Nothing -> putStrLn "无法恢复状态"
    
    -- 恢复到第二个状态
    case getMemento caretaker'' 1 of
        Just memento -> do
            let restored = restoreFromMemento originator'' memento
            putStrLn $ "恢复到第二个状态: " ++ getState restored
        Nothing -> putStrLn "无法恢复状态"
```

## Lean实现思路

```lean
structure Originator where
  state : String

def newOriginator (state : String) : Originator := { state := state }
def setState (originator : Originator) (newState : String) : Originator :=
  { originator with state := newState }
def getState (originator : Originator) : String := originator.state
def saveToMemento (originator : Originator) : Memento :=
  { state := originator.state }
def restoreFromMemento (_ : Originator) (memento : Memento) : Originator :=
  { state := memento.state }

structure Memento where
  state : String

def getMementoState (memento : Memento) : String := memento.state

structure Caretaker where
  mementos : List Memento

def newCaretaker : Caretaker := { mementos := [] }
def addMemento (caretaker : Caretaker) (memento : Memento) : Caretaker :=
  { caretaker with mementos := memento :: caretaker.mementos }
def getMemento (caretaker : Caretaker) (index : Nat) : Option Memento :=
  caretaker.mementos.get? index
```

## 应用场景

- 撤销重做功能
- 游戏存档系统
- 数据库事务回滚
- 配置管理

## 最佳实践

- 合理控制备忘录数量
- 实现增量保存
- 支持选择性恢复
