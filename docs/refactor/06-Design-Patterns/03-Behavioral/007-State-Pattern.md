# 007 状态模式

## 1. 理论基础

状态模式是一种行为型设计模式，允许对象在内部状态改变时改变其行为。对象看起来修改了其类，实际上是状态转换。

## 2. 接口设计

```haskell
-- Haskell接口设计
class State a where
  handle :: a -> Context -> IO ()

-- 上下文
data Context = Context State

-- 具体状态
data ConcreteStateA = ConcreteStateA
data ConcreteStateB = ConcreteStateB
```

## 3. 多语言实现

### Haskell实现

```haskell
-- 状态接口
class State a where
  handle :: a -> Context -> IO ()

-- 上下文
data Context = Context (Maybe State) deriving Show

-- 具体状态
data ConcreteStateA = ConcreteStateA deriving Show
data ConcreteStateB = ConcreteStateB deriving Show

instance State ConcreteStateA where
  handle ConcreteStateA context = 
    putStrLn "Handling in State A"

instance State ConcreteStateB where
  handle ConcreteStateB context = 
    putStrLn "Handling in State B"

-- 上下文操作
setState :: Context -> State -> Context
setState (Context _) state = Context (Just state)

getState :: Context -> Maybe State
getState (Context state) = state

-- 使用示例
main :: IO ()
main = do
  let context = Context Nothing
  let context' = setState context ConcreteStateA
  case getState context' of
    Just state -> handle state context'
    Nothing -> putStrLn "No state"
```

### Rust实现

```rust
// 状态trait
trait State {
    fn handle(&self, context: &mut Context);
}

// 上下文
struct Context {
    state: Option<Box<dyn State>>,
}

impl Context {
    fn new() -> Self {
        Context { state: None }
    }
    
    fn set_state(&mut self, state: Box<dyn State>) {
        self.state = Some(state);
    }
    
    fn request(&mut self) {
        if let Some(state) = &self.state {
            state.handle(self);
        }
    }
}

// 具体状态A
struct ConcreteStateA;

impl State for ConcreteStateA {
    fn handle(&self, context: &mut Context) {
        println!("Handling in State A");
        // 可以在这里转换到其他状态
        context.set_state(Box::new(ConcreteStateB));
    }
}

// 具体状态B
struct ConcreteStateB;

impl State for ConcreteStateB {
    fn handle(&self, context: &mut Context) {
        println!("Handling in State B");
        // 可以在这里转换到其他状态
        context.set_state(Box::new(ConcreteStateA));
    }
}
```

### Lean实现

```lean
-- 状态类型
inductive State where
  | StateA : State
  | StateB : State

-- 上下文类型
def Context := State

-- 状态处理函数
def handle : State → Context → IO Unit
  | State.StateA, _ => IO.println "Handling in State A"
  | State.StateB, _ => IO.println "Handling in State B"

-- 状态转换
def transition : State → State
  | State.StateA => State.StateB
  | State.StateB => State.StateA

-- 状态模式正确性定理
theorem state_transition_correctness :
  ∀ s : State, transition (transition s) = s :=
  by cases s; simp [transition]
```

## 4. 工程实践

- 状态机实现
- 工作流引擎
- 游戏状态管理
- 协议状态

## 5. 性能优化

- 状态缓存
- 延迟初始化
- 内存管理
- 状态压缩

## 6. 应用场景

- 游戏状态
- 网络协议
- 工作流
- 用户界面

## 7. 最佳实践

- 保持状态简单
- 避免状态爆炸
- 考虑性能影响
- 实现状态验证
