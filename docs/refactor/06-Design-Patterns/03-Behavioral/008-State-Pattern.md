# 状态模式（State Pattern）

## 概述
状态模式是一种行为型设计模式，允许对象在内部状态改变时改变其行为，对象看起来好像修改了其类。

## 理论基础
- **状态封装**：将状态相关的行为封装在独立的状态类中
- **状态转换**：定义清晰的状态转换规则
- **行为变化**：状态改变时行为自动变化

## Rust实现示例
```rust
trait State {
    fn handle(&self, context: &mut Context) -> String;
}

struct Context {
    state: Box<dyn State>,
}

impl Context {
    fn new() -> Self {
        Self {
            state: Box::new(ConcreteStateA),
        }
    }
    
    fn set_state(&mut self, state: Box<dyn State>) {
        self.state = state;
    }
    
    fn request(&self) -> String {
        self.state.handle(self)
    }
}

struct ConcreteStateA;

impl State for ConcreteStateA {
    fn handle(&self, context: &mut Context) -> String {
        context.set_state(Box::new(ConcreteStateB));
        "状态A处理请求，转换到状态B".to_string()
    }
}

struct ConcreteStateB;

impl State for ConcreteStateB {
    fn handle(&self, context: &mut Context) -> String {
        context.set_state(Box::new(ConcreteStateC));
        "状态B处理请求，转换到状态C".to_string()
    }
}

struct ConcreteStateC;

impl State for ConcreteStateC {
    fn handle(&self, context: &mut Context) -> String {
        context.set_state(Box::new(ConcreteStateA));
        "状态C处理请求，转换到状态A".to_string()
    }
}

fn main() {
    let mut context = Context::new();
    
    println!("{}", context.request());
    println!("{}", context.request());
    println!("{}", context.request());
    println!("{}", context.request());
}
```

## Haskell实现示例
```haskell
class State a where
    handle :: a -> Context -> (String, Context)

data Context = Context { currentState :: State }
newContext :: Context
newContext = Context ConcreteStateA
setState :: Context -> State -> Context
setState context state = context { currentState = state }
request :: Context -> (String, Context)
request context = handle (currentState context) context

data ConcreteStateA = ConcreteStateA
instance State ConcreteStateA where
    handle _ context = ("状态A处理请求，转换到状态B", setState context ConcreteStateB)

data ConcreteStateB = ConcreteStateB
instance State ConcreteStateB where
    handle _ context = ("状态B处理请求，转换到状态C", setState context ConcreteStateC)

data ConcreteStateC = ConcreteStateC
instance State ConcreteStateC where
    handle _ context = ("状态C处理请求，转换到状态A", setState context ConcreteStateA)

main = do
    let context = newContext
    let (result1, context1) = request context
    putStrLn result1
    let (result2, context2) = request context1
    putStrLn result2
    let (result3, context3) = request context2
    putStrLn result3
    let (result4, _) = request context3
    putStrLn result4
```

## Lean实现思路
```lean
class State (α : Type) where
  handle : α → Context → String × Context

structure Context where
  currentState : State

def newContext : Context := { currentState := ConcreteStateA }
def setState (context : Context) (state : State) : Context :=
  { context with currentState := state }
def request (context : Context) : String × Context :=
  State.handle context.currentState context

structure ConcreteStateA
instance : State ConcreteStateA where
  handle _ context := ("状态A处理请求，转换到状态B", setState context ConcreteStateB)

structure ConcreteStateB
instance : State ConcreteStateB where
  handle _ context := ("状态B处理请求，转换到状态C", setState context ConcreteStateC)

structure ConcreteStateC
instance : State ConcreteStateC where
  handle _ context := ("状态C处理请求，转换到状态A", setState context ConcreteStateA)
```

## 应用场景
- 游戏角色状态
- 工作流状态机
- 网络连接状态
- 订单状态管理

## 最佳实践
- 明确定义状态转换规则
- 避免状态类过于复杂
- 支持状态历史记录 