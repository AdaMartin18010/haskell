# 解释器模式（Interpreter Pattern）

## 概述

解释器模式是一种行为型设计模式，为语言创建解释器，定义语法的表示以及解释该语法的方法。

## 理论基础

- **抽象语法树**：构建语法树表示
- **递归解释**：递归遍历语法树
- **上下文环境**：维护解释上下文

## Rust实现示例

```rust
trait Expression {
    fn interpret(&self, context: &Context) -> i32;
}

struct Context {
    variables: std::collections::HashMap<String, i32>,
}

impl Context {
    fn new() -> Self {
        Self { variables: std::collections::HashMap::new() }
    }
    
    fn set_variable(&mut self, name: &str, value: i32) {
        self.variables.insert(name.to_string(), value);
    }
    
    fn get_variable(&self, name: &str) -> Option<&i32> {
        self.variables.get(name)
    }
}

struct NumberExpression {
    value: i32,
}

impl Expression for NumberExpression {
    fn interpret(&self, _context: &Context) -> i32 {
        self.value
    }
}

struct VariableExpression {
    name: String,
}

impl Expression for VariableExpression {
    fn interpret(&self, context: &Context) -> i32 {
        context.get_variable(&self.name).copied().unwrap_or(0)
    }
}

struct AddExpression {
    left: Box<dyn Expression>,
    right: Box<dyn Expression>,
}

impl Expression for AddExpression {
    fn interpret(&self, context: &Context) -> i32 {
        self.left.interpret(context) + self.right.interpret(context)
    }
}

struct SubtractExpression {
    left: Box<dyn Expression>,
    right: Box<dyn Expression>,
}

impl Expression for SubtractExpression {
    fn interpret(&self, context: &Context) -> i32 {
        self.left.interpret(context) - self.right.interpret(context)
    }
}

fn main() {
    let mut context = Context::new();
    context.set_variable("x", 10);
    context.set_variable("y", 5);
    
    let expression = AddExpression {
        left: Box::new(VariableExpression { name: "x".to_string() }),
        right: Box::new(SubtractExpression {
            left: Box::new(VariableExpression { name: "y".to_string() }),
            right: Box::new(NumberExpression { value: 2 }),
        }),
    };
    
    let result = expression.interpret(&context);
    println!("结果: {}", result);
}
```

## Haskell实现示例

```haskell
class Expression a where
    interpret :: a -> Context -> Int

data Context = Context { variables :: [(String, Int)] }
newContext :: Context
newContext = Context []
setVariable :: Context -> String -> Int -> Context
setVariable (Context vars) name value = Context ((name, value) : vars)
getVariable :: Context -> String -> Int
getVariable (Context vars) name = maybe 0 id (lookup name vars)

data NumberExpression = NumberExpression Int
instance Expression NumberExpression where
    interpret (NumberExpression value) _ = value

data VariableExpression = VariableExpression String
instance Expression VariableExpression where
    interpret (VariableExpression name) context = getVariable context name

data AddExpression = AddExpression Expression Expression
instance Expression AddExpression where
    interpret (AddExpression left right) context = 
        interpret left context + interpret right context

data SubtractExpression = SubtractExpression Expression Expression
instance Expression SubtractExpression where
    interpret (SubtractExpression left right) context = 
        interpret left context - interpret right context

main = do
    let context = setVariable (setVariable newContext "x" 10) "y" 5
    let expression = AddExpression 
        (VariableExpression "x") 
        (SubtractExpression (VariableExpression "y") (NumberExpression 2))
    let result = interpret expression context
    putStrLn $ "结果: " ++ show result
```

## Lean实现思路

```lean
class Expression (α : Type) where
  interpret : α → Context → Int

structure Context where
  variables : List (String × Int)

def newContext : Context := { variables := [] }
def setVariable (context : Context) (name : String) (value : Int) : Context :=
  { context with variables := (name, value) :: context.variables }
def getVariable (context : Context) (name : String) : Int :=
  match context.variables.find? (fun (k, _) => k = name) with
  | some (_, v) => v
  | none => 0

structure NumberExpression where
  value : Int

instance : Expression NumberExpression where
  interpret e _ := e.value

structure VariableExpression where
  name : String

instance : Expression VariableExpression where
  interpret e context := getVariable context e.name

structure AddExpression where
  left : Expression
  right : Expression

instance : Expression AddExpression where
  interpret e context := interpret e.left context + interpret e.right context

structure SubtractExpression where
  left : Expression
  right : Expression

instance : Expression SubtractExpression where
  interpret e context := interpret e.left context - interpret e.right context
```

## 应用场景

- 编程语言解释器
- 配置文件解析
- 查询语言处理
- 规则引擎

## 最佳实践

- 构建清晰的语法树结构
- 优化解释性能
- 支持错误处理和恢复
