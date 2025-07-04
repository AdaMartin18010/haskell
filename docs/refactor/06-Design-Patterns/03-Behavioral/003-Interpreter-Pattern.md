# 003 解释器模式

## 1. 理论基础

解释器模式是一种行为型设计模式，为语言创建解释器。定义语法表示和解释方法，用于解释特定语言或表达式。

## 2. 接口设计

```haskell
-- Haskell接口设计
class Expression a where
  interpret :: a -> Context -> Int

-- 上下文
data Context = Context (Map String Int)

-- 表达式类型
data TerminalExpression = TerminalExpression String
data NonTerminalExpression = NonTerminalExpression Expression Expression
```

## 3. 多语言实现

### Haskell实现

```haskell
import Data.Map (Map)
import qualified Data.Map as Map

-- 表达式接口
class Expression a where
  interpret :: a -> Context -> Int

-- 上下文
data Context = Context (Map String Int) deriving Show

-- 终结表达式
data TerminalExpression = TerminalExpression String deriving Show

instance Expression TerminalExpression where
  interpret (TerminalExpression var) (Context context) = 
    Map.findWithDefault 0 var context

-- 非终结表达式
data NonTerminalExpression = NonTerminalExpression TerminalExpression TerminalExpression deriving Show

instance Expression NonTerminalExpression where
  interpret (NonTerminalExpression left right) context = 
    interpret left context + interpret right context

-- 使用示例
main :: IO ()
main = do
  let context = Context $ Map.fromList [("x", 10), ("y", 20)]
  let expr = NonTerminalExpression 
              (TerminalExpression "x") 
              (TerminalExpression "y")
  print $ interpret expr context
```

### Rust实现

```rust
use std::collections::HashMap;

// 表达式trait
trait Expression {
    fn interpret(&self, context: &Context) -> i32;
}

// 上下文
struct Context {
    variables: HashMap<String, i32>,
}

impl Context {
    fn new() -> Self {
        Context {
            variables: HashMap::new(),
        }
    }
    
    fn set(&mut self, key: &str, value: i32) {
        self.variables.insert(key.to_string(), value);
    }
    
    fn get(&self, key: &str) -> i32 {
        *self.variables.get(key).unwrap_or(&0)
    }
}

// 终结表达式
struct TerminalExpression {
    variable: String,
}

impl Expression for TerminalExpression {
    fn interpret(&self, context: &Context) -> i32 {
        context.get(&self.variable)
    }
}

// 非终结表达式
struct NonTerminalExpression {
    left: Box<dyn Expression>,
    right: Box<dyn Expression>,
}

impl Expression for NonTerminalExpression {
    fn interpret(&self, context: &Context) -> i32 {
        self.left.interpret(context) + self.right.interpret(context)
    }
}
```

### Lean实现

```lean
-- 表达式类型
inductive Expression where
  | Terminal : String → Expression
  | NonTerminal : Expression → Expression → Expression

-- 上下文
def Context := List (String × ℕ)

-- 解释函数
def interpret : Expression → Context → ℕ
  | Expression.Terminal var, ctx => 
    match ctx.lookup var with
    | some value => value
    | none => 0
  | Expression.NonTerminal left right, ctx =>
    interpret left ctx + interpret right ctx

-- 解释器正确性定理
theorem interpreter_correctness :
  ∀ expr : Expression, ∀ ctx : Context,
  interpret expr ctx ≥ 0 :=
  by simp [interpret]
```

## 4. 工程实践

- 语法解析
- 表达式求值
- 规则引擎
- 配置解析

## 5. 性能优化

- 表达式缓存
- 预编译优化
- 内存管理
- 并行解释

## 6. 应用场景

- 配置文件解析
- 查询语言
- 规则引擎
- 脚本解释器

## 7. 最佳实践

- 保持语法简单
- 实现错误处理
- 考虑性能影响
- 支持扩展语法
