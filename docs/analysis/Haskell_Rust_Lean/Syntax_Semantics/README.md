# 2. 语法与语义 Syntax & Semantics

## 2.1 表达式与语句 Expressions & Statements #SyntaxSemantics-2.1

### 2.1.1 定义 Definition

- **中文**：表达式是有值的语法结构，语句是执行动作的结构。函数式语言以表达式为主，命令式语言以语句为主。
- **English**: Expressions are syntactic constructs with values; statements perform actions. Functional languages focus on expressions, imperative languages on statements.

### 2.1.2 历史与发展 History & Development

- **中文**：表达式与语句的区分源于早期编程范式，Haskell极致表达式化，Rust兼容两者，Lean以表达式和证明脚本为主。
- **English**: The distinction between expressions and statements originates from early programming paradigms; Haskell is highly expression-oriented, Rust supports both, Lean uses expressions and proof scripts.

### 2.1.3 哲学批判与争议 Philosophical Critique & Controversies

- **中文**：表达式化提升抽象力，语句化强调过程控制，两者的平衡影响语言风格与可验证性。
- **English**: Expression-orientation enhances abstraction, statement-orientation emphasizes process control; their balance affects language style and verifiability.

### 2.1.4 国际对比与标准 International Comparison & Standards

- **中文**：Haskell表达式为主，Rust语句与表达式混合，Lean以表达式和证明脚本为主。
- **English**: Haskell is expression-oriented, Rust mixes statements and expressions, Lean uses expressions and proof scripts.

### 2.1.5 典型案例 Typical Example

```haskell
-- Haskell: 表达式
let x = 1 + 2
```

```rust
// Rust: 语句与表达式
let x = if cond { 1 } else { 2 };
```

```lean
-- Lean: 表达式与证明脚本
#eval 1 + 2
```

### 2.1.6 对比表格 Comparison Table

| 语言 | 表达式 | 语句 |
|------|--------|------|
| Haskell | 强 | 弱 |
| Rust    | 强 | 强 |
| Lean    | 强 | 证明脚本 |

### 2.1.7 交叉引用 Cross References

- [类型系统 Type Systems](../TypeSystems/README.md)

### 2.1.8 参考文献 References

- [Wikipedia: Expression (computer science)](https://en.wikipedia.org/wiki/Expression_(computer_science))

### 2.1.9 批判性小结 Critical Summary

- **中文**：表达式与语句的设计影响语言抽象力与可验证性，未来需关注多范式融合。
- **English**: The design of expressions and statements affects abstraction and verifiability; future work should focus on multi-paradigm integration.

---

## 2.2 模式匹配 Pattern Matching #SyntaxSemantics-2.2

### 2.2.1 定义 Definition

- **中文**：模式匹配是根据数据结构自动分解和绑定变量的机制。
- **English**: Pattern matching is a mechanism for automatically decomposing data structures and binding variables.

### 2.2.2 历史与发展 History & Development

- **中文**：模式匹配起源于ML，Haskell强化，Rust引入match，Lean支持依赖类型下的模式匹配。
- **English**: Pattern matching originated in ML, enhanced in Haskell, introduced as match in Rust, supported in Lean with dependent types.

### 2.2.3 哲学批判与争议 Philosophical Critique & Controversies

- **中文**：模式匹配提升表达力，但复杂模式可能降低可读性。
- **English**: Pattern matching enhances expressiveness, but complex patterns may reduce readability.

### 2.2.4 国际对比与标准 International Comparison & Standards

- **中文**：Haskell、Rust、Lean均有强模式匹配，Wiki有详细定义。
- **English**: Haskell, Rust, and Lean all have strong pattern matching; Wiki provides detailed definitions.

### 2.2.5 典型案例 Typical Example

```haskell
-- Haskell: 模式匹配
case xs of [] -> 0; (x:_) -> x
```

```rust
// Rust: match语句
match xs.first() { Some(x) => x, None => 0 }
```

```lean
-- Lean: 依赖类型下的模式匹配
def head {α : Type} : List α → Option α
| []      => none
| (x::_)  => some x
```

### 2.2.6 对比表格 Comparison Table

| 语言 | 模式匹配 | 依赖类型支持 |
|------|----------|--------------|
| Haskell | 强 | GADT支持 |
| Rust    | 强 | 限支持 |
| Lean    | 强 | 内建 |

### 2.2.7 交叉引用 Cross References

- [类型系统 Type Systems](../TypeSystems/README.md)

### 2.2.8 参考文献 References

- [Wikipedia: Pattern matching](https://en.wikipedia.org/wiki/Pattern_matching)

### 2.2.9 批判性小结 Critical Summary

- **中文**：模式匹配需平衡表达力与可读性，未来需关注类型安全与自动化。
- **English**: Pattern matching should balance expressiveness and readability; future work should focus on type safety and automation.

---

## 2.3 类型声明 Type Declarations #SyntaxSemantics-2.3

### 2.3.1 定义 Definition

- **中文**：类型声明用于显式指定变量、函数、数据结构的类型。
- **English**: Type declarations are used to explicitly specify the types of variables, functions, and data structures.

### 2.3.2 历史与发展 History & Development

- **中文**：类型声明起源于早期静态类型语言，Haskell支持可选声明，Rust和Lean要求显式声明。
- **English**: Type declarations originated in early statically typed languages; Haskell supports optional declarations, Rust and Lean require explicit declarations.

### 2.3.3 哲学批判与争议 Philosophical Critique & Controversies

- **中文**：类型声明提升安全性，但过度冗余可能影响开发效率。
- **English**: Type declarations enhance safety, but excessive redundancy may affect development efficiency.

### 2.3.4 国际对比与标准 International Comparison & Standards

- **中文**：Haskell类型声明可选，Rust/Lean强制，Wiki有详细定义。
- **English**: Haskell type declarations are optional, Rust/Lean are mandatory; Wiki provides detailed definitions.

### 2.3.5 典型案例 Typical Example

```haskell
-- Haskell: 可选类型声明
x :: Int
x = 42
```

```rust
// Rust: 必需类型声明
let x: i32 = 42;
```

```lean
-- Lean: 必需类型声明
def x : Nat := 42
```

### 2.3.6 对比表格 Comparison Table

| 语言 | 类型声明 | 类型推断 |
|------|----------|----------|
| Haskell | 可选 | 强 |
| Rust    | 必需 | 局部 |
| Lean    | 必需 | 依赖类型 |

### 2.3.7 交叉引用 Cross References

- [类型系统 Type Systems](../TypeSystems/README.md)

### 2.3.8 参考文献 References

- [Wikipedia: Type declaration](https://en.wikipedia.org/wiki/Type_declaration)

### 2.3.9 批判性小结 Critical Summary

- **中文**：类型声明需平衡安全性与开发效率，未来需关注类型推断与声明自动化。
- **English**: Type declarations should balance safety and development efficiency; future work should focus on type inference and declaration automation.

---

## 2.4 求值策略 Evaluation Strategies #SyntaxSemantics-2.4

### 2.4.1 定义 Definition

- **中文**：求值策略决定表达式何时、如何被计算，常见有惰性与严格求值。
- **English**: Evaluation strategies determine when and how expressions are computed; common strategies include lazy and strict evaluation.

### 2.4.2 历史与发展 History & Development

- **中文**：Haskell采用惰性求值，Rust和Lean采用严格求值。
- **English**: Haskell uses lazy evaluation, Rust and Lean use strict evaluation.

### 2.4.3 哲学批判与争议 Philosophical Critique & Controversies

- **中文**：惰性提升抽象力，严格提升可预测性，两者的选择影响性能与可验证性。
- **English**: Laziness enhances abstraction, strictness improves predictability; the choice affects performance and verifiability.

### 2.4.4 国际对比与标准 International Comparison & Standards

- **中文**：Haskell惰性，Rust/Lean严格，Wiki有详细定义。
- **English**: Haskell is lazy, Rust/Lean are strict; Wiki provides detailed definitions.

### 2.4.5 典型案例 Typical Example

```haskell
-- Haskell: 惰性求值
let xs = [1..] in take 5 xs
```

```rust
// Rust: 严格求值
let x = 1 + 2;
```

```lean
-- Lean: 严格求值
#eval 1 + 2
```

### 2.4.6 对比表格 Comparison Table

| 语言 | 求值策略 | 性能 |
|------|----------|------|
| Haskell | 惰性 | 高抽象 |
| Rust    | 严格 | 高性能 |
| Lean    | 严格 | 证明步进 |

### 2.4.7 交叉引用 Cross References

- [语义模型 Semantic Models](../SemanticModels/README.md)

### 2.4.8 参考文献 References

- [Wikipedia: Evaluation strategy](https://en.wikipedia.org/wiki/Evaluation_strategy)

### 2.4.9 批判性小结 Critical Summary

- **中文**：求值策略需平衡抽象力与性能，未来需关注多策略融合与自动优化。
- **English**: Evaluation strategies should balance abstraction and performance; future work should focus on multi-strategy integration and automatic optimization.
