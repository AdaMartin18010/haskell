# 1. 类型系统 Type Systems

## 1.1 类型推断 Type Inference #TypeSystems-1.1

### 1.1.1 定义 Definition

- **中文**：类型推断是编程语言自动推导表达式类型的能力，减少显式类型注解。
- **English**: Type inference is the ability of a programming language to automatically deduce the types of expressions, reducing explicit type annotations.

### 1.1.2 历史与发展 History & Development

- **中文**：类型推断起源于Hindley-Milner系统，Haskell广泛采用，Rust基于trait系统实现。
- **English**: Type inference originated from the Hindley-Milner system, widely adopted in Haskell, and implemented in Rust via the trait system.

### 1.1.3 哲学批判与争议 Philosophical Critique & Controversies

- **中文**：类型推断提升了表达力，但过度自动化可能导致类型错误难以定位。
- **English**: Type inference enhances expressiveness, but excessive automation may make type errors harder to locate.

### 1.1.4 国际对比与标准 International Comparison & Standards

- **中文**：Haskell类型推断最强，Rust强调安全与局部推断，Lean支持依赖类型推断。
- **English**: Haskell has the strongest type inference, Rust emphasizes safety and local inference, Lean supports dependent type inference.

### 1.1.5 典型案例 Typical Example

```haskell
-- Haskell: 类型推断
double x = x + x
```

```rust
// Rust: 局部类型推断
let x = 42; // 类型自动为i32
```

```lean
-- Lean: 依赖类型推断
def id {α : Type} (a : α) := a
```

### 1.1.6 对比表格 Comparison Table

| 语言 | 类型推断 | 局限 |
|------|----------|------|
| Haskell | 强，全局 | 某些GADT需注解 |
| Rust    | 局部，trait | 复杂泛型需注解 |
| Lean    | 依赖类型 | 复杂证明需注解 |

### 1.1.7 交叉引用 Cross References

- [语法与语义 Syntax & Semantics](../Syntax_Semantics/README.md)

### 1.1.8 参考文献 References

- [Wikipedia: Type inference](https://en.wikipedia.org/wiki/Type_inference)

### 1.1.9 批判性小结 Critical Summary

- **中文**：类型推断需平衡自动化与可读性，未来需关注类型错误定位与推断透明性。
- **English**: Type inference should balance automation and readability; future work should focus on error localization and inference transparency.

---

## 1.2 多态与泛型 Polymorphism & Generics #TypeSystems-1.2

### 1.2.1 定义 Definition

- **中文**：多态允许同一操作作用于多种类型，泛型是多态的工程实现。
- **English**: Polymorphism allows the same operation to apply to multiple types; generics are the engineering realization of polymorphism.

### 1.2.2 历史与发展 History & Development

- **中文**：多态起源于ML、Haskell，Rust通过trait泛型实现，Lean支持依赖类型多态。
- **English**: Polymorphism originated in ML and Haskell; Rust implements it via trait generics; Lean supports dependent type polymorphism.

### 1.2.3 哲学批判与争议 Philosophical Critique & Controversies

- **中文**：多态提升抽象力，但过度泛化可能降低类型安全。
- **English**: Polymorphism increases abstraction, but excessive generalization may reduce type safety.

### 1.2.4 国际对比与标准 International Comparison & Standards

- **中文**：Haskell类型类、Rust trait、Lean依赖类型多态均有国际标准。
- **English**: Haskell type classes, Rust traits, and Lean dependent type polymorphism all have international standards.

### 1.2.5 典型案例 Typical Example

```haskell
-- Haskell: 类型类多态
class Eq a where
  (==) :: a -> a -> Bool
```

```rust
// Rust: trait泛型
trait Eq { fn eq(&self, other: &Self) -> bool; }
```

```lean
-- Lean: 依赖类型多态
def id {α : Type} (a : α) := a
```

### 1.2.6 对比表格 Comparison Table

| 语言 | 多态机制 | 工程实现 |
|------|----------|----------|
| Haskell | 类型类 | 泛型函数 |
| Rust    | trait泛型 | trait bound |
| Lean    | 依赖类型 | 多态证明 |

### 1.2.7 交叉引用 Cross References

- [语法与语义 Syntax & Semantics](../Syntax_Semantics/README.md)

### 1.2.8 参考文献 References

- [Wikipedia: Polymorphism (computer science)](https://en.wikipedia.org/wiki/Polymorphism_(computer_science))

### 1.2.9 批判性小结 Critical Summary

- **中文**：多态与泛型需兼顾抽象力与类型安全，未来需关注多范式兼容与类型推断。
- **English**: Polymorphism and generics should balance abstraction and type safety; future work should focus on multi-paradigm compatibility and type inference.

---

## 1.3 依赖类型与高级类型 Dependent & Advanced Types #TypeSystems-1.3

### 1.3.1 定义 Definition

- **中文**：依赖类型允许类型依赖于值，高级类型包括GADT、Type Families等。
- **English**: Dependent types allow types to depend on values; advanced types include GADTs, Type Families, etc.

### 1.3.2 历史与发展 History & Development

- **中文**：依赖类型起源于Martin-Löf类型理论，Lean内建，Haskell通过GADT等扩展支持。
- **English**: Dependent types originated from Martin-Löf type theory, built-in in Lean, supported in Haskell via GADTs, etc.

### 1.3.3 哲学批判与争议 Philosophical Critique & Controversies

- **中文**：依赖类型提升表达力，但增加类型系统复杂性与学习曲线。
- **English**: Dependent types enhance expressiveness but increase type system complexity and learning curve.

### 1.3.4 国际对比与标准 International Comparison & Standards

- **中文**：Lean依赖类型最强，Haskell支持GADT/Type Families，Rust有限支持。
- **English**: Lean has the strongest dependent types, Haskell supports GADTs/Type Families, Rust has limited support.

### 1.3.5 典型案例 Typical Example

```haskell
-- Haskell: GADT
 data Expr a where
   EInt  :: Int -> Expr Int
   EAdd  :: Expr Int -> Expr Int -> Expr Int
```

```lean
-- Lean: 依赖类型
def Vec (α : Type) : Nat → Type
| 0     => Unit
| n + 1 => α × Vec α n
```

### 1.3.6 对比表格 Comparison Table

| 语言 | 依赖类型 | 高级类型 |
|------|----------|----------|
| Haskell | GADT、Type Families | GHC扩展 |
| Rust    | 限支持 | trait bound |
| Lean    | 内建 | 依赖类型、GADT |

### 1.3.7 交叉引用 Cross References

- [语义模型 Semantic Models](../SemanticModels/README.md)

### 1.3.8 参考文献 References

- [Wikipedia: Dependent type](https://en.wikipedia.org/wiki/Dependent_type)

### 1.3.9 批判性小结 Critical Summary

- **中文**：依赖类型与高级类型推动了类型系统创新，但需关注工程可用性与工具链支持。
- **English**: Dependent and advanced types drive type system innovation, but engineering usability and toolchain support need attention.

---

## 1.4 线性/仿射类型 Linear/Affine Types #TypeSystems-1.4

### 1.4.1 定义 Definition

- **中文**：线性类型要求变量只能用一次，仿射类型允许变量至多用一次。
- **English**: Linear types require variables to be used exactly once; affine types allow variables to be used at most once.

### 1.4.2 历史与发展 History & Development

- **中文**：线性类型起源于Girard线性逻辑，Haskell通过GHC扩展支持，Rust通过所有权系统实现。
- **English**: Linear types originated from Girard's linear logic, supported in Haskell via GHC extensions, implemented in Rust via the ownership system.

### 1.4.3 哲学批判与争议 Philosophical Critique & Controversies

- **中文**：线性/仿射类型提升资源安全，但增加工程复杂性。
- **English**: Linear/affine types improve resource safety but increase engineering complexity.

### 1.4.4 国际对比与标准 International Comparison & Standards

- **中文**：Rust所有权系统为业界标杆，Haskell支持线性类型，Lean可用依赖类型模拟。
- **English**: Rust's ownership system is an industry benchmark, Haskell supports linear types, Lean can simulate with dependent types.

### 1.4.5 典型案例 Typical Example

```haskell
-- Haskell: 线性类型
f :: a %1 -> (a, a)
```

```rust
// Rust: 所有权与仿射类型
fn consume_once(x: String) { println!("{}", x); }
```

### 1.4.6 对比表格 Comparison Table

| 语言 | 线性/仿射类型 | 工程实现 |
|------|----------|----------|
| Haskell | GHC扩展 | 线性类型注解 |
| Rust    | 内建 | 所有权/借用 |
| Lean    | 依赖类型模拟 | 理论为主 |

### 1.4.7 交叉引用 Cross References

- [工程应用 Engineering Applications](../EngineeringApplications/README.md)

### 1.4.8 参考文献 References

- [Wikipedia: Linear type system](https://en.wikipedia.org/wiki/Linear_type_system)

### 1.4.9 批判性小结 Critical Summary

- **中文**：线性/仿射类型需平衡安全性与工程复杂性，未来需关注类型推断与生态支持。
- **English**: Linear/affine types should balance safety and engineering complexity; future work should focus on type inference and ecosystem support.
