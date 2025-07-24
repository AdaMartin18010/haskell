# 01. 仿射类型理论基础（Affine Type Theory Foundation）

> **中英双语核心定义 | Bilingual Core Definitions**

## 1.1 仿射类型理论简介（Introduction to Affine Type Theory）

- **定义（Definition）**：
  - **中文**：仿射类型理论是一种类型系统，要求每个变量最多使用一次（可以不用），广泛用于内存安全、资源管理和并发场景。
  - **English**: Affine type theory is a type system that requires each variable to be used at most once (possibly zero times). It is widely used for memory safety, resource management, and concurrency.

- **Wiki风格国际化解释（Wiki-style Explanation）**：
  - 仿射类型理论为Rust的所有权与借用系统、Haskell的资源安全抽象等提供理论基础。
  - Affine type theory underpins Rust's ownership and borrowing system, as well as resource-safe abstractions in Haskell.

## 1.2 仿射类型系统基本结构（Basic Structure of Affine Type Systems）

- **仿射类型上下文（Affine Type Context）**
  - $\Gamma : \text{Var} \rightarrow \text{Type}$，每个变量最多出现一次。
  - **中文**：仿射类型上下文允许变量不用，但最多用一次。
  - **English**: Affine type context allows each variable to be used at most once.

- **仿射类型构造（Affine Type Constructors）**
  - $\tau ::= \text{Base} \mid \tau_1 \rightarrow \tau_2 \mid \tau_1 \& \tau_2 \mid \tau_1 \oplus \tau_2$
  - $\rightarrow$：仿射函数类型（affine function type）
  - $\&$：加法积类型（with type）
  - $\oplus$：加法类型（plus type）

- **推理规则（Inference Rules）**

| 规则 | 数学形式 | 中文 | English |
|------|----------|------|---------|
| 变量 | $\frac{x : \tau \in \Gamma}{\Gamma \vdash x : \tau}$ | 变量类型 | Variable type |
| 仿射抽象 | $\frac{\Gamma, x : \tau_1 \vdash e : \tau_2}{\Gamma \vdash \lambda x.e : \tau_1 \rightarrow \tau_2}$ | 仿射函数抽象 | Affine function abstraction |
| 仿射应用 | $\frac{\Gamma_1 \vdash e_1 : \tau_1 \rightarrow \tau_2 \quad \Gamma_2 \vdash e_2 : \tau_1}{\Gamma_1, \Gamma_2 \vdash e_1 e_2 : \tau_2}$ | 仿射函数应用 | Affine function application |
| 弱化 | $\frac{\Gamma \vdash e : \tau}{\Gamma, x : \tau' \vdash e : \tau}$ | 变量可不用 | Weakening (variable may be unused) |

## 1.3 Haskell仿射类型系统与语义模型（Haskell Affine Type System & Semantic Model）

- **Haskell中的仿射类型思想**
  - Haskell本身不直接支持仿射类型，但可通过类型类、newtype等模拟资源唯一性。

```haskell
newtype Affine a = Affine { useOnce :: Maybe a }

consume :: Affine a -> (a -> b) -> Maybe b
consume (Affine (Just x)) f = Just (f x)
consume _ _ = Nothing
```

- **Rust所有权系统对比**
  - Rust的所有权与借用系统严格实现了仿射类型约束：

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 被移动到 s2，s1 不再可用
    // println!("{}", s1);  // 编译错误：s1 已被移动
}
```

## 1.4 形式化证明与论证（Formal Proofs & Reasoning）

- **仿射类型保持性证明（Preservation Proof）**
  - **中文**：对每个推理规则，证明仿射类型在归约后保持不变。
  - **English**: For each inference rule, prove that the affine type is preserved after reduction.

- **仿射进展性证明（Progress Proof）**
  - **中文**：对每个语法构造，证明要么是值，要么可以继续归约。
  - **English**: For each syntactic construct, prove it is either a value or can be further reduced.

## 1.5 多表征与本地跳转（Multi-representation & Local Reference）

- **仿射类型系统结构图（Affine Type System Structure Diagram）**

```mermaid
graph TD
  A[仿射类型上下文] --> B[仿射类型判断]
  B --> C[推理规则]
  C --> D[仿射类型安全性]
  D --> E[Haskell仿射类型模拟]
```

- **相关主题跳转**：
  - [类型理论 Type Theory](../01-Type-Theory/01-Type-Theory-Foundation.md)
  - [线性类型理论 Linear Type Theory](../02-Linear-Type-Theory/01-Linear-Type-Theory-Foundation.md)
  - [时序类型理论 Temporal Type Theory](../04-Temporal-Type-Theory/01-Temporal-Type-Theory-Foundation.md)

---

## 1.6 历史与发展 History & Development

- **中文**：仿射类型理论起源于线性逻辑的推广，允许变量最多使用一次（可不使用），广泛应用于内存安全、资源管理和并发。Haskell通过类型类和newtype等机制可模拟仿射类型思想，Rust则在所有权系统中严格实现。
- **English**: Affine type theory originated as a generalization of linear logic, allowing variables to be used at most once (possibly zero times). It is widely used for memory safety, resource management, and concurrency. Haskell can simulate affine types via type classes and newtype, while Rust strictly enforces them in its ownership system.

## 1.7 Haskell 相关特性 Haskell Features

### 经典特性 Classic Features

- 类型类、newtype、不可变数据结构、资源安全抽象等。
- Type classes, newtype, immutable data structures, resource-safe abstractions, etc.

### 最新特性 Latest Features

- **Linear Types（线性类型）**：GHC 8.12+支持，变量必须恰好使用一次，仿射类型可通过约束松弛模拟。
- **Type-level Programming**：类型级资源管理与约束。
- **GHC 2021/2022**：标准化类型系统扩展。

- **English**:
  - Linear Types: Supported since GHC 8.12+, variables must be used exactly once; affine types can be simulated by relaxing constraints.
  - Type-level programming: Type-level resource management and constraints.
  - GHC 2021/2022: Standardizes type system extensions.

## 1.8 应用 Applications

- **中文**：内存安全API、资源管理、并发、不可变数据结构、所有权建模等。
- **English**: Memory-safe APIs, resource management, concurrency, immutable data structures, ownership modeling, etc.

## 1.9 例子 Examples

```haskell
newtype Affine a = Affine { useOnce :: Maybe a }

consume :: Affine a -> (a -> b) -> Maybe b
consume (Affine (Just x)) f = Just (f x)
consume _ _ = Nothing
```

## 相关理论 Related Theories

- 线性类型理论（Linear Type Theory）
- 资源敏感类型系统（Resource-sensitive Type Systems）
- 不可变数据结构（Immutable Data Structures）
- 并发与分布式系统（Concurrency and Distributed Systems）

## 参考文献 References

- [Wikipedia: Affine Type](https://en.wikipedia.org/wiki/Affine_type)
- [GHC User's Guide](https://downloads.haskell.org/ghc/latest/docs/html/users_guide/)
- [Rust Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)
- [Learn You a Haskell for Great Good!](http://learnyouahaskell.com/)

> 本文档为仿射类型理论基础的中英双语、Haskell语义模型与形式化证明规范化输出，适合学术研究与工程实践参考。
