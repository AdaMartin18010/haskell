# 1.9 国际对比与标准 International Comparison & Standards #TypeTheory-1.9

## 对比表格 Comparison Table

| 语言/特性 | Haskell | Rust | Lean |
|-----------|---------|------|------|
| 类型推断  | 强，全局 | 局部，trait | 依赖类型 |
| 多态      | 类型类  | trait泛型   | 依赖类型多态 |
| 依赖类型  | GADT/Type Families | 有限支持 | 内建，强 |
| 线性/仿射类型 | GHC扩展 | 所有权/借用 | 理论模拟 |
| 工程应用  | 函数式/抽象 | 系统/安全 | 形式化证明 |

## 典型代码对比 Typical Code Comparison

```haskell
-- Haskell: 多态恒等
id :: a -> a
id x = x
```

```rust
// Rust: 泛型恒等
fn id<T>(x: T) -> T { x }
```

```lean
-- Lean: 依赖类型恒等
def id {α : Type} (a : α) := a
```

## 哲学与工程意义对比 Philosophical & Engineering Significance

- **Haskell**：强调抽象与类型安全，适合高层次建模与函数式范式。
- **Rust**：强调所有权与资源安全，适合系统级开发与并发。
- **Lean**：强调依赖类型与形式化证明，适合数学与可验证工程。

## 国际标准与Wiki对标 International Standards & Wiki

- Haskell: Haskell 2010, ISO, Wiki
- Rust: Rust Reference, ISO, Wiki
- Lean: Lean Reference, mathlib, Wiki

## 交叉引用 Cross References

- [类型系统 Type Systems](../TypeSystems/README.md)
- [工程应用 Engineering Applications](../EngineeringApplications/README.md)
