# 3.9 国际对比与标准 International Comparison & Standards #LinearTypeTheory-3.9

## 对比表格 Comparison Table

| 语言/特性 | Haskell | Rust | Lean |
|-----------|---------|------|------|
| 线性类型  | GHC扩展 | 所有权/借用 | 理论模拟 |
| 资源安全  | 类型约束 | 所有权强制 | 依赖类型建模 |
| 工程应用  | 并发/不可变 | 系统/嵌入式 | 理论为主 |

## 典型代码对比 Typical Code Comparison

```haskell
-- Haskell: 线性类型
f :: a %1 -> (a, a)
-- 错误：x被用两次，违反线性约束
```

```rust
// Rust: 所有权与借用
fn consume_once(x: String) {
    println!("{}", x);
    // println!("{}", x); // 错误：x已被消耗
}
```

```lean
-- Lean: 依赖类型模拟线性约束（伪代码）
def use_once {α : Type} (x : α) : ... := ...
```

## 哲学与工程意义对比 Philosophical & Engineering Significance

- **Haskell**：强调类型安全与抽象，适合高层次建模。
- **Rust**：强调资源唯一性与工程安全，适合系统级开发。
- **Lean**：理论模拟，适合形式化建模与证明。

## 国际标准与Wiki对标 International Standards & Wiki

- Haskell: GHC Linear Types, Wiki
- Rust: Rust Reference, Ownership, Wiki
- Lean: 理论文献、mathlib、Wiki

## 交叉引用 Cross References

- [仿射类型理论 Affine Type Theory](../AffineTypeTheory/README.md)
- [系统理论 System Theory](../SystemTheory/README.md)
