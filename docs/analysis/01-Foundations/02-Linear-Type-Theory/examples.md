# 3.5 典型案例 Examples #LinearTypeTheory-3.5

## 典型代码与推理 Typical Code & Reasoning

- **中文**：展示线性类型在Haskell、Rust等语言中的典型实现与资源安全场景。
- **English**: Show typical implementations of linear types and resource safety scenarios in Haskell, Rust, and other languages.

```haskell
-- Haskell: 线性类型示例（GHC 9.x）
f :: a %1 -> (a, a)
f x = (x, x)  -- 错误：x被用两次，违反线性约束
```

```rust
// Rust: 所有权与借用的线性约束
fn consume_once(x: String) {
    println!("{}", x);
    // println!("{}", x); // 错误：x已被消耗
}
```

## 哲学与工程意义 Philosophical & Engineering Significance

- **中文**：线性类型的案例体现了资源唯一性与消耗性的工程与哲学统一。
- **English**: Linear type cases embody the unity of resource uniqueness and consumption in engineering and philosophy.

## 交叉引用 Cross References

- [仿射类型理论 Affine Type Theory](../AffineTypeTheory/README.md)
- [系统理论 System Theory](../SystemTheory/README.md)
