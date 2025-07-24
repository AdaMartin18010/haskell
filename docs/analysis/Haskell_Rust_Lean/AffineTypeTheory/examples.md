# 4.5 典型案例 Examples #AffineTypeTheory-4.5

## 典型代码与推理 Typical Code & Reasoning

- **中文**：展示仿射类型在Rust等语言中的典型实现与资源有限性场景。
- **English**: Show typical implementations of affine types and resource finiteness scenarios in Rust and other languages.

```rust
// Rust: 仿射类型的所有权示例
fn consume_once(x: String) {
    println!("{}", x);
    // println!("{}", x); // 错误：x已被消耗
}
```

## 哲学与工程意义 Philosophical & Engineering Significance

- **中文**：仿射类型的案例体现了资源有限性与责任伦理的统一。
- **English**: Affine type cases embody the unity of resource finiteness and responsibility ethics.

## 交叉引用 Cross References

- [线性类型理论 Linear Type Theory](../LinearTypeTheory/README.md)
- [系统理论 System Theory](../SystemTheory/README.md)
