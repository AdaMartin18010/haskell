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

```haskell
{-# LANGUAGE LinearTypes #-}
-- Haskell: 仿射/线性风格的一次性消费示意
discardOrUse :: a %1 -> ()
discardOrUse _ = ()  -- 仿射允许丢弃
```

```lean
-- Lean（骨架）：一次性资源消费的命题化
def AffRes := Unit
theorem at_most_once (r : AffRes) : True := trivial
```

## 哲学与工程意义 Philosophical & Engineering Significance

- **中文**：仿射类型的案例体现了资源有限性与责任伦理的统一。
- **English**: Affine type cases embody the unity of resource finiteness and responsibility ethics.

## 交叉引用 Cross References

- [线性类型理论 Linear Type Theory](../LinearTypeTheory/README.md)
- [系统理论 System Theory](../SystemTheory/README.md)

## 课程与行业案例对齐 Courses & Industry Alignment

- **课程 Courses**: CMU/ MIT 资源语义课程作业（一次性消费与弱化）；Rust 安全性专题。
- **行业 Industry**: 文件句柄与网络连接一次性释放；一次性 token/凭证；GPU/IO 缓冲生命周期管理。

参考模板：参见 `../course_case_alignment_template.md`
