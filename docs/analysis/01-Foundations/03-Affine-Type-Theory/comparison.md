# 4.9 国际对比与标准 International Comparison & Standards #AffineTypeTheory-4.9

## 核心定义与范围 Core Definition & Scope

- **中文**：仿射类型=至多一次使用；允许弱化、禁止收缩；指数层受控复制/丢弃。
- **English**: Affine types = at-most-once usage; weakening allowed, contraction forbidden; exponentials control duplication/disposal.

## 对比表格 Comparison Table

| 语言/特性 | Haskell | Rust | Lean |
|-----------|---------|------|------|
| 仿射类型  | 线性类型模拟 | 所有权系统 | 理论模拟 |
| 资源有限  | 类型约束 | 所有权强制 | 依赖类型建模 |
| 工程应用  | 并发/不可变 | 系统/嵌入式 | 理论为主 |

## 典型代码对比 Typical Code Comparison

```haskell
-- Haskell: 线性类型模拟仿射
f :: a %1 -> ()
```

```rust
// Rust: 仿射所有权
fn consume_once(x: String) {
    println!("{}", x);
    // println!("{}", x); // 错误：x已被消耗
}
```

```lean
-- Lean: 依赖类型模拟仿射约束（伪代码）
def use_at_most_once {α : Type} (x : Option α) : ... := ...
```

## 哲学与工程意义对比 Philosophical & Engineering Significance

- **Haskell**：通过类型系统模拟资源有限性。
- **Rust**：所有权系统严格实现仿射约束，提升安全。
- **Lean**：理论模拟，适合形式化建模。

## 形式化比较 Formal Comparison

- **规则级差异 Rule-level**: 仿射具弱化无收缩；线性无弱化无收缩；普通系统具弱化与收缩。
- **保持性表达 Preservation**: 仿射使用 `Γ' ⪯ Γ`；线性要求资源等值；普通系统允许扩张。
- **指数层差异 Exponentials**: `!`/`?` 的可用性与侧条件在各系统实现不同（Rust 借用 vs Haskell 扩展）。

## 国际标准与Wiki对标 International Standards & Wiki

- Haskell: GHC Linear Types, Wiki
- Rust: Rust Reference, Ownership, Wiki
- Lean: 理论文献、mathlib、Wiki

## 课程与行业案例对齐 Courses & Industry Alignment

- **课程**: MIT 6.821/6.822；CMU 15-312/814；Rust 安全性专题。
- **行业**: RustBelt（JACM 2021）；一次性资源 API/句柄；嵌入式连接生命周期管理。

参考模板：参见 `../course_case_alignment_template.md`

## 交叉引用 Cross References

- [线性类型理论 Linear Type Theory](../LinearTypeTheory/README.md)
- [系统理论 System Theory](../SystemTheory/README.md)
