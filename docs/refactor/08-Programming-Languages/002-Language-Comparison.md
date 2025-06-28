# 编程语言对比分析

## Haskell vs Rust vs Lean

### 设计理念

| 语言 | 核心理念 | 主要优势 |
|------|----------|----------|
| Haskell | 纯函数式编程 | 强类型系统、惰性求值 |
| Rust | 内存安全系统编程 | 零成本抽象、并发安全 |
| Lean | 定理证明 | 依赖类型、数学形式化 |

### 类型系统对比

```haskell
-- Haskell: 高阶类型
newtype State s a = State { runState :: s -> (a, s) }
```

```rust
// Rust: 所有权系统
fn main() {
    let s1 = String::from("hello");
    let s2 = s1; // 所有权转移
}
```

```lean
-- Lean: 依赖类型
def Vector (α : Type) : Nat → Type
  | 0 => Unit
  | n + 1 => α × Vector α n
```

### 应用场景

- **Haskell**: Web开发、金融系统、并发编程
- **Rust**: 系统编程、嵌入式、高性能应用
- **Lean**: 数学证明、形式化验证

---

**相关链接**：

- [Haskell深度解析](./003-Haskell-Deep-Dive.md)
- [Rust深度解析](./004-Rust-Deep-Dive.md)
- [Lean深度解析](./005-Lean-Deep-Dive.md)
