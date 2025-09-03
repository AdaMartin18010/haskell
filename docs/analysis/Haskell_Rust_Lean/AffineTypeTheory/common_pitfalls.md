# 4.12 常见误区 Common Pitfalls #AffineTypeTheory-4.12

## 4.12.1 理论误区 Theoretical Pitfalls #AffineTypeTheory-4.12.1

- 误解仿射类型的“弱唯一性”，未区分“必须用一次”与“最多用一次”。
- 忽视仿射类型在并发、分布式系统中的资源释放语义。
- 误将仿射类型等同于线性类型，未区分其推理规则与资源管理策略。
- 忽视仿射类型与类型推断、类型安全的交互。

## 4.12.2 工程陷阱 Engineering Pitfalls #AffineTypeTheory-4.12.2

- 在Rust等语言中，仿射类型与生命周期管理结合不当，导致悬垂指针。
- 忽视仿射类型与垃圾回收机制的协同。
- 工程实现中，仿射类型系统设计不当导致资源泄漏或未释放。

### 反例与校正 Counterexamples & Fixes

```rust
// 反例：错误使用导致 move 后再用
fn bad() {
    let s = String::from("x");
    let n = s.len();
    drop(s);
    // println!("{}", s); // error: moved value
}
```

```haskell
{-# LANGUAGE LinearTypes #-}
-- 反例：线性参数未消费（仿射需允许丢弃，但线性不行）
bad :: a %1 -> ()
bad _ = () -- 在线性设定下不成立；仿射设定允许
```

工程规约（Guidelines）：

- 明确一次性资源的“拥有者”与释放点；在 API 层编码约束。
- 将可丢弃行为限制在指数/能力层；记录释放语义（Doc/Test）。
- 用静态分析/属性测试补充类型系统覆盖盲区。

## 4.12.3 三语言相关注意事项 Language-specific Notes #AffineTypeTheory-4.12.3

- Haskell：仿射类型扩展需关注类型推断与兼容性。
- Rust：所有权与借用机制实现复杂，需关注资源释放。
- Lean：形式化仿射证明需关注资源丢弃的完备性。

## 4.12.5 课程与行业案例对齐 Courses & Industry Alignment

- **课程**: MIT 6.821/6.822；CMU 15-312/814（资源语义、错误用例分析）。
- **行业**: RustBelt 反例库；生产事故复盘（句柄泄漏/双重释放）。

参考模板：参见 `../course_case_alignment_template.md`

## 4.12.4 相关Tag

`# AffineTypeTheory #AffineTypeTheory-4 #AffineTypeTheory-4.12 #AffineTypeTheory-4.12.1 #AffineTypeTheory-4.12.2 #AffineTypeTheory-4.12.3`
