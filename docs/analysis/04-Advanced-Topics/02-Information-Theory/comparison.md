# 14.6 三语言对比 Comparison (Haskell/Rust/Lean) #InformationTheory-14.6

## 14.6.1 对比表格 Comparison Table #InformationTheory-14.6.1

| 特性/语言 | Haskell | Rust | Lean |
|-----------|---------|------|------|
| 信息建模 | 数据类型/概率模型 | struct/trait | 归纳类型/概率 |
| 熵与概率 | 类型系统/概率分布 | trait/概率库 | 形式化熵与概率 |
| 编码实现 | 函数式编码/压缩 | trait实现/高效编码 | 形式化编码与证明 |
| 工程应用 | 通信仿真、数据分析 | 嵌入式、信号处理 | 形式化信息安全 |

## 14.6.2 典型代码对比 Typical Code Comparison #InformationTheory-14.6.2

```haskell
-- Haskell: 熵计算
entropy ps = negate $ sum [p * logBase 2 p | p <- ps, p > 0]
```

```rust
// Rust: 熵计算
fn entropy(ps: &[f64]) -> f64 {
    -ps.iter().filter(|&&p| p > 0.0).map(|&p| p * p.log2()).sum::<f64>()
}
```

```lean
-- Lean: 熵计算
def entropy (ps : list ℝ) : ℝ :=
  - (ps.filter (λ p, p > 0)).sum (λ p, p * real.logb 2 p)
```

## 14.6.3 哲学与工程意义 Philosophical & Engineering Significance #InformationTheory-14.6.3

- Haskell：强调抽象与概率建模，适合高层信息分析。
- Rust：强调高效实现与系统安全。
- Lean：强调形式化证明与信息安全的可验证性。

## 14.6.4 国际标准与Wiki对标 International Standards & Wiki #InformationTheory-14.6.4

- Haskell: Haskell 2010, ISO, Wiki
- Rust: Rust Reference, ISO, Wiki
- Lean: Lean Reference, mathlib, Wiki

## 14.6.5 相关Tag

`# InformationTheory #InformationTheory-14 #InformationTheory-14.6 #InformationTheory-14.6.1 #InformationTheory-14.6.2 #InformationTheory-14.6.3 #InformationTheory-14.6.4`
