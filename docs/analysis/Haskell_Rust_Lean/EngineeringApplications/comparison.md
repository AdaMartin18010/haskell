# 1.6 三语言对比 Comparison (Haskell/Rust/Lean)

Tag: #EngineeringApplications-1.6

| 维度 Dimension | Haskell | Rust | Lean |
|---|---|---|---|
| 正确性 Correctness | 强类型+纯函数+效应抽象 | 所有权/借用/生命周期 | 机器检验证明 |
| 性能 Performance | 惰性+fusion+优化等价 | 零成本抽象+SIMD+并发 | 证明成本高、运行成本低（提取） |
| 工程复杂度 Complexity | 抽象深，工具成熟 | 系统工程复杂 | 证明负担高 |
