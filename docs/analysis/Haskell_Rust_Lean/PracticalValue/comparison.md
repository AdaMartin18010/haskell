# 1.6 三语言对比 Comparison (Haskell/Rust/Lean)

Tag: #PracticalValue-1.6

| 价值维度 Value Dimension | Haskell | Rust | Lean |
|---|---|---|---|
| 开发效率 Development Efficiency | 高（抽象强、工具成熟） | 中（学习曲线陡峭） | 低（证明负担重） |
| 质量保证 Quality Assurance | 高（类型安全、纯函数） | 高（内存安全、并发安全） | 最高（机器检验） |
| 性能保证 Performance | 中（惰性、GC） | 高（零成本、无GC） | 低（证明开销） |
| 维护成本 Maintenance | 低（不可变性、类型） | 中（所有权、生命周期） | 低（形式化规范） |
