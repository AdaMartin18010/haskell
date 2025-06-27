# 301 软件工程基础（Software Engineering Foundations）

## 1. 概述

软件工程基础涵盖软件开发的基本原理、生命周期、质量保障等，是现代计算科学与工程实践的核心。其目标是以系统化、规范化、可度量的方式开发和维护高质量软件。

## 2. 主要分支/流派/方法

- 瀑布模型（Waterfall Model）
- 敏捷开发（Agile Development）
- 持续集成与持续交付（CI/CD）
- 需求工程、测试工程、维护工程

## 3. 理论体系与工程流程

- 软件生命周期模型：需求分析、系统设计、编码实现、测试验证、部署运维、维护升级
- 质量属性：可维护性、可扩展性、可靠性、安全性
- 典型流程图与结构图（可用Mermaid/LaTeX绘制）

## 4. Haskell工程实践示例

```haskell
-- Haskell中的模块化与测试
module Main where

main :: IO ()
main = putStrLn "Hello, Software Engineering!"
```

## 5. 相关证明与形式化表达

- 形式化需求规约（LaTeX示例）：
  \[
  \forall x \in \text{Input},\ \text{System}(x) \rightarrow \text{Output}(x)
  \]
- 需求一致性与可追踪性证明思路

## 6. 应用案例与工程经验

- Haskell在金融、区块链等领域的工程实践
- 典型项目的工程流程与质量保障措施

## 7. 与Rust/Lean工程对比

| 特性         | Haskell           | Rust              | Lean                |
|--------------|-------------------|-------------------|---------------------|
| 工程生态     | 成熟，社区活跃    | 成熟，系统编程强  | 新兴，形式化为主    |
| 类型系统     | 强，惰性          | 强，所有权/生命周期| 依赖类型，证明辅助  |
| 工程工具     | Stack/Cabal       | Cargo             | Lean工具链          |

## 8. 参考文献

- [1] Sommerville, I. (2016). Software Engineering.
- [2] Pressman, R. S. (2014). Software Engineering: A Practitioner's Approach.
