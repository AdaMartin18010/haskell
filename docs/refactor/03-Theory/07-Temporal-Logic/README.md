# 时态逻辑理论

## 📋 概述

时态逻辑是形式化方法的重要组成部分，用于描述和验证系统的时间相关性质。它提供了一套形式化语言来描述"总是"、"最终"、"直到"等时间概念，广泛应用于硬件验证、软件验证和协议验证等领域。

## 🏗️ 目录结构

### 01-线性时态逻辑

- [LTL语法语义](01-Linear-Temporal-Logic/01-LTL-Syntax-Semantics.md)
- [LTL模型检测](01-Linear-Temporal-Logic/02-LTL-Model-Checking.md)
- [LTL可满足性](01-Linear-Temporal-Logic/03-LTL-Satisfiability.md)
- [LTL综合](01-Linear-Temporal-Logic/04-LTL-Synthesis.md)

### 02-计算树逻辑

- [CTL语法语义](02-Computation-Tree-Logic/01-CTL-Syntax-Semantics.md)
- [CTL模型检测](02-Computation-Tree-Logic/02-CTL-Model-Checking.md)
- [CTL可满足性](02-Computation-Tree-Logic/03-CTL-Satisfiability.md)
- [CTL综合](02-Computation-Tree-Logic/04-CTL-Synthesis.md)

### 03-实时时态逻辑

- [时间自动机](03-Real-Time-Temporal-Logic/01-Timed-Automata.md)
- [度量时态逻辑](03-Real-Time-Temporal-Logic/02-Metric-Temporal-Logic.md)
- [实时验证](03-Real-Time-Temporal-Logic/03-Real-Time-Verification.md)
- [时间系统](03-Real-Time-Temporal-Logic/04-Timed-Systems.md)

### 04-时态逻辑应用

- [硬件验证](04-Temporal-Logic-Applications/01-Hardware-Verification.md)
- [软件验证](04-Temporal-Logic-Applications/02-Software-Verification.md)
- [协议验证](04-Temporal-Logic-Applications/03-Protocol-Verification.md)

## 🔗 相关链接

- [形式化方法](../04-Formal-Methods/)
- [模型检测](../04-Formal-Methods/01-Model-Checking/)
- [形式科学层逻辑学](../../02-Formal-Science/02-Formal-Logic/)

## 📚 理论基础

### 数学基础

- **模态逻辑**：时态逻辑作为模态逻辑的扩展
- **自动机理论**：Kripke结构和Büchi自动机
- **图论**：状态转换图和时间图

### 形式化方法

- **模型检测**：自动验证时态逻辑公式
- **可满足性检查**：检查公式的可满足性
- **综合算法**：从时态逻辑规约生成系统

### 应用领域

- **硬件验证**：验证数字电路的正确性
- **软件验证**：验证程序的时间性质
- **协议验证**：验证通信协议的正确性

## 🎯 学习目标

1. **理解时态逻辑**：掌握时态逻辑的基本概念和语法
2. **掌握模型检测**：学会使用模型检测验证时态性质
3. **应用时态逻辑**：在实际验证中应用时态逻辑
4. **实现验证工具**：能够实现简单的时态逻辑验证器

## 🔧 技术栈

- **形式化语言**：LTL、CTL、MTL
- **验证工具**：SPIN、NuSMV、UPPAAL
- **编程语言**：Haskell、Python、C++

## 📖 参考资料

- Clarke, E. M., et al. (1999). Model Checking
- Baier, C., & Katoen, J. P. (2008). Principles of Model Checking
- Alur, R., & Dill, D. L. (1994). A theory of timed automata

---

*本目录提供时态逻辑理论的完整学习路径，从基础概念到实际应用。*
