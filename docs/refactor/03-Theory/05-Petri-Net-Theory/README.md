# Petri网理论 - 主索引

## 📋 概述

Petri网理论是并发系统建模和分析的重要形式化工具，提供了描述和分析并发、同步、资源竞争等复杂系统行为的数学框架。

## 🏗️ 理论架构

### 核心概念

- **Petri网**：有向二分图，包含库所(places)和变迁(transitions)
- **标记(Marking)**：库所中托肯(token)的分布
- **变迁规则**：标记转移的形式化规则
- **可达性**：从初始标记可达的所有标记集合
- **活性**：系统无死锁的性质
- **有界性**：库所中托肯数量的上界

### 理论层次

1. **基础Petri网**：经典Petri网的基本概念和性质
2. **高级Petri网**：扩展的Petri网模型
3. **Petri网分析**：分析技术和算法
4. **Petri网应用**：实际应用领域

## 📚 详细内容

### 01-基础Petri网

- [基础概念与定义](01-Basic-Concepts.md)
- [标记与变迁规则](02-Markings-and-Transitions.md)
- [可达性分析](03-Reachability-Analysis.md)
- [基本性质](04-Basic-Properties.md)

### 02-高级Petri网

- [时间Petri网](01-Timed-Petri-Nets.md)
- [着色Petri网](02-Colored-Petri-Nets.md)
- [层次Petri网](03-Hierarchical-Petri-Nets.md)
- [随机Petri网](04-Stochastic-Petri-Nets.md)

### 03-Petri网分析

- [结构分析](01-Structural-Analysis.md)
- [行为分析](02-Behavioral-Analysis.md)
- [性能分析](03-Performance-Analysis.md)
- [验证技术](04-Verification-Techniques.md)

### 04-Petri网应用

- [软件工程](01-Software-Engineering.md)
- [工作流建模](02-Workflow-Modeling.md)
- [并发系统](03-Concurrent-Systems.md)
- [实时系统](04-Real-Time-Systems.md)

## 🔗 相关链接

- **上层理论**：[编程语言理论](../01-Programming-Language-Theory/README.md)
- **上层理论**：[系统理论](../02-System-Theory/README.md)
- **上层理论**：[控制论](../03-Control-Theory/README.md)
- **上层理论**：[分布式系统理论](../04-Distributed-Systems-Theory/README.md)
- **下层应用**：[形式化验证](../../04-Applied-Science/03-Formal-Verification/README.md)
- **下层应用**：[工作流系统](../../06-Architecture/03-Workflow-Systems/README.md)

## 📖 参考文献

1. Petri, C.A. (1962). "Kommunikation mit Automaten"
2. Reisig, W. (1985). "Petri Nets: An Introduction"
3. Murata, T. (1989). "Petri Nets: Properties, Analysis and Applications"
4. Jensen, K. (1997). "Coloured Petri Nets: Basic Concepts"

---

*本索引文件提供了Petri网理论的完整导航和框架。*
