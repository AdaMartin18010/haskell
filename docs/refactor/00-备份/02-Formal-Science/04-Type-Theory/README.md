# 类型论 (Type Theory)

## 📋 概述

类型论是现代数学和计算机科学的基础理论，它统一了逻辑、集合论和计算理论。类型论为函数式编程、定理证明和形式化验证提供理论基础。

## 🎯 核心概念

### 基本类型系统

- **简单类型理论**：基础的类型系统
- **依赖类型理论**：类型可以依赖于值的类型系统
- **同伦类型理论**：基于同伦论的现代类型理论
- **构造类型理论**：强调构造性的类型理论

### 类型构造

- **函数类型**：表示函数和映射
- **积类型**：表示有序对和记录
- **和类型**：表示联合和变体
- **归纳类型**：表示递归定义的数据结构

### 类型推理

- **类型检查**：验证程序是否符合类型规则
- **类型推导**：自动推断表达式的类型
- **统一算法**：解决类型约束的算法
- **类型安全**：确保程序运行时的安全性

## 📚 详细内容

### 01-基本概念 (Basic-Concepts)

- [类型论基础](./01-Basic-Concepts/01-Type-Theory-Basics.md)
- [类型与项](./01-Basic-Concepts/02-Types-and-Terms.md)
- [类型检查](./01-Basic-Concepts/03-Type-Checking.md)
- [类型推导](./01-Basic-Concepts/04-Type-Inference.md)

### 02-简单类型论 (Simple-Type-Theory)

- [λ演算](./02-Simple-Type-Theory/01-Lambda-Calculus.md)
- [简单类型λ演算](./02-Simple-Type-Theory/02-Simply-Typed-Lambda-Calculus.md)
- [类型构造子](./02-Simple-Type-Theory/03-Type-Constructors.md)
- [类型系统性质](./02-Simple-Type-Theory/04-Type-System-Properties.md)

### 03-多态类型论 (Polymorphic-Type-Theory)

- [System F](./03-Polymorphic-Type-Theory/01-System-F.md)
- [Hindley-Milner系统](./03-Polymorphic-Type-Theory/02-Hindley-Milner-System.md)
- [高阶多态](./03-Polymorphic-Type-Theory/03-Higher-Order-Polymorphism.md)
- [类型抽象](./03-Polymorphic-Type-Theory/04-Type-Abstraction.md)

### 04-依赖类型论 (Dependent-Type-Theory)

- [Martin-Löf类型论](./04-Dependent-Type-Theory/01-Martin-Lof-Type-Theory.md)
- Π类型与Σ类型
- 归纳类型
- 模式匹配

### 05-同伦类型论 (Homotopy-Type-Theory)

- [基本概念](./05-Homotopy-Type-Theory/01-Basic-Concepts.md)
- 类型作为空间
- 等价与同构
- 高阶归纳类型

### 06-构造类型论 (Constructive-Type-Theory)

- [直觉逻辑](./06-Constructive-Type-Theory/01-Intuitionistic-Logic.md)
- 构造性证明
- 程序提取
- 证明无关性

## 🔗 相关链接

- [形式科学层主索引](../README.md)
- [数学基础](../01-Mathematics/README.md)
- [形式逻辑](../02-Formal-Logic/README.md)
- [范畴论](../03-Category-Theory/README.md)
- [编程语言理论](../../03-Theory/01-Programming-Language-Theory/README.md)

## 📖 学习路径

1. **基本概念**：理解类型、项和类型关系
2. **简单类型论**：掌握λ演算和类型检查
3. **多态类型论**：学习参数多态和类型抽象
4. **依赖类型论**：理解依赖类型和证明系统

## 🎯 应用领域

- **函数式编程**：Haskell、Agda、Coq
- **定理证明**：形式化数学证明
- **程序验证**：程序正确性验证
- **语言设计**：编程语言设计

---

*类型论是现代数学和计算机科学的重要基础，为形式化方法和函数式编程提供了坚实的理论基础。*
