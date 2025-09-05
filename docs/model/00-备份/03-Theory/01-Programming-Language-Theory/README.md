# 01-Programming-Language-Theory (编程语言理论)

## 📚 编程语言理论概述

编程语言理论是计算机科学的核心理论之一，研究编程语言的设计、实现和语义。我们涵盖从语法理论到语义理论，从基础类型系统到高级类型系统的完整体系。

## 🏗️ 目录结构

```text
01-Programming-Language-Theory/
├── README.md                           # 本文件 - 编程语言理论总览
├── 01-Syntax-Theory/                   # 语法理论
│   ├── README.md                       # 语法理论总览
│   ├── 01-Formal-Grammars.md           # 形式文法
│   ├── 02-Parsing-Theory.md            # 解析理论
│   ├── 03-Syntax-Analysis.md           # 语法分析
│   └── 04-Compiler-Construction.md     # 编译器构造
├── 02-Semantics-Theory/                # 语义理论
│   ├── README.md                       # 语义理论总览
│   ├── 01-Operational-Semantics.md     # 操作语义
│   ├── 02-Denotational-Semantics.md    # 指称语义
│   ├── 03-Axiomatic-Semantics.md       # 公理语义
│   └── 04-Formal-Semantics.md          # 形式语义
└── 03-Type-System-Theory/              # 类型系统理论
    ├── README.md                       # 类型系统理论总览
    ├── 01-Basic-Type-Systems/          # 基础类型系统
    │   ├── README.md                   # 基础类型系统总览
    │   ├── 01-Basic-Concepts.md        # 基本概念
    │   ├── 02-Simple-Type-Systems.md   # 简单类型系统
    │   ├── 03-Polymorphic-Type-Systems.md # 多态类型系统
    │   └── 04-Dependent-Type-Systems.md # 依赖类型系统
    └── 02-Advanced-Type-Systems/       # 高级类型系统
        ├── README.md                   # 高级类型系统总览
        ├── 01-Higher-Order-Type-Systems.md # 高阶类型系统
        ├── 02-Subtyping-Theory.md      # 子类型理论
        ├── 03-Type-Inference.md        # 类型推断
        └── 04-Type-Safety.md           # 类型安全
```

## 🔗 快速导航

### 核心分支

- [语法理论](01-Syntax-Theory/) - 形式文法、解析理论、语法分析、编译器构造
- [语义理论](02-Semantics-Theory/) - 操作语义、指称语义、公理语义、形式语义
- [类型系统理论](03-Type-System-Theory/) - 基础类型系统、高级类型系统

### 主题导航

- [形式文法](01-Syntax-Theory/01-Formal-Grammars.md) - 上下文无关文法、正则文法
- [操作语义](02-Semantics-Theory/01-Operational-Semantics.md) - 小步语义、大步语义
- [简单类型系统](03-Type-System-Theory/01-Basic-Type-Systems/02-Simple-Type-Systems.md) - λ演算、类型检查

## 📖 核心概念

### 语法理论 (Syntax Theory)

**研究编程语言的语法结构和解析方法**:

#### 形式文法 (Formal Grammars)

- **上下文无关文法**：编程语言的基本语法结构
- **正则文法**：词法分析的基础
- **属性文法**：语法树属性的计算
- **语法分析**：自顶向下和自底向上分析

#### 解析理论 (Parsing Theory)

- **LL解析**：自顶向下的预测解析
- **LR解析**：自底向上的移进归约解析
- **递归下降解析**：手写解析器的实现
- **解析器生成器**：自动生成解析器

### 语义理论 (Semantics Theory)

**研究编程语言的语义定义和解释**:

#### 操作语义 (Operational Semantics)

- **小步语义**：逐步执行的计算模型
- **大步语义**：整体执行的计算模型
- **抽象机**：程序执行的抽象模型
- **求值策略**：参数传递和求值顺序

#### 指称语义 (Denotational Semantics)

- **数学函数**：程序作为数学函数
- **域理论**：递归定义的数学基础
- **不动点理论**：递归程序的理论基础
- **语义组合性**：复合程序的语义组合

### 类型系统理论 (Type System Theory)

**研究类型系统的设计和实现**:

#### 基础类型系统 (Basic Type Systems)

- **简单类型λ演算**：类型系统的基础
- **多态类型系统**：参数多态和特设多态
- **依赖类型系统**：类型依赖值的系统
- **类型安全**：类型系统的安全保证

#### 高级类型系统 (Advanced Type Systems)

- **高阶类型系统**：类型作为一等公民
- **子类型理论**：类型间的包含关系
- **类型推断**：自动推导类型信息
- **类型擦除**：运行时类型信息的处理

## 🎯 理论应用

### 语言设计

- **语法设计**：设计清晰、无歧义的语法
- **语义设计**：定义准确、一致的语义
- **类型设计**：设计安全、表达力强的类型系统

### 编译器实现

- **词法分析**：将源代码转换为词法单元
- **语法分析**：构建抽象语法树
- **语义分析**：类型检查和语义检查
- **代码生成**：生成目标代码

### 程序验证

- **类型检查**：静态类型检查
- **程序验证**：形式化程序验证
- **模型检测**：程序行为验证
- **定理证明**：程序正确性证明

## 📚 相关理论

- [形式逻辑](../02-Formal-Science/02-Formal-Logic/) - 逻辑基础
- [类型论](../02-Formal-Science/04-Type-Theory/) - 类型理论基础
- [自动机理论](06-Automata-Theory/) - 语言识别
- [形式方法](04-Formal-Methods/) - 程序验证

## 🔬 研究方向

### 当前热点

- **依赖类型系统**：结合类型和值的系统
- **线性类型系统**：资源管理的类型系统
- **效应系统**：副作用和计算的类型系统
- **同伦类型论**：几何直觉的类型理论

### 应用领域

- **函数式编程**：Haskell、OCaml、F#
- **系统编程**：Rust、Zig、Vale
- **Web开发**：TypeScript、Elm、PureScript
- **科学计算**：Julia、Idris、Agda

---

**上一级**: [理论层](../README.md)  
**下一级**: [语法理论](01-Syntax-Theory/) | [语义理论](02-Semantics-Theory/) | [类型系统理论](03-Type-System-Theory/)
