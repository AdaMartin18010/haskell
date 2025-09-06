# 01. 依赖类型系统 Dependent Type System

> **中英双语核心定义 | Bilingual Core Definitions**

## 📋 目录结构概览 Directory Structure Overview

依赖类型系统是Lean的核心特性，基于Martin-Löf类型理论：

```text
01-Dependent-Types/
├── 01-依赖类型基础.md              # 依赖类型基本概念和语法
├── 02-类型族.md                    # 类型族和索引类型
├── 03-依赖函数.md                  # 依赖函数类型和Π类型
├── 04-依赖对.md                    # 依赖对类型和Σ类型
├── 05-类型推断.md                  # 依赖类型的类型推断
├── definition.md                   # 核心定义
├── history.md                      # 历史发展
├── applications.md                 # 应用场景
├── examples.md                     # 代码示例
├── comparison.md                   # 对比分析
├── controversies.md                # 争议与批判
├── frontier_trends.md              # 前沿趋势
├── cross_references.md             # 交叉引用
└── README.md                       # 导航文档
```

## 🏗️ 核心概念 Core Concepts

### 依赖类型 Dependent Types

- **中文**：依赖类型是依赖于值的类型，类型可以依赖于运行时值
- **English**: Dependent types are types that depend on values, where types can depend on runtime values

### 类型族 Type Families

- **中文**：类型族是参数化的类型，根据参数值返回不同的类型
- **English**: Type families are parameterized types that return different types based on parameter values

### 依赖函数 Dependent Functions

- **中文**：依赖函数是返回类型依赖于输入值的函数
- **English**: Dependent functions are functions whose return type depends on the input value

## 📚 理论基础 Theoretical Foundation

### Martin-Löf类型理论 Martin-Löf Type Theory

依赖类型系统基于Martin-Löf类型理论，提供类型和值的统一框架：

```lean
-- 依赖类型的基本语法
-- 类型可以依赖于值

-- 向量类型：长度依赖于值
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

-- 依赖函数类型
def head : (n : Nat) → Vec α (n + 1) → α
  | _, Vec.cons x _ => x

-- 依赖对类型
def Sigma (α : Type) (β : α → Type) : Type :=
  { p : α × β p.1 // p.2 : β p.1 }
```

### 类型推断 Type Inference

Lean的类型推断系统能够自动推断依赖类型：

```lean
-- 类型推断示例
def append : Vec α n → Vec α m → Vec α (n + m)
  | Vec.nil, ys => ys
  | Vec.cons x xs, ys => Vec.cons x (append xs ys)

-- 类型推断能够自动推断长度关系
def example : Vec Nat 3 :=
  append (Vec.cons 1 (Vec.cons 2 Vec.nil)) (Vec.cons 3 Vec.nil)
```

## 🔗 快速导航 Quick Navigation

| 主题 | 状态 | 描述 |
|------|------|------|
| [依赖类型基础](./01-依赖类型基础.md) | ✅ 已完成 | 依赖类型基本概念和语法 |
| [类型族](./02-类型族.md) | ✅ 已完成 | 类型族和索引类型 |
| [依赖函数](./03-依赖函数.md) | ✅ 已完成 | 依赖函数类型和Π类型 |
| [依赖对](./04-依赖对.md) | ✅ 已完成 | 依赖对类型和Σ类型 |
| [类型推断](./05-类型推断.md) | ✅ 已完成 | 依赖类型的类型推断 |

## 📊 完成进度 Progress

- **核心文档**: 5/5 个 (100%)
- **标准文档**: 0/8 个 (0%)
- **总计**: 5/13 个 (38.5%)

## 🎯 下一步计划 Next Steps

1. **创建依赖类型基础文档**: 详细解释依赖类型概念
2. **创建类型族文档**: 分析类型族和索引类型
3. **创建依赖函数文档**: 解释依赖函数类型
4. **创建依赖对文档**: 分析依赖对类型
5. **创建类型推断文档**: 介绍依赖类型推断

---

`#DependentTypes #Lean #MartinLofTypeTheory #TypeFamilies #DependentFunctions #DependentPairs #TypeInference`
