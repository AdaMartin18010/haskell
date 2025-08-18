# 1.1 定义 Definition

Tag: #TypeSystems-1.1

## 中文

类型系统是对程序项进行分类与约束的形式化机制，通过类型赋予项以可判定的语义边界，以提升正确性、可验证性与可维护性。

## English

A type system is a formal mechanism that classifies and constrains program terms with types, imposing decidable semantic boundaries to improve correctness, verifiability, and maintainability.

## 形式化 Formalization

- 判断式 Judgment:  Γ ⊢ e : T
- 规则 Rules: 变量/抽象/应用、Let、多态、代换、保型

## Haskell / Rust / Lean 快览 Quick Glance

- Haskell: HM 推断 + 扩展（GADTs, TypeFamilies, LinearTypes, Dependent Haskell）
- Rust: 所有权/借用/生命周期与 trait 系统
- Lean: 依赖类型、宇宙分层、归纳家族、证明即程序

## 参考 References

- #Cross: #TypeSystems-1.11
