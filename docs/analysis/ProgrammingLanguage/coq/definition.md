# Coq 形式语言的形式系统（CIC in Coq）

> 中英双语；覆盖语法/判断/归纳族/宇宙/Prop-Set-Type；参考 Coq Refman/HoTT/nLab。

## 1. 判断与语法 Judgements & Syntax

- Γ ⊢ A : s（类型归属）; Γ ⊢ a : A（项归属）; s ∈ {Prop, Set, Type₀, Type₁, ...}
- 依赖函数（Π‑types）、依赖对（Σ‑types 可由记录/存在编码）、恒等类型（eq）

## 2. 宇宙与层级 Universes

- 层级避免悖论：Type₀ : Type₁ : Type₂ : ...；宇宙多态（Universe Polymorphism）
- Prop 与 Set：Prop 面向命题/证明（可擦除），Set/Type 面向数据/计算

## 3. 归纳/协代数类型 Inductive/Coinductive

- Inductive 定义数据与归纳原理；CoInductive 定义无限对象与核递归
- 互递归（mutual）、索引族（indexed families），依赖消解与模式匹配

## 4. 递归与守恒 Recursion & Guardedness

- Fixpoint/Program Fixpoint；结构递归或可证明终止性
- CoFixpoint 要求守恒（productivity）

## 5. 证明引擎与战术 Proof Engine & Tactics

- 基础 tactics：intro/induction/destruct/rewrite/reflexivity
- 自动化：auto/eauto; lia/nia; ring/field; firstorder
- Ltac/SSReflect/Elpi；Hint 数据库；canonical structures（MathComp）

## 6. 抽取与计算 Extraction & Computation

- `Extraction` 到 OCaml/Haskell/Scheme；通过证据擦除保证运行时纯净
- 计算规则：β/δ/ι/ζ 归约；`cbv/cbn/lazy` 策略

## 7. 模块化与依赖管理 Modularization

- Modules/Functors；Sections 与上下文；OPAM/Coq Platform 管理

## 8. 关系到 HoTT/Univalence Relations to HoTT

- 可加载 HoTT/Univalence 扩展或使用 Cubical；等价即相等的语义（可选）

## 9. 参考 References

- Coq Reference Manual；Software Foundations；Mathematical Components；Certified Programming with Dependent Types
