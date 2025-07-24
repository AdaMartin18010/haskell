# 9.6 三语言对比 Comparison (Haskell/Rust/Lean) #FormalLanguageTheory-9.6

## 9.6.1 对比表格 Comparison Table #FormalLanguageTheory-9.6.1

| 特性/语言 | Haskell | Rust | Lean |
|-----------|---------|------|------|
| 语言建模 | 数据类型/ADT | struct/enum | 归纳类型 |
| 文法表达 | 解析器组合子/ADT | trait/宏/解析器库 | 归纳定义 |
| 自动机实现 | 有限自动机/解析器库 | 状态机/trait实现 | 形式化自动机 |
| 工程应用 | 语法分析、DSL | 语法分析、编译器 | 形式化语言证明 |

## 9.6.2 典型代码对比 Typical Code Comparison #FormalLanguageTheory-9.6.2

```haskell
-- Haskell: 解析器组合子定义简单表达式
expr = number <|> (char '(' *> expr <* char ')')
```

```rust
// Rust: nom库定义简单表达式解析器
use nom::{IResult, character::complete::char};
fn expr(input: &str) -> IResult<&str, &str> {
    nom::branch::alt((number, |i| {
        let (i, _) = char('(')(i)?;
        let (i, e) = expr(i)?;
        let (i, _) = char(')')(i)?;
        Ok((i, e))
    }))(input)
}
```

```lean
-- Lean: 归纳定义表达式文法
inductive expr
| num : ℕ → expr
| paren : expr → expr
```

## 9.6.3 哲学与工程意义 Philosophical & Engineering Significance #FormalLanguageTheory-9.6.3

- Haskell：强调抽象与组合性，适合DSL与语法建模。
- Rust：强调系统安全与高效语法分析。
- Lean：强调形式化证明与语言结构的可验证性。

## 9.6.4 国际标准与Wiki对标 International Standards & Wiki #FormalLanguageTheory-9.6.4

- Haskell: Haskell 2010, ISO, Wiki
- Rust: Rust Reference, ISO, Wiki
- Lean: Lean Reference, mathlib, Wiki

## 9.6.5 相关Tag

`# FormalLanguageTheory #FormalLanguageTheory-9 #FormalLanguageTheory-9.6 #FormalLanguageTheory-9.6.1 #FormalLanguageTheory-9.6.2 #FormalLanguageTheory-9.6.3 #FormalLanguageTheory-9.6.4`
