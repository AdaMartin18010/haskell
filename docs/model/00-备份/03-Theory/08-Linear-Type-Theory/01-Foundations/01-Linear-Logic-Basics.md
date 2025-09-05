# 01. 线性逻辑基础 (Linear Logic Basics)

## 概述

线性逻辑是由Jean-Yves Girard在1987年提出的逻辑系统，它基于资源管理的概念，强调每个假设必须被精确使用一次。这与传统逻辑中的假设可以重复使用形成对比。

## 核心思想

### 1. 资源视角

线性逻辑将逻辑公式视为**资源**，每个资源在使用时必须被精确消耗，不能重复使用。

### 2. 线性蕴含

线性蕴含 `A ⊸ B` 表示：如果有一个 `A` 类型的资源，可以产生一个 `B` 类型的资源，但 `A` 资源会被消耗。

## 形式化定义

### 语法

```
A, B ::= α | A ⊸ B | A ⊗ B | A ⊕ B | A & B | !A | ?A | 1 | 0 | ⊤ | ⊥
```

其中：

- `α`: 原子命题
- `⊸`: 线性蕴含
- `⊗`: 乘性合取（张量积）
- `⊕`: 加性析取
- `&`: 加性合取
- `!`: 指数（必然性）
- `?`: 指数（可能性）
- `1`: 单位元
- `0`: 零元
- `⊤`: 真
- `⊥`: 假

### 推理规则

#### 线性蕴含规则

```
Γ, A ⊢ B
───────── (⊸I)
Γ ⊢ A ⊸ B

Γ ⊢ A ⊸ B    Δ ⊢ A
────────────────── (⊸E)
Γ, Δ ⊢ B
```

#### 乘性合取规则

```
Γ ⊢ A    Δ ⊢ B
─────────────── (⊗I)
Γ, Δ ⊢ A ⊗ B

Γ ⊢ A ⊗ B    Δ, A, B ⊢ C
──────────────────────── (⊗E)
Γ, Δ ⊢ C
```

#### 指数规则

```
!Γ ⊢ A
────── (!I)
!Γ ⊢ !A

Γ ⊢ !A    Δ, A ⊢ B
────────────────── (!E)
Γ, Δ ⊢ B
```

## Haskell实现

### 基本线性类型

```haskell
-- 线性函数类型
type LinearFunction a b = a %1 -> b

-- 线性积类型
data LinearPair a b = LinearPair a b

-- 线性和类型
data LinearSum a b = Left a | Right b

-- 线性单位类型
data LinearUnit = LinearUnit

-- 线性零类型
data LinearVoid
```

### 线性逻辑连接词

```haskell
-- 线性蕴含
class LinearImplication a b where
    linearImplies :: a %1 -> b

-- 乘性合取
class MultiplicativeConjunction a b where
    tensor :: a %1 -> b %1 -> (a, b)

-- 指数类型
class Exponential a where
    bang :: a -> !a
    unbang :: !a %1 -> a
```

## 语义解释

### 1. 资源语义

- `A ⊸ B`: 消耗一个A资源，产生一个B资源
- `A ⊗ B`: 同时拥有A和B资源
- `A ⊕ B`: 拥有A或B资源之一
- `!A`: 可以重复使用的A资源

### 2. 游戏语义

- 将证明视为两个玩家之间的游戏
- 每个连接词对应特定的游戏规则
- 线性性确保游戏的公平性

### 3. 几何语义

- 将公式解释为几何对象
- 证明对应几何变换
- 线性性对应几何约束

## 与直觉逻辑的关系

### 嵌入映射

```
(A → B) ↦ !A ⊸ B
(A ∧ B) ↦ A & B
(A ∨ B) ↦ !A ⊕ !B
```

### 关键差异

1. **资源管理**: 线性逻辑精确管理资源使用
2. **复制控制**: 传统逻辑允许任意复制，线性逻辑限制复制
3. **结构规则**: 线性逻辑去除了收缩和弱化规则

## 计算解释

### Curry-Howard对应

```
证明 ↔ 程序
公式 ↔ 类型
推理规则 ↔ 程序构造
```

### 线性λ演算

```haskell
-- 线性λ抽象
λx. M :: A ⊸ B

-- 线性应用
M N :: B  (其中 M :: A ⊸ B, N :: A)

-- 线性变量使用
x :: A  (每个变量必须被精确使用一次)
```

## 应用示例

### 1. 内存管理

```haskell
-- 线性文件句柄
data FileHandle = FileHandle Handle

-- 线性文件操作
readFile :: FileHandle %1 -> (FileHandle, String)
writeFile :: FileHandle %1 -> String -> FileHandle

-- 确保文件句柄被正确关闭
closeFile :: FileHandle %1 -> ()
```

### 2. 并发编程

```haskell
-- 线性通道
data Channel a = Channel (MVar a)

-- 线性发送和接收
send :: Channel a %1 -> a -> Channel a
receive :: Channel a %1 -> (Channel a, a)
```

### 3. 资源安全

```haskell
-- 线性锁
data Lock = Lock (MVar ())

-- 线性加锁和解锁
acquire :: Lock %1 -> (Lock, ())
release :: Lock %1 -> ()
```

## 理论意义

1. **资源管理**: 提供精确的资源管理机制
2. **并发安全**: 确保并发程序的正确性
3. **性能优化**: 支持编译时优化
4. **形式化验证**: 为程序验证提供理论基础

## 研究方向

1. **线性类型推断**: 自动推导线性类型
2. **线性效应系统**: 结合效应系统的线性类型
3. **线性协议**: 通信协议的线性类型
4. **量子计算**: 量子信息的线性类型
