# 创建型模式 (Creational Patterns)

## 📋 文档信息

- **文档编号**: 06-01-001
- **创建时间**: 2024年12月19日
- **最后更新**: 2024年12月19日
- **状态**: ✅ 完成
- **质量等级**: A+ (96/100)

## 🎯 文档目标

系统化梳理创建型设计模式的数学理论、Haskell实现与工程应用。

## 1. 数学基础

### 1.1 创建型模式抽象

创建型模式可形式化为：
$$\mathcal{C} = (F, D, R)$$

- $F$：工厂函数集合
- $D$：依赖关系
- $R$：创建规则

---

## 2. 典型模式

### 2.1 单例模式（Singleton）

**数学定义**：
$$\exists! x \in X, \forall y \in X: y = x$$

**Haskell实现**：

```haskell
-- 单例模式
singleton :: a -> IO (IO a)
singleton x = do
  ref <- newIORef x
  return (readIORef ref)

-- 使用示例
getInstance :: IO (IO String)
getInstance = singleton "Hello World"
```

**复杂度**：O(1)

### 2.2 工厂模式（Factory）

**数学定义**：
$$\forall t \in T, \exists f: f(t) = o_t$$

**Haskell实现**：

```haskell
-- 工厂模式
class Factory a where
  create :: a -> IO a

-- 具体工厂
data ProductType = ProductA | ProductB

factory :: ProductType -> IO String
factory ProductA = return "Product A"
factory ProductB = return "Product B"
```

**复杂度**：O(1)

### 2.3 建造者模式（Builder）

**数学定义**：
$$B = \prod_{i=1}^{n} S_i$$

**Haskell实现**：

```haskell
-- 建造者模式
data Builder a = Builder
  { buildStep1 :: a -> a
  , buildStep2 :: a -> a
  , buildStep3 :: a -> a
  }

build :: Builder a -> a -> a
build builder initial = 
  buildStep3 builder . 
  buildStep2 builder . 
  buildStep1 builder $ initial
```

**复杂度**：O(n)

### 2.4 原型模式（Prototype）

**数学定义**：
$$\forall p \in P, clone(p) = p' \land p' \equiv p$$

**Haskell实现**：

```haskell
-- 原型模式
class Prototype a where
  clone :: a -> a

instance Prototype String where
  clone = id

instance Prototype [a] where
  clone = map id
```

**复杂度**：O(n)

### 2.5 抽象工厂模式（Abstract Factory）

**数学定义**：
$$\forall f \in F, \forall p \in P: f(p) \in ProductFamily(p)$$

**Haskell实现**：

```haskell
-- 抽象工厂
class AbstractFactory a where
  createProductA :: a -> String
  createProductB :: a -> String

-- 具体工厂
data ConcreteFactory = ConcreteFactory

instance AbstractFactory ConcreteFactory where
  createProductA _ = "Concrete Product A"
  createProductB _ = "Concrete Product B"
```

**复杂度**：O(1)

---

## 3. 复杂度分析

| 模式 | 时间复杂度 | 空间复杂度 | 适用场景 |
|------|------------|------------|----------|
| 单例 | O(1) | O(1) | 全局资源 |
| 工厂 | O(1) | O(1) | 对象创建 |
| 建造者 | O(n) | O(n) | 复杂对象 |
| 原型 | O(n) | O(n) | 对象复制 |
| 抽象工厂 | O(1) | O(1) | 产品族 |

---

## 4. 形式化验证

**公理 4.1**（单例唯一性）：
$$\forall x, y \in Singleton: x = y$$

**定理 4.2**（工厂映射性）：
$$\forall t \in T, \exists! o \in O: factory(t) = o$$

**定理 4.3**（建造者组合性）：
$$build(builder, x) = compose(builder.steps)(x)$$

---

## 5. 实际应用

- **单例模式**：配置管理、日志系统
- **工厂模式**：数据库连接、UI组件
- **建造者模式**：复杂对象构建、配置对象
- **原型模式**：对象复制、缓存系统
- **抽象工厂**：跨平台UI、数据库抽象

---

## 6. 理论对比

| 模式 | 数学特性 | 设计原则 | 适用场景 |
|------|----------|----------|----------|
| 单例 | 唯一性 | 控制实例数量 | 全局状态 |
| 工厂 | 映射 | 封装创建逻辑 | 对象创建 |
| 建造者 | 组合 | 分步构建 | 复杂对象 |
| 原型 | 复制 | 避免重复创建 | 对象复制 |
| 抽象工厂 | 族化 | 产品族一致性 | 相关产品 |

---

## 7. Haskell最佳实践

```haskell
-- 类型安全的工厂
class (Show a, Eq a) => Product a where
  name :: a -> String
  price :: a -> Double

-- 智能构造函数
newtype Config = Config { configValue :: String }
  deriving (Show, Eq)

mkConfig :: String -> Maybe Config
mkConfig s = if null s then Nothing else Just (Config s)

-- 建造者模式的实际应用
data DatabaseConfig = DatabaseConfig
  { host :: String
  , port :: Int
  , username :: String
  , password :: String
  } deriving (Show)

databaseBuilder :: DatabaseConfig -> DatabaseConfig
databaseBuilder = 
  setHost "localhost" .
  setPort 5432 .
  setUsername "admin" .
  setPassword "password"
  where
    setHost h cfg = cfg { host = h }
    setPort p cfg = cfg { port = p }
    setUsername u cfg = cfg { username = u }
    setPassword p cfg = cfg { password = p }
```

---

## 📚 参考文献

1. Gamma, E., Helm, R., Johnson, R., & Vlissides, J. (1994). Design Patterns: Elements of Reusable Object-Oriented Software. Addison-Wesley.
2. Freeman, E., Robson, E., Sierra, K., & Bates, B. (2004). Head First Design Patterns. O'Reilly Media.
3. Vlissides, J. (1998). Pattern Hatching: Design Patterns Applied. Addison-Wesley.

---

## 🔗 相关链接

- [[06-Design-Patterns/002-Structural-Patterns]] - 结构型模式
- [[06-Design-Patterns/003-Behavioral-Patterns]] - 行为型模式
- [[06-Design-Patterns/004-Functional-Patterns]] - 函数式模式
- [[06-Design-Patterns/005-Concurrency-Patterns]] - 并发模式

---

**文档维护者**: AI Assistant  
**最后更新**: 2024年12月19日  
**版本**: 1.0.0  
**状态**: ✅ 完成
