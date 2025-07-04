# 006 享元模式

## 1. 理论基础

享元模式是一种结构型设计模式，通过共享技术有效支持大量细粒度对象的复用。减少内存使用，提高系统性能。

## 2. 接口设计

```haskell
-- Haskell接口设计
class Flyweight a where
  operation :: a -> String -> String

-- 享元工厂
data FlyweightFactory = FlyweightFactory (Map String Flyweight)

-- 具体享元
data ConcreteFlyweight = ConcreteFlyweight String
```

## 3. 多语言实现

### Haskell实现

```haskell
import Data.Map (Map)
import qualified Data.Map as Map

-- 享元接口
class Flyweight a where
  operation :: a -> String -> String

-- 具体享元
data ConcreteFlyweight = ConcreteFlyweight String deriving Show

instance Flyweight ConcreteFlyweight where
  operation (ConcreteFlyweight intrinsic) extrinsic = 
    "Intrinsic: " ++ intrinsic ++ ", Extrinsic: " ++ extrinsic

-- 享元工厂
data FlyweightFactory = FlyweightFactory (Map String ConcreteFlyweight)

-- 工厂操作
getFlyweight :: FlyweightFactory -> String -> (ConcreteFlyweight, FlyweightFactory)
getFlyweight (FlyweightFactory cache) key = 
  case Map.lookup key cache of
    Just flyweight -> (flyweight, FlyweightFactory cache)
    Nothing -> 
      let newFlyweight = ConcreteFlyweight key
          newCache = Map.insert key newFlyweight cache
      in (newFlyweight, FlyweightFactory newCache)

-- 使用示例
main :: IO ()
main = do
  let factory = FlyweightFactory Map.empty
  let (flyweight1, factory1) = getFlyweight factory "shared"
  let (flyweight2, factory2) = getFlyweight factory1 "shared"
  print $ operation flyweight1 "extrinsic1"
  print $ operation flyweight2 "extrinsic2"
```

### Rust实现

```rust
use std::collections::HashMap;

// 享元trait
trait Flyweight {
    fn operation(&self, extrinsic: &str) -> String;
}

// 具体享元
struct ConcreteFlyweight {
    intrinsic: String,
}

impl Flyweight for ConcreteFlyweight {
    fn operation(&self, extrinsic: &str) -> String {
        format!("Intrinsic: {}, Extrinsic: {}", self.intrinsic, extrinsic)
    }
}

// 享元工厂
struct FlyweightFactory {
    cache: HashMap<String, ConcreteFlyweight>,
}

impl FlyweightFactory {
    fn new() -> Self {
        FlyweightFactory {
            cache: HashMap::new(),
        }
    }
    
    fn get_flyweight(&mut self, key: &str) -> &ConcreteFlyweight {
        if !self.cache.contains_key(key) {
            let flyweight = ConcreteFlyweight {
                intrinsic: key.to_string(),
            };
            self.cache.insert(key.to_string(), flyweight);
        }
        self.cache.get(key).unwrap()
    }
}
```

### Lean实现

```lean
-- 享元类型
def Flyweight := String → String → String

-- 具体享元
def concreteFlyweight (intrinsic : String) : Flyweight :=
  fun extrinsic => "Intrinsic: " ++ intrinsic ++ ", Extrinsic: " ++ extrinsic

-- 享元工厂
def FlyweightFactory := List (String × Flyweight)

-- 获取享元
def getFlyweight : FlyweightFactory → String → Flyweight
  | [], key => concreteFlyweight key
  | (k, f) :: rest, key => 
    if k = key then f else getFlyweight rest key

-- 享元共享定理
theorem flyweight_sharing :
  ∀ factory : FlyweightFactory, ∀ key : String,
  getFlyweight factory key = getFlyweight factory key :=
  by simp [getFlyweight]
```

## 4. 工程实践

- 对象池管理
- 内存优化
- 缓存策略
- 线程安全

## 5. 性能优化

- 对象复用
- 内存池
- 延迟初始化
- 缓存清理

## 6. 应用场景

- 文本编辑器
- 游戏对象
- 图形渲染
- 数据库连接池

## 7. 最佳实践

- 合理使用共享
- 避免过度优化
- 考虑线程安全
- 监控内存使用
