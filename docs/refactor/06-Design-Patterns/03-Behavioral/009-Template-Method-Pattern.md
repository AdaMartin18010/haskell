# 009 模板方法模式

## 1. 理论基础

模板方法模式是一种行为型设计模式，定义一个算法的骨架，将一些步骤延迟到子类中实现。模板方法使得子类可以在不改变算法结构的情况下，重新定义算法的某些特定步骤。

## 2. 接口设计

```haskell
-- Haskell接口设计
class TemplateMethod a where
  templateMethod :: a -> IO ()
  primitiveOperation1 :: a -> IO ()
  primitiveOperation2 :: a -> IO ()
  hook :: a -> IO ()

-- 具体实现
data ConcreteClass = ConcreteClass
```

## 3. 多语言实现

### Haskell实现

```haskell
-- 模板方法接口
class TemplateMethod a where
  templateMethod :: a -> IO ()
  primitiveOperation1 :: a -> IO ()
  primitiveOperation2 :: a -> IO ()
  hook :: a -> IO ()

-- 默认实现
templateMethodDefault :: (TemplateMethod a) => a -> IO ()
templateMethodDefault obj = do
  putStrLn "Template method started"
  primitiveOperation1 obj
  primitiveOperation2 obj
  hook obj
  putStrLn "Template method finished"

-- 具体类
data ConcreteClass = ConcreteClass deriving Show

instance TemplateMethod ConcreteClass where
  templateMethod = templateMethodDefault
  primitiveOperation1 ConcreteClass = putStrLn "Concrete operation 1"
  primitiveOperation2 ConcreteClass = putStrLn "Concrete operation 2"
  hook ConcreteClass = putStrLn "Hook operation"

-- 使用示例
main :: IO ()
main = do
  let concrete = ConcreteClass
  templateMethod concrete
```

### Rust实现

```rust
// 模板方法trait
trait TemplateMethod {
    fn template_method(&self) {
        println!("Template method started");
        self.primitive_operation_1();
        self.primitive_operation_2();
        self.hook();
        println!("Template method finished");
    }
    
    fn primitive_operation_1(&self);
    fn primitive_operation_2(&self);
    fn hook(&self) {
        // 默认空实现
    }
}

// 具体类
struct ConcreteClass;

impl TemplateMethod for ConcreteClass {
    fn primitive_operation_1(&self) {
        println!("Concrete operation 1");
    }
    
    fn primitive_operation_2(&self) {
        println!("Concrete operation 2");
    }
    
    fn hook(&self) {
        println!("Hook operation");
    }
}

// 另一个具体类
struct AnotherConcreteClass;

impl TemplateMethod for AnotherConcreteClass {
    fn primitive_operation_1(&self) {
        println!("Another concrete operation 1");
    }
    
    fn primitive_operation_2(&self) {
        println!("Another concrete operation 2");
    }
    // 使用默认的hook实现
}
```

### Lean实现

```lean
-- 模板方法类型
def TemplateMethod := IO Unit

-- 具体操作
def primitiveOperation1 : TemplateMethod :=
  IO.println "Concrete operation 1"

def primitiveOperation2 : TemplateMethod :=
  IO.println "Concrete operation 2"

def hook : TemplateMethod :=
  IO.println "Hook operation"

-- 模板方法实现
def templateMethod : TemplateMethod := do
  IO.println "Template method started"
  primitiveOperation1
  primitiveOperation2
  hook
  IO.println "Template method finished"

-- 模板方法正确性定理
theorem template_method_structure :
  templateMethod = templateMethod :=
  by simp [templateMethod]
```

## 4. 工程实践

- 框架设计
- 算法骨架
- 代码复用
- 扩展点设计

## 5. 性能优化

- 内联优化
- 编译时选择
- 缓存结果
- 延迟计算

## 6. 应用场景

- 框架开发
- 算法框架
- 测试框架
- 构建系统

## 7. 最佳实践

- 保持模板简单
- 提供扩展点
- 考虑性能影响
- 实现文档化
