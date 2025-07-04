# 模板方法模式（Template Method Pattern）

## 概述
模板方法模式是一种行为型设计模式，定义一个操作中的算法骨架，将某些步骤延迟到子类中实现。模板方法使得子类可以不改变算法的结构即可重定义该算法的某些特定步骤。

## 理论基础
- **算法骨架**：定义算法的主要步骤
- **钩子方法**：子类可以重写的特定步骤
- **不变结构**：保持算法结构不变

## Rust实现示例
```rust
trait AbstractClass {
    fn template_method(&self) -> String {
        let mut result = String::new();
        result.push_str(&self.primitive_operation1());
        result.push_str(&self.primitive_operation2());
        result.push_str(&self.primitive_operation3());
        result
    }
    
    fn primitive_operation1(&self) -> String;
    fn primitive_operation2(&self) -> String;
    fn primitive_operation3(&self) -> String;
}

struct ConcreteClassA;

impl AbstractClass for ConcreteClassA {
    fn primitive_operation1(&self) -> String {
        "具体类A的操作1".to_string()
    }
    
    fn primitive_operation2(&self) -> String {
        "具体类A的操作2".to_string()
    }
    
    fn primitive_operation3(&self) -> String {
        "具体类A的操作3".to_string()
    }
}

struct ConcreteClassB;

impl AbstractClass for ConcreteClassB {
    fn primitive_operation1(&self) -> String {
        "具体类B的操作1".to_string()
    }
    
    fn primitive_operation2(&self) -> String {
        "具体类B的操作2".to_string()
    }
    
    fn primitive_operation3(&self) -> String {
        "具体类B的操作3".to_string()
    }
}

fn main() {
    let concrete_a = ConcreteClassA;
    let concrete_b = ConcreteClassB;
    
    println!("{}", concrete_a.template_method());
    println!("{}", concrete_b.template_method());
}
```

## Haskell实现示例
```haskell
class AbstractClass a where
    templateMethod :: a -> String
    templateMethod obj = 
        primitiveOperation1 obj ++ 
        primitiveOperation2 obj ++ 
        primitiveOperation3 obj
    
    primitiveOperation1 :: a -> String
    primitiveOperation2 :: a -> String
    primitiveOperation3 :: a -> String

data ConcreteClassA = ConcreteClassA
instance AbstractClass ConcreteClassA where
    primitiveOperation1 _ = "具体类A的操作1"
    primitiveOperation2 _ = "具体类A的操作2"
    primitiveOperation3 _ = "具体类A的操作3"

data ConcreteClassB = ConcreteClassB
instance AbstractClass ConcreteClassB where
    primitiveOperation1 _ = "具体类B的操作1"
    primitiveOperation2 _ = "具体类B的操作2"
    primitiveOperation3 _ = "具体类B的操作3"

main = do
    let concreteA = ConcreteClassA
    let concreteB = ConcreteClassB
    
    putStrLn $ templateMethod concreteA
    putStrLn $ templateMethod concreteB
```

## Lean实现思路
```lean
class AbstractClass (α : Type) where
  templateMethod : α → String
  primitiveOperation1 : α → String
  primitiveOperation2 : α → String
  primitiveOperation3 : α → String

def templateMethod [AbstractClass α] (obj : α) : String :=
  AbstractClass.primitiveOperation1 obj ++ 
  AbstractClass.primitiveOperation2 obj ++ 
  AbstractClass.primitiveOperation3 obj

structure ConcreteClassA
instance : AbstractClass ConcreteClassA where
  primitiveOperation1 _ := "具体类A的操作1"
  primitiveOperation2 _ := "具体类A的操作2"
  primitiveOperation3 _ := "具体类A的操作3"

structure ConcreteClassB
instance : AbstractClass ConcreteClassB where
  primitiveOperation1 _ := "具体类B的操作1"
  primitiveOperation2 _ := "具体类B的操作2"
  primitiveOperation3 _ := "具体类B的操作3"
```

## 应用场景
- 框架设计
- 算法模板
- 构建流程
- 测试框架

## 最佳实践
- 保持模板方法稳定
- 合理使用钩子方法
- 避免过度抽象 