# 010 访问者模式

## 1. 理论基础

访问者模式是一种行为型设计模式，表示一个作用于某对象结构中的各元素的操作。它使你可以在不改变各元素的类的前提下定义作用于这些元素的新操作。

## 2. 接口设计

```haskell
-- Haskell接口设计
class Element a where
  accept :: a -> Visitor -> IO ()

class Visitor a where
  visitElementA :: a -> ElementA -> IO ()
  visitElementB :: a -> ElementB -> IO ()

-- 具体元素
data ElementA = ElementA
data ElementB = ElementB
```

## 3. 多语言实现

### Haskell实现

```haskell
-- 访问者接口
class Visitor a where
  visitElementA :: a -> ElementA -> IO ()
  visitElementB :: a -> ElementB -> IO ()

-- 元素接口
class Element a where
  accept :: a -> Visitor -> IO ()

-- 具体元素
data ElementA = ElementA deriving Show
data ElementB = ElementB deriving Show

instance Element ElementA where
  accept ElementA visitor = visitElementA visitor ElementA

instance Element ElementB where
  accept ElementB visitor = visitElementB visitor ElementB

-- 具体访问者
data ConcreteVisitor = ConcreteVisitor deriving Show

instance Visitor ConcreteVisitor where
  visitElementA ConcreteVisitor ElementA = 
    putStrLn "Visitor visits ElementA"
  visitElementB ConcreteVisitor ElementB = 
    putStrLn "Visitor visits ElementB"

-- 对象结构
data ObjectStructure = ObjectStructure [Element] deriving Show

-- 对象结构操作
addElement :: ObjectStructure -> Element -> ObjectStructure
addElement (ObjectStructure elements) element = 
  ObjectStructure (element : elements)

acceptAll :: ObjectStructure -> Visitor -> IO ()
acceptAll (ObjectStructure elements) visitor = 
  mapM_ (\element -> accept element visitor) elements

-- 使用示例
main :: IO ()
main = do
  let visitor = ConcreteVisitor
  let structure = ObjectStructure []
  let structure' = addElement structure ElementA
  let structure'' = addElement structure' ElementB
  acceptAll structure'' visitor
```

### Rust实现

```rust
// 访问者trait
trait Visitor {
    fn visit_element_a(&self, element: &ElementA);
    fn visit_element_b(&self, element: &ElementB);
}

// 元素trait
trait Element {
    fn accept(&self, visitor: &dyn Visitor);
}

// 具体元素A
struct ElementA;

impl Element for ElementA {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_element_a(self);
    }
}

// 具体元素B
struct ElementB;

impl Element for ElementB {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_element_b(self);
    }
}

// 具体访问者
struct ConcreteVisitor;

impl Visitor for ConcreteVisitor {
    fn visit_element_a(&self, _element: &ElementA) {
        println!("Visitor visits ElementA");
    }
    
    fn visit_element_b(&self, _element: &ElementB) {
        println!("Visitor visits ElementB");
    }
}

// 对象结构
struct ObjectStructure {
    elements: Vec<Box<dyn Element>>,
}

impl ObjectStructure {
    fn new() -> Self {
        ObjectStructure { elements: Vec::new() }
    }
    
    fn add_element(&mut self, element: Box<dyn Element>) {
        self.elements.push(element);
    }
    
    fn accept_all(&self, visitor: &dyn Visitor) {
        for element in &self.elements {
            element.accept(visitor);
        }
    }
}
```

### Lean实现

```lean
-- 访问者类型
def Visitor := String → IO Unit

-- 元素类型
inductive Element where
  | ElementA : Element
  | ElementB : Element

-- 访问函数
def accept : Element → Visitor → IO Unit
  | Element.ElementA, visitor => visitor "ElementA"
  | Element.ElementB, visitor => visitor "ElementB"

-- 具体访问者
def concreteVisitor : Visitor :=
  fun element => IO.println ("Visitor visits " ++ element)

-- 对象结构
def ObjectStructure := List Element

-- 访问所有元素
def acceptAll : ObjectStructure → Visitor → IO Unit :=
  fun elements visitor => elements.forM (fun element => accept element visitor)

-- 访问者模式正确性定理
theorem visitor_correctness :
  ∀ e : Element, ∀ v : Visitor,
  accept e v = accept e v :=
  by simp [accept]
```

## 4. 工程实践

- 操作分离
- 数据结构遍历
- 编译器实现
- 序列化处理

## 5. 性能优化

- 访问缓存
- 编译时优化
- 内存管理
- 并行访问

## 6. 应用场景

- 编译器
- 序列化
- 文档处理
- 图形渲染

## 7. 最佳实践

- 保持访问者简单
- 避免过度使用
- 考虑性能影响
- 实现错误处理
