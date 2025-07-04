# 004 组合模式

## 1. 理论基础

组合模式是一种结构型设计模式，将对象组合成树形结构以表示"部分-整体"的层次结构。使客户端对单个对象和组合对象具有一致的访问性。

## 2. 接口设计

```haskell
-- Haskell接口设计
class Component a where
  operation :: a -> String
  add :: a -> a -> Maybe a
  remove :: a -> a -> Maybe a
  getChild :: a -> Int -> Maybe a

-- 叶子节点
data Leaf = Leaf String

-- 复合节点
data Composite = Composite String [Component]
```

## 3. 多语言实现

### Haskell实现

```haskell
-- 组件接口
class Component a where
  operation :: a -> String
  add :: a -> a -> Maybe a
  remove :: a -> a -> Maybe a
  getChild :: a -> Int -> Maybe a

-- 叶子节点
data Leaf = Leaf String deriving Show

instance Component Leaf where
  operation (Leaf name) = "Leaf: " ++ name
  add _ _ = Nothing
  remove _ _ = Nothing
  getChild _ _ = Nothing

-- 复合节点
data Composite = Composite String [Composite] deriving Show

instance Component Composite where
  operation (Composite name _) = "Composite: " ++ name
  add (Composite name children) child = 
    Just $ Composite name (child : children)
  remove (Composite name children) child = 
    Just $ Composite name (filter (/= child) children)
  getChild (Composite _ children) index = 
    if index >= 0 && index < length children
    then Just (children !! index)
    else Nothing

-- 使用示例
main :: IO ()
main = do
  let leaf1 = Leaf "Leaf1"
  let leaf2 = Leaf "Leaf2"
  let composite = Composite "Root" [leaf1, leaf2]
  print $ operation composite
```

### Rust实现

```rust
// 组件trait
trait Component {
    fn operation(&self) -> String;
    fn add(&mut self, component: Box<dyn Component>) -> bool;
    fn remove(&mut self, component: &Box<dyn Component>) -> bool;
    fn get_child(&self, index: usize) -> Option<&Box<dyn Component>>;
}

// 叶子节点
struct Leaf {
    name: String,
}

impl Component for Leaf {
    fn operation(&self) -> String {
        format!("Leaf: {}", self.name)
    }
    
    fn add(&mut self, _component: Box<dyn Component>) -> bool {
        false
    }
    
    fn remove(&mut self, _component: &Box<dyn Component>) -> bool {
        false
    }
    
    fn get_child(&self, _index: usize) -> Option<&Box<dyn Component>> {
        None
    }
}

// 复合节点
struct Composite {
    name: String,
    children: Vec<Box<dyn Component>>,
}

impl Component for Composite {
    fn operation(&self) -> String {
        format!("Composite: {}", self.name)
    }
    
    fn add(&mut self, component: Box<dyn Component>) -> bool {
        self.children.push(component);
        true
    }
    
    fn remove(&mut self, component: &Box<dyn Component>) -> bool {
        if let Some(pos) = self.children.iter().position(|c| std::ptr::eq(c.as_ref(), component.as_ref())) {
            self.children.remove(pos);
            true
        } else {
            false
        }
    }
    
    fn get_child(&self, index: usize) -> Option<&Box<dyn Component>> {
        self.children.get(index)
    }
}
```

### Lean实现

```lean
-- 组件类型
inductive Component where
  | Leaf : String → Component
  | Composite : String → List Component → Component

-- 操作函数
def operation : Component → String
  | Component.Leaf name => "Leaf: " ++ name
  | Component.Composite name _ => "Composite: " ++ name

-- 添加子组件
def add : Component → Component → Component
  | Component.Composite name children, child => 
    Component.Composite name (child :: children)
  | leaf, _ => leaf

-- 组合模式性质定理
theorem composite_operation_preserved :
  ∀ c1 c2 : Component, 
  operation (add c1 c2) = operation c1 :=
  by simp [operation, add]
```

## 4. 工程实践

- 树形结构管理
- 递归操作
- 统一接口
- 层次遍历

## 5. 性能优化

- 缓存遍历结果
- 延迟加载
- 索引优化

## 6. 应用场景

- 文件系统
- GUI组件树
- 组织架构
- 菜单系统

## 7. 最佳实践

- 保持接口一致
- 避免深层递归
- 考虑内存使用
- 实现访问者模式
