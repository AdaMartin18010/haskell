# 004 组合模式 (Composite Pattern)

## 1. 理论基础

### 1.1 模式定义

组合模式是一种结构型设计模式，将对象组合成树形结构以表示"部分-整体"的层次结构。使客户端对单个对象和组合对象具有一致的访问性。

### 1.2 核心概念

- **Component（组件）**: 定义组合中对象的接口，为所有对象声明通用接口
- **Leaf（叶子）**: 组合中的叶子节点对象，没有子节点
- **Composite（复合）**: 定义有子部件的那些部件的行为，存储子部件

### 1.3 设计原则

- **开闭原则**: 对扩展开放，对修改封闭
- **单一职责**: 每个类只负责一个功能
- **里氏替换**: 子类可以替换父类

### 1.4 优缺点分析

**优点:**

- 简化客户端代码，客户端可以一致地处理单个对象和组合对象
- 容易添加新类型的组件
- 符合开闭原则

**缺点:**

- 使设计过于一般化，可能难以限制组合中的组件类型
- 在运行时检查类型可能很困难

## 2. 接口设计

### 2.1 核心接口

```haskell
-- Haskell接口设计
class Component a where
  operation :: a -> String
  add :: a -> a -> Maybe a
  remove :: a -> a -> Maybe a
  getChild :: a -> Int -> Maybe a
  getChildren :: a -> [a]
  isComposite :: a -> Bool

-- 叶子节点
data Leaf = Leaf String

-- 复合节点
data Composite = Composite String [Component]
```

### 2.2 扩展接口

```haskell
-- 支持遍历的接口
class (Component a) => TraversableComponent a where
  traverse :: (Monad m) => (a -> m b) -> a -> m b
  mapM :: (Monad m) => (a -> m b) -> a -> m [b]
  
-- 支持序列化的接口
class (Component a) => SerializableComponent a where
  serialize :: a -> String
  deserialize :: String -> Maybe a
```

## 3. 多语言实现

### 3.1 Haskell实现

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- 组件接口
class Component a where
  operation :: a -> String
  add :: a -> a -> Maybe a
  remove :: a -> a -> Maybe a
  getChild :: a -> Int -> Maybe a
  getChildren :: a -> [a]
  isComposite :: a -> Bool

-- 叶子节点
data Leaf = Leaf String deriving (Show, Eq)

instance Component Leaf where
  operation (Leaf name) = "Leaf: " ++ name
  add _ _ = Nothing
  remove _ _ = Nothing
  getChild _ _ = Nothing
  getChildren _ = []
  isComposite _ = False

-- 复合节点
data Composite = Composite String [Composite] deriving (Show, Eq)

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
  getChildren (Composite _ children) = children
  isComposite _ = True

-- 遍历实现
instance Traversable Composite where
  traverse f (Composite name children) = 
    Composite name <$> traverse f children

-- 使用示例
main :: IO ()
main = do
  let leaf1 = Leaf "Leaf1"
  let leaf2 = Leaf "Leaf2"
  let composite = Composite "Root" [leaf1, leaf2]
  
  putStrLn "组合模式示例:"
  putStrLn $ operation composite
  putStrLn $ "子组件数量: " ++ show (length $ getChildren composite)
  
  -- 递归遍历
  let printComponent :: Component a => a -> IO ()
      printComponent c = do
        putStrLn $ operation c
        mapM_ printComponent (getChildren c)
  
  printComponent composite
```

### 3.2 Rust实现

```rust
use std::collections::HashMap;

// 组件trait
trait Component {
    fn operation(&self) -> String;
    fn add(&mut self, component: Box<dyn Component>) -> bool;
    fn remove(&mut self, component: &Box<dyn Component>) -> bool;
    fn get_child(&self, index: usize) -> Option<&Box<dyn Component>>;
    fn get_children(&self) -> Vec<&Box<dyn Component>>;
    fn is_composite(&self) -> bool;
}

// 叶子节点
#[derive(Debug)]
struct Leaf {
    name: String,
}

impl Leaf {
    fn new(name: String) -> Self {
        Leaf { name }
    }
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
    
    fn get_children(&self) -> Vec<&Box<dyn Component>> {
        vec![]
    }
    
    fn is_composite(&self) -> bool {
        false
    }
}

// 复合节点
#[derive(Debug)]
struct Composite {
    name: String,
    children: Vec<Box<dyn Component>>,
}

impl Composite {
    fn new(name: String) -> Self {
        Composite {
            name,
            children: Vec::new(),
        }
    }
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
        if let Some(pos) = self.children.iter().position(|c| {
            std::ptr::eq(c.as_ref(), component.as_ref())
        }) {
            self.children.remove(pos);
            true
        } else {
            false
        }
    }
    
    fn get_child(&self, index: usize) -> Option<&Box<dyn Component>> {
        self.children.get(index)
    }
    
    fn get_children(&self) -> Vec<&Box<dyn Component>> {
        self.children.iter().collect()
    }
    
    fn is_composite(&self) -> bool {
        true
    }
}

// 遍历器
struct ComponentIterator<'a> {
    stack: Vec<&'a Box<dyn Component>>,
}

impl<'a> ComponentIterator<'a> {
    fn new(root: &'a Box<dyn Component>) -> Self {
        ComponentIterator {
            stack: vec![root],
        }
    }
}

impl<'a> Iterator for ComponentIterator<'a> {
    type Item = &'a Box<dyn Component>;
    
    fn next(&mut self) -> Option<Self::Item> {
        self.stack.pop().map(|component| {
            if component.is_composite() {
                for child in component.get_children().into_iter().rev() {
                    self.stack.push(child);
                }
            }
            component
        })
    }
}

// 使用示例
fn main() {
    let mut root = Box::new(Composite::new("Root".to_string()));
    let leaf1 = Box::new(Leaf::new("Leaf1".to_string()));
    let leaf2 = Box::new(Leaf::new("Leaf2".to_string()));
    
    root.add(leaf1);
    root.add(leaf2);
    
    println!("组合模式示例:");
    println!("{}", root.operation());
    
    // 遍历所有组件
    for component in ComponentIterator::new(&root) {
        println!("{}", component.operation());
    }
}
```

### 3.3 Lean实现

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

-- 移除子组件
def remove : Component → Component → Component
  | Component.Composite name children, target => 
    Component.Composite name (children.filter (· ≠ target))
  | leaf, _ => leaf

-- 获取子组件
def getChildren : Component → List Component
  | Component.Leaf _ => []
  | Component.Composite _ children => children

-- 检查是否为复合组件
def isComposite : Component → Bool
  | Component.Leaf _ => false
  | Component.Composite _ _ => true

-- 遍历函数
def traverse (f : Component → α) : Component → List α
  | Component.Leaf _ => [f (Component.Leaf "")]
  | Component.Composite _ children => 
    f (Component.Composite "" []) :: (children.bind (traverse f))

-- 组合模式性质定理
theorem composite_operation_preserved :
  ∀ c1 c2 : Component, 
  operation (add c1 c2) = operation c1 :=
  by simp [operation, add]

-- 使用示例
def main : IO Unit := do
  let leaf1 := Component.Leaf "Leaf1"
  let leaf2 := Component.Leaf "Leaf2"
  let composite := Component.Composite "Root" [leaf1, leaf2]
  
  IO.println s!"组合模式示例: {operation composite}"
  IO.println s!"子组件数量: {composite.getChildren.length}"
```

## 4. 工程实践

### 4.1 设计考虑

- **接口一致性**: 确保叶子节点和复合节点实现相同的接口
- **类型安全**: 在编译时检查类型约束
- **内存管理**: 合理管理组件树的内存分配和释放
- **性能优化**: 避免不必要的对象创建和复制

### 4.2 实现模式

```haskell
-- 安全类型实现
data SafeComponent where
  SafeLeaf :: String -> SafeComponent
  SafeComposite :: String -> [SafeComponent] -> SafeComponent

-- 带缓存的实现
data CachedComponent = CachedComponent {
  component :: Component,
  cache :: Map String String
}
```

### 4.3 错误处理

```haskell
-- 错误类型
data ComponentError = 
  InvalidOperation String
  | ComponentNotFound String
  | CircularReference String

-- 安全操作
safeAdd :: Component -> Component -> Either ComponentError Component
safeAdd parent child = 
  if hasCircularReference parent child
  then Left $ CircularReference "检测到循环引用"
  else Right $ add parent child
```

## 5. 性能优化

### 5.1 缓存策略

- **操作结果缓存**: 缓存频繁调用的操作结果
- **遍历路径缓存**: 缓存常用的遍历路径
- **内存池**: 使用对象池减少内存分配开销

### 5.2 延迟加载

```haskell
-- 延迟加载组件
data LazyComponent = LazyComponent {
  name :: String,
  loader :: IO Component,
  cached :: Maybe Component
}

loadComponent :: LazyComponent -> IO Component
loadComponent (LazyComponent _ loader (Just cached)) = return cached
loadComponent (LazyComponent _ loader Nothing) = loader
```

### 5.3 索引优化

```haskell
-- 带索引的复合组件
data IndexedComposite = IndexedComposite {
  name :: String,
  children :: Map String Component,
  index :: Map String Int
}
```

## 6. 应用场景

### 6.1 文件系统

```haskell
-- 文件系统组件
data FileSystemComponent where
  File :: String -> Int -> FileSystemComponent  -- 文件名和大小
  Directory :: String -> [FileSystemComponent] -> FileSystemComponent

instance Component FileSystemComponent where
  operation (File name size) = "File: " ++ name ++ " (" ++ show size ++ " bytes)"
  operation (Directory name _) = "Directory: " ++ name
  -- ... 其他实现
```

### 6.2 GUI组件树

```haskell
-- GUI组件
data GUIComponent where
  Button :: String -> GUIComponent
  Panel :: String -> [GUIComponent] -> GUIComponent
  Window :: String -> [GUIComponent] -> GUIComponent

instance Component GUIComponent where
  operation (Button text) = "Button: " ++ text
  operation (Panel title _) = "Panel: " ++ title
  operation (Window title _) = "Window: " ++ title
  -- ... 其他实现
```

### 6.3 组织架构

```haskell
-- 组织架构组件
data OrganizationComponent where
  Employee :: String -> String -> OrganizationComponent  -- 姓名和职位
  Department :: String -> [OrganizationComponent] -> OrganizationComponent

instance Component OrganizationComponent where
  operation (Employee name position) = "Employee: " ++ name ++ " (" ++ position ++ ")"
  operation (Department name _) = "Department: " ++ name
  -- ... 其他实现
```

### 6.4 菜单系统

```haskell
-- 菜单组件
data MenuComponent where
  MenuItem :: String -> IO () -> MenuComponent  -- 菜单项和动作
  SubMenu :: String -> [MenuComponent] -> MenuComponent

instance Component MenuComponent where
  operation (MenuItem text _) = "MenuItem: " ++ text
  operation (SubMenu title _) = "SubMenu: " ++ title
  -- ... 其他实现
```

## 7. 最佳实践

### 7.1 设计原则

- **保持接口一致**: 确保叶子节点和复合节点实现相同的接口
- **避免深层递归**: 限制组件树的深度，避免栈溢出
- **考虑内存使用**: 合理管理组件树的内存占用
- **实现访问者模式**: 结合访问者模式实现复杂的遍历操作

### 7.2 实现建议

```haskell
-- 类型安全的组件构建器
class ComponentBuilder a where
  buildLeaf :: String -> a
  buildComposite :: String -> [a] -> a
  validate :: a -> Bool

-- 不可变组件
data ImmutableComponent = ImmutableComponent {
  name :: String,
  children :: [ImmutableComponent],
  metadata :: Map String String
}

-- 线程安全组件
data ThreadSafeComponent = ThreadSafeComponent {
  component :: MVar Component,
  lock :: MVar ()
}
```

### 7.3 测试策略

```haskell
-- 组件测试
testComponent :: Component -> Bool
testComponent component = 
  let children = getChildren component
      childTests = map testComponent children
  in all id childTests && isValidComponent component

-- 性能测试
benchmarkComponent :: Component -> IO Double
benchmarkComponent component = do
  start <- getCurrentTime
  replicateM_ 1000 $ operation component
  end <- getCurrentTime
  return $ diffUTCTime end start
```

### 7.4 扩展性考虑

- **插件系统**: 支持动态加载新的组件类型
- **序列化**: 支持组件的序列化和反序列化
- **版本控制**: 支持组件结构的版本管理
- **分布式**: 支持跨网络的组件树操作

## 8. 总结

组合模式是处理树形结构的强大工具，通过统一的接口简化了客户端代码。在实现时需要注意类型安全、性能优化和内存管理。该模式在文件系统、GUI框架、组织架构等场景中都有广泛应用。
