# 010 访问者模式 (Visitor Pattern)

## 1. 理论基础

### 1.1 模式定义

访问者模式是一种行为型设计模式，表示一个作用于某对象结构中的各元素的操作。它使你可以在不改变各元素的类的前提下定义作用于这些元素的新操作。

### 1.2 核心概念

- **Visitor（访问者）**: 定义访问元素的操作接口
- **ConcreteVisitor（具体访问者）**: 实现访问者接口的具体操作
- **Element（元素）**: 定义接受访问者的接口
- **ConcreteElement（具体元素）**: 实现元素接口的具体类
- **ObjectStructure（对象结构）**: 能够枚举它的元素，可以提供一个高层的接口以允许访问者访问它的元素

### 1.3 设计原则

- **开闭原则**: 对扩展开放，对修改封闭
- **单一职责**: 每个访问者只负责一种操作
- **依赖倒置**: 依赖于抽象而非具体实现

### 1.4 优缺点分析

**优点:**

- 易于增加新的操作
- 将相关操作集中在一个访问者对象中
- 访问者可以跨过类的层次结构
- 符合开闭原则

**缺点:**

- 破坏封装性
- 增加系统复杂性
- 难以维护元素类的层次结构
- 可能违反里氏替换原则

## 2. 接口设计

### 2.1 核心接口

```haskell
-- Haskell接口设计
class Element a where
  accept :: a -> Visitor -> IO ()

class Visitor a where
  visitElementA :: a -> ElementA -> IO ()
  visitElementB :: a -> ElementB -> IO ()
  visitElementC :: a -> ElementC -> IO ()

-- 具体元素
data ElementA = ElementA deriving Show
data ElementB = ElementB deriving Show
data ElementC = ElementC deriving Show
```

### 2.2 扩展接口

```haskell
-- 支持参数化的访问者
class (Visitor a) => ParameterizedVisitor a where
  setParameters :: a -> [String] -> a
  getParameters :: a -> [String]
  
-- 支持条件访问的访问者
class (Visitor a) => ConditionalVisitor a where
  shouldVisit :: a -> Element -> Bool
  getVisitCount :: a -> Int
```

## 3. 多语言实现

### 3.1 Haskell实现

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- 访问者接口
class Visitor a where
  visitElementA :: a -> ElementA -> IO ()
  visitElementB :: a -> ElementB -> IO ()
  visitElementC :: a -> ElementC -> IO ()

-- 元素接口
class Element a where
  accept :: a -> Visitor -> IO ()

-- 具体元素
data ElementA = ElementA {
  name :: String,
  value :: Int
} deriving Show

data ElementB = ElementB {
  name :: String,
  data :: [String]
} deriving Show

data ElementC = ElementC {
  name :: String,
  config :: Map String String
} deriving Show

instance Element ElementA where
  accept ElementA visitor = visitElementA visitor ElementA

instance Element ElementB where
  accept ElementB visitor = visitElementB visitor ElementB

instance Element ElementC where
  accept ElementC visitor = visitElementC visitor ElementC

-- 具体访问者
data ConcreteVisitor = ConcreteVisitor {
  visitorName :: String,
  visitCount :: IORef Int
} deriving Show

instance Visitor ConcreteVisitor where
  visitElementA visitor ElementA = do
    modifyIORef (visitCount visitor) (+1)
    count <- readIORef (visitCount visitor)
    putStrLn $ visitorName visitor ++ " visits ElementA: " ++ name ElementA ++ " (count: " ++ show count ++ ")"
  
  visitElementB visitor ElementB = do
    modifyIORef (visitCount visitor) (+1)
    count <- readIORef (visitCount visitor)
    putStrLn $ visitorName visitor ++ " visits ElementB: " ++ name ElementB ++ " (count: " ++ show count ++ ")"
  
  visitElementC visitor ElementC = do
    modifyIORef (visitCount visitor) (+1)
    count <- readIORef (visitCount visitor)
    putStrLn $ visitorName visitor ++ " visits ElementC: " ++ name ElementC ++ " (count: " ++ show count ++ ")"

-- 参数化访问者
data ParameterizedVisitor = ParameterizedVisitor {
  baseVisitor :: ConcreteVisitor,
  parameters :: [String]
} deriving Show

instance Visitor ParameterizedVisitor where
  visitElementA visitor ElementA = do
    putStrLn $ "Parameterized: " ++ show (parameters visitor)
    visitElementA (baseVisitor visitor) ElementA
  
  visitElementB visitor ElementB = do
    putStrLn $ "Parameterized: " ++ show (parameters visitor)
    visitElementB (baseVisitor visitor) ElementB
  
  visitElementC visitor ElementC = do
    putStrLn $ "Parameterized: " ++ show (parameters visitor)
    visitElementC (baseVisitor visitor) ElementC

-- 条件访问者
data ConditionalVisitor = ConditionalVisitor {
  baseVisitor :: ConcreteVisitor,
  conditions :: Map String Bool
} deriving Show

instance Visitor ConditionalVisitor where
  visitElementA visitor ElementA = 
    if Map.findWithDefault True (name ElementA) (conditions visitor)
    then visitElementA (baseVisitor visitor) ElementA
    else putStrLn $ "Skipping ElementA: " ++ name ElementA
  
  visitElementB visitor ElementB = 
    if Map.findWithDefault True (name ElementB) (conditions visitor)
    then visitElementB (baseVisitor visitor) ElementB
    else putStrLn $ "Skipping ElementB: " ++ name ElementB
  
  visitElementC visitor ElementC = 
    if Map.findWithDefault True (name ElementC) (conditions visitor)
    then visitElementC (baseVisitor visitor) ElementC
    else putStrLn $ "Skipping ElementC: " ++ name ElementC

-- 对象结构
data ObjectStructure = ObjectStructure {
  elements :: [Element],
  metadata :: Map String String
} deriving Show

-- 对象结构操作
addElement :: ObjectStructure -> Element -> ObjectStructure
addElement structure element = 
  structure { elements = element : elements structure }

acceptAll :: ObjectStructure -> Visitor -> IO ()
acceptAll structure visitor = 
  mapM_ (\element -> accept element visitor) (elements structure)

-- 使用示例
main :: IO ()
main = do
  -- 创建访问者
  countRef <- newIORef 0
  let visitor = ConcreteVisitor "MainVisitor" countRef
  
  -- 创建元素
  let elementA = ElementA "ElementA" 100
  let elementB = ElementB "ElementB" ["data1", "data2"]
  let elementC = ElementC "ElementC" (Map.fromList [("key1", "value1")])
  
  -- 创建对象结构
  let structure = ObjectStructure [] Map.empty
  let structure' = addElement structure elementA
  let structure'' = addElement structure' elementB
  let structure''' = addElement structure'' elementC
  
  putStrLn "访问者模式示例:"
  
  putStrLn "\n基本访问者执行:"
  acceptAll structure''' visitor
  
  -- 参数化访问者
  let paramVisitor = ParameterizedVisitor visitor ["param1", "param2"]
  putStrLn "\n参数化访问者执行:"
  acceptAll structure''' paramVisitor
  
  -- 条件访问者
  let conditionVisitor = ConditionalVisitor visitor (Map.fromList [("ElementA", True), ("ElementB", False), ("ElementC", True)])
  putStrLn "\n条件访问者执行:"
  acceptAll structure''' conditionVisitor
```

### 3.2 Rust实现

```rust
use std::collections::HashMap;
use std::cell::RefCell;
use std::rc::Rc;

// 访问者trait
trait Visitor {
    fn visit_element_a(&self, element: &ElementA);
    fn visit_element_b(&self, element: &ElementB);
    fn visit_element_c(&self, element: &ElementC);
}

// 元素trait
trait Element {
    fn accept(&self, visitor: &dyn Visitor);
}

// 具体元素A
#[derive(Debug)]
struct ElementA {
    name: String,
    value: i32,
}

impl Element for ElementA {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_element_a(self);
    }
}

// 具体元素B
#[derive(Debug)]
struct ElementB {
    name: String,
    data: Vec<String>,
}

impl Element for ElementB {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_element_b(self);
    }
}

// 具体元素C
#[derive(Debug)]
struct ElementC {
    name: String,
    config: HashMap<String, String>,
}

impl Element for ElementC {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_element_c(self);
    }
}

// 具体访问者
#[derive(Debug)]
struct ConcreteVisitor {
    visitor_name: String,
    visit_count: Rc<RefCell<i32>>,
}

impl ConcreteVisitor {
    fn new(name: String) -> Self {
        ConcreteVisitor {
            visitor_name,
            visit_count: Rc::new(RefCell::new(0)),
        }
    }
}

impl Visitor for ConcreteVisitor {
    fn visit_element_a(&self, element: &ElementA) {
        *self.visit_count.borrow_mut() += 1;
        println!(
            "{} visits ElementA: {} (count: {})",
            self.visitor_name,
            element.name,
            *self.visit_count.borrow()
        );
    }
    
    fn visit_element_b(&self, element: &ElementB) {
        *self.visit_count.borrow_mut() += 1;
        println!(
            "{} visits ElementB: {} (count: {})",
            self.visitor_name,
            element.name,
            *self.visit_count.borrow()
        );
    }
    
    fn visit_element_c(&self, element: &ElementC) {
        *self.visit_count.borrow_mut() += 1;
        println!(
            "{} visits ElementC: {} (count: {})",
            self.visitor_name,
            element.name,
            *self.visit_count.borrow()
        );
    }
}

// 参数化访问者
#[derive(Debug)]
struct ParameterizedVisitor {
    base_visitor: ConcreteVisitor,
    parameters: Vec<String>,
}

impl ParameterizedVisitor {
    fn new(base_visitor: ConcreteVisitor, parameters: Vec<String>) -> Self {
        ParameterizedVisitor {
            base_visitor,
            parameters,
        }
    }
}

impl Visitor for ParameterizedVisitor {
    fn visit_element_a(&self, element: &ElementA) {
        println!("Parameterized: {:?}", self.parameters);
        self.base_visitor.visit_element_a(element);
    }
    
    fn visit_element_b(&self, element: &ElementB) {
        println!("Parameterized: {:?}", self.parameters);
        self.base_visitor.visit_element_b(element);
    }
    
    fn visit_element_c(&self, element: &ElementC) {
        println!("Parameterized: {:?}", self.parameters);
        self.base_visitor.visit_element_c(element);
    }
}

// 条件访问者
#[derive(Debug)]
struct ConditionalVisitor {
    base_visitor: ConcreteVisitor,
    conditions: HashMap<String, bool>,
}

impl ConditionalVisitor {
    fn new(base_visitor: ConcreteVisitor, conditions: HashMap<String, bool>) -> Self {
        ConditionalVisitor {
            base_visitor,
            conditions,
        }
    }
}

impl Visitor for ConditionalVisitor {
    fn visit_element_a(&self, element: &ElementA) {
        if *self.conditions.get(&element.name).unwrap_or(&true) {
            self.base_visitor.visit_element_a(element);
        } else {
            println!("Skipping ElementA: {}", element.name);
        }
    }
    
    fn visit_element_b(&self, element: &ElementB) {
        if *self.conditions.get(&element.name).unwrap_or(&true) {
            self.base_visitor.visit_element_b(element);
        } else {
            println!("Skipping ElementB: {}", element.name);
        }
    }
    
    fn visit_element_c(&self, element: &ElementC) {
        if *self.conditions.get(&element.name).unwrap_or(&true) {
            self.base_visitor.visit_element_c(element);
        } else {
            println!("Skipping ElementC: {}", element.name);
        }
    }
}

// 对象结构
#[derive(Debug)]
struct ObjectStructure {
    elements: Vec<Box<dyn Element>>,
    metadata: HashMap<String, String>,
}

impl ObjectStructure {
    fn new() -> Self {
        ObjectStructure {
            elements: Vec::new(),
            metadata: HashMap::new(),
        }
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

// 使用示例
fn main() {
    // 创建访问者
    let visitor = ConcreteVisitor::new("MainVisitor".to_string());
    
    // 创建元素
    let element_a = ElementA {
        name: "ElementA".to_string(),
        value: 100,
    };
    let element_b = ElementB {
        name: "ElementB".to_string(),
        data: vec!["data1".to_string(), "data2".to_string()],
    };
    let element_c = ElementC {
        name: "ElementC".to_string(),
        config: {
            let mut config = HashMap::new();
            config.insert("key1".to_string(), "value1".to_string());
            config
        },
    };
    
    // 创建对象结构
    let mut structure = ObjectStructure::new();
    structure.add_element(Box::new(element_a));
    structure.add_element(Box::new(element_b));
    structure.add_element(Box::new(element_c));
    
    println!("访问者模式示例:");
    
    println!("\n基本访问者执行:");
    structure.accept_all(&visitor);
    
    // 参数化访问者
    let param_visitor = ParameterizedVisitor::new(
        visitor,
        vec!["param1".to_string(), "param2".to_string()],
    );
    println!("\n参数化访问者执行:");
    structure.accept_all(&param_visitor);
    
    // 条件访问者
    let mut conditions = HashMap::new();
    conditions.insert("ElementA".to_string(), true);
    conditions.insert("ElementB".to_string(), false);
    conditions.insert("ElementC".to_string(), true);
    let condition_visitor = ConditionalVisitor::new(visitor, conditions);
    println!("\n条件访问者执行:");
    structure.accept_all(&condition_visitor);
}
```

### 3.3 Lean实现

```lean
-- 访问者类型
inductive Visitor where
  | ConcreteVisitor : String → Nat → Visitor
  | ParameterizedVisitor : Visitor → List String → Visitor
  | ConditionalVisitor : Visitor → List (String × Bool) → Visitor

-- 元素类型
inductive Element where
  | ElementA : String → Nat → Element
  | ElementB : String → List String → Element
  | ElementC : String → List (String × String) → Element

-- 访问函数
def accept : Element → Visitor → IO Unit
  | Element.ElementA name value, Visitor.ConcreteVisitor visitorName count => 
    IO.println (s!"{visitorName} visits ElementA: {name} (count: {count + 1})")
  | Element.ElementB name data, Visitor.ConcreteVisitor visitorName count => 
    IO.println (s!"{visitorName} visits ElementB: {name} (count: {count + 1})")
  | Element.ElementC name config, Visitor.ConcreteVisitor visitorName count => 
    IO.println (s!"{visitorName} visits ElementC: {name} (count: {count + 1})")
  
  | element, Visitor.ParameterizedVisitor baseVisitor params => do
    IO.println (s!"Parameterized: {params}")
    accept element baseVisitor
  
  | element, Visitor.ConditionalVisitor baseVisitor conditions => 
    let elementName := match element with
      | Element.ElementA name _ => name
      | Element.ElementB name _ => name
      | Element.ElementC name _ => name
    let shouldVisit := conditions.any (λ (name, enabled) => name = elementName ∧ enabled)
    if shouldVisit
    then accept element baseVisitor
    else IO.println (s!"Skipping {elementName}")

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

-- 使用示例
def main : IO Unit := do
  let elementA := Element.ElementA "ElementA" 100
  let elementB := Element.ElementB "ElementB" ["data1", "data2"]
  let elementC := Element.ElementC "ElementC" [("key1", "value1")]
  
  let structure := [elementA, elementB, elementC]
  
  IO.println "访问者模式示例:"
  
  let visitor := Visitor.ConcreteVisitor "MainVisitor" 0
  IO.println "\n基本访问者执行:"
  acceptAll structure visitor
  
  let paramVisitor := Visitor.ParameterizedVisitor visitor ["param1", "param2"]
  IO.println "\n参数化访问者执行:"
  acceptAll structure paramVisitor
  
  let conditionVisitor := Visitor.ConditionalVisitor visitor [("ElementA", true), ("ElementB", false), ("ElementC", true)]
  IO.println "\n条件访问者执行:"
  acceptAll structure conditionVisitor
```

## 4. 工程实践

### 4.1 设计考虑

- **操作分离**: 将操作与数据结构分离
- **扩展性**: 支持新的操作而不修改数据结构
- **性能优化**: 避免频繁的虚函数调用
- **错误处理**: 处理访问者执行失败的情况

### 4.2 实现模式

```haskell
-- 带缓存的访问者
data CachedVisitor a = CachedVisitor {
  visitor :: a,
  cache :: MVar (Map String String)
}

-- 异步访问者
data AsyncVisitor = AsyncVisitor {
  visitor :: Visitor,
  executor :: ThreadPool
}

-- 带监控的访问者
data MonitoredVisitor a = MonitoredVisitor {
  visitor :: a,
  metrics :: MVar VisitorMetrics
}
```

### 4.3 错误处理

```haskell
-- 错误类型
data VisitorError = 
  VisitorExecutionFailed String
  | InvalidElement String
  | ElementNotFound String

-- 安全访问
safeAccept :: Element a => a -> Visitor -> IO (Either VisitorError ())
safeAccept element visitor = 
  try (accept element visitor) >>= \case
    Left e -> return $ Left $ VisitorExecutionFailed (show e)
    Right result -> return $ Right result
```

## 5. 性能优化

### 5.1 缓存策略

- **访问结果缓存**: 缓存相同元素的访问结果
- **访问者对象缓存**: 缓存访问者对象避免重复创建
- **性能指标缓存**: 缓存访问者的性能指标

### 5.2 访问优化

```haskell
-- 优化的访问者
data OptimizedVisitor a = OptimizedVisitor {
  visitor :: a,
  optimizations :: Map String String
}

-- 并行访问
data ParallelVisitor = ParallelVisitor {
  visitors :: [Visitor],
  executor :: ThreadPool
}

executeParallel :: ParallelVisitor -> ObjectStructure -> IO [()]
executeParallel visitor structure = 
  mapConcurrently (\v -> acceptAll structure v) (visitors visitor)
```

### 5.3 访问组合

```haskell
-- 组合访问者
data CompositeVisitor = CompositeVisitor {
  visitors :: [Visitor],
  composition :: () -> () -> ()
}

executeComposite :: CompositeVisitor -> ObjectStructure -> ()
executeComposite composite structure = 
  foldr (composition composite) () (map (\v -> acceptAll structure v) (visitors composite))
```

## 6. 应用场景

### 6.1 编译器实现

```haskell
-- 抽象语法树访问者
data ASTVisitor = ASTVisitor {
  visitExpression :: Expression -> IO (),
  visitStatement :: Statement -> IO (),
  visitDeclaration :: Declaration -> IO ()
}

-- 语法树元素
data Expression = 
  LiteralExpr Literal
  | BinaryExpr Expression Operator Expression
  | FunctionCallExpr String [Expression]

data Statement = 
  ExpressionStmt Expression
  | IfStmt Expression Statement Statement
  | WhileStmt Expression Statement

-- 编译器访问者
data CompilerVisitor = CompilerVisitor {
  astVisitor :: ASTVisitor,
  codeGenerator :: CodeGenerator,
  symbolTable :: SymbolTable
}

-- 编译访问
compileAST :: CompilerVisitor -> AST -> IO ByteCode
compileAST visitor ast = do
  -- 1. 语义分析
  semanticAnalysis visitor ast
  -- 2. 代码生成
  generateCode visitor ast
  -- 3. 优化
  optimizeCode visitor ast
  return $ finalizeCode visitor ast
```

### 6.2 序列化处理

```haskell
-- 序列化访问者
data SerializationVisitor = SerializationVisitor {
  format :: SerializationFormat,
  buffer :: SerializationBuffer
}

-- 序列化元素
data SerializableElement = 
  StringElement String
  | NumberElement Double
  | ObjectElement [(String, SerializableElement)]
  | ArrayElement [SerializableElement]

-- 序列化访问
serializeElement :: SerializationVisitor -> SerializableElement -> IO ByteString
serializeElement visitor element = do
  -- 1. 开始序列化
  beginSerialization visitor
  -- 2. 访问元素
  accept element visitor
  -- 3. 结束序列化
  endSerialization visitor
  return $ getSerializedData visitor
```

### 6.3 文档处理

```haskell
-- 文档访问者
data DocumentVisitor = DocumentVisitor {
  visitParagraph :: Paragraph -> IO (),
  visitHeading :: Heading -> IO (),
  visitList :: List -> IO (),
  visitTable :: Table -> IO ()
}

-- 文档元素
data DocumentElement = 
  ParagraphElement Paragraph
  | HeadingElement Heading
  | ListElement List
  | TableElement Table

-- 文档处理访问者
data DocumentProcessor = DocumentProcessor {
  documentVisitor :: DocumentVisitor,
  formatter :: DocumentFormatter,
  renderer :: DocumentRenderer
}

-- 处理文档
processDocument :: DocumentProcessor -> Document -> IO ProcessedDocument
processDocument processor document = do
  -- 1. 解析文档
  parsedDoc <- parseDocument document
  -- 2. 访问元素
  acceptAll parsedDoc (documentVisitor processor)
  -- 3. 格式化
  formattedDoc <- formatDocument (formatter processor) parsedDoc
  -- 4. 渲染
  renderedDoc <- renderDocument (renderer processor) formattedDoc
  return renderedDoc
```

### 6.4 图形渲染

```haskell
-- 图形访问者
data GraphicsVisitor = GraphicsVisitor {
  visitCircle :: Circle -> IO (),
  visitRectangle :: Rectangle -> IO (),
  visitLine :: Line -> IO (),
  visitText :: Text -> IO ()
}

-- 图形元素
data GraphicsElement = 
  CircleElement Circle
  | RectangleElement Rectangle
  | LineElement Line
  | TextElement Text

-- 渲染访问者
data RendererVisitor = RendererVisitor {
  graphicsVisitor :: GraphicsVisitor,
  canvas :: Canvas,
  context :: GraphicsContext
}

-- 渲染图形
renderGraphics :: RendererVisitor -> GraphicsScene -> IO RenderedImage
renderGraphics renderer scene = do
  -- 1. 设置画布
  setupCanvas (canvas renderer)
  -- 2. 访问图形元素
  acceptAll scene (graphicsVisitor renderer)
  -- 3. 应用变换
  applyTransformations (context renderer)
  -- 4. 生成图像
  generateImage (canvas renderer)
```

## 7. 最佳实践

### 7.1 设计原则

- **保持访问者稳定**: 确保访问者接口的稳定性
- **合理使用访问者**: 适度使用访问者模式避免过度复杂
- **避免过度抽象**: 避免创建过于复杂的访问者层次
- **性能考虑**: 考虑访问者模式的性能影响

### 7.2 实现建议

```haskell
-- 访问者工厂
class VisitorFactory a where
  createVisitor :: String -> Maybe a
  listVisitors :: [String]
  validateVisitor :: a -> Bool

-- 访问者注册表
data VisitorRegistry = VisitorRegistry {
  visitors :: Map String (forall a. Visitor a => a),
  metadata :: Map String String
}

-- 线程安全访问者管理器
data ThreadSafeVisitorManager = ThreadSafeVisitorManager {
  manager :: MVar VisitorManager,
  lock :: MVar ()
}
```

### 7.3 测试策略

```haskell
-- 访问者测试
testVisitor :: Visitor a => a -> ObjectStructure -> Bool
testVisitor visitor structure = 
  let result = acceptAll structure visitor
  in isValidResult result

-- 性能测试
benchmarkVisitor :: Visitor a => a -> ObjectStructure -> IO Double
benchmarkVisitor visitor structure = do
  start <- getCurrentTime
  replicateM_ 1000 $ acceptAll structure visitor
  end <- getCurrentTime
  return $ diffUTCTime end start
```

### 7.4 扩展性考虑

- **插件系统**: 支持动态加载新的访问者类型
- **序列化**: 支持访问者的序列化和反序列化
- **版本控制**: 支持访问者的版本管理
- **分布式**: 支持跨网络的访问者执行

## 8. 总结

访问者模式是分离数据结构与操作的强大工具，通过将操作封装在访问者对象中提供了良好的扩展性。在实现时需要注意访问者接口的稳定性、操作的合理分离和性能优化。该模式在编译器实现、序列化处理、文档处理、图形渲染等场景中都有广泛应用。
