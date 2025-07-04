# 建造者模式 (Builder Pattern)

## 概述
建造者模式是一种创建型设计模式，它允许你分步骤创建复杂对象。建造者模式特别适用于创建具有多个可选参数的对象，或者需要分步骤构建的复杂对象。

## 核心概念

### 1. 基本特征
- **分步构建**: 逐步构建复杂对象
- **链式调用**: 支持方法链式调用
- **参数验证**: 在构建过程中验证参数
- **不可变对象**: 构建完成后对象不可变

### 2. 实现方式
- **传统建造者**: 分步骤构建对象
- **流式接口**: 支持链式调用的建造者
- **类型安全建造者**: 使用类型系统保证构建完整性
- **函数式建造者**: 使用函数式编程风格

## 理论基础

### 1. 基本建造者模式
```rust
// 复杂对象
#[derive(Debug, Clone)]
struct Computer {
    cpu: String,
    memory: String,
    storage: String,
    graphics: Option<String>,
    network: Option<String>,
}

impl Computer {
    fn new() -> Self {
        Self {
            cpu: String::new(),
            memory: String::new(),
            storage: String::new(),
            graphics: None,
            network: None,
        }
    }
    
    fn cpu(&self) -> &str {
        &self.cpu
    }
    
    fn memory(&self) -> &str {
        &self.memory
    }
    
    fn storage(&self) -> &str {
        &self.storage
    }
    
    fn graphics(&self) -> Option<&str> {
        self.graphics.as_deref()
    }
    
    fn network(&self) -> Option<&str> {
        self.network.as_deref()
    }
}

// 建造者
struct ComputerBuilder {
    computer: Computer,
}

impl ComputerBuilder {
    fn new() -> Self {
        Self {
            computer: Computer::new(),
        }
    }
    
    fn cpu(mut self, cpu: String) -> Self {
        self.computer.cpu = cpu;
        self
    }
    
    fn memory(mut self, memory: String) -> Self {
        self.computer.memory = memory;
        self
    }
    
    fn storage(mut self, storage: String) -> Self {
        self.computer.storage = storage;
        self
    }
    
    fn graphics(mut self, graphics: String) -> Self {
        self.computer.graphics = Some(graphics);
        self
    }
    
    fn network(mut self, network: String) -> Self {
        self.computer.network = Some(network);
        self
    }
    
    fn build(self) -> Result<Computer, String> {
        // 验证必需字段
        if self.computer.cpu.is_empty() {
            return Err("CPU is required".to_string());
        }
        if self.computer.memory.is_empty() {
            return Err("Memory is required".to_string());
        }
        if self.computer.storage.is_empty() {
            return Err("Storage is required".to_string());
        }
        
        Ok(self.computer)
    }
}

// 使用示例
fn use_basic_builder() {
    let computer = ComputerBuilder::new()
        .cpu("Intel i7".to_string())
        .memory("16GB DDR4".to_string())
        .storage("512GB SSD".to_string())
        .graphics("NVIDIA RTX 3080".to_string())
        .network("WiFi 6".to_string())
        .build()
        .unwrap();
    
    println!("Computer: {:?}", computer);
}
```

### 2. 流式接口建造者
```rust
// 流式接口建造者
struct FluentComputerBuilder {
    cpu: Option<String>,
    memory: Option<String>,
    storage: Option<String>,
    graphics: Option<String>,
    network: Option<String>,
}

impl FluentComputerBuilder {
    fn new() -> Self {
        Self {
            cpu: None,
            memory: None,
            storage: None,
            graphics: None,
            network: None,
        }
    }
    
    fn cpu(mut self, cpu: String) -> Self {
        self.cpu = Some(cpu);
        self
    }
    
    fn memory(mut self, memory: String) -> Self {
        self.memory = Some(memory);
        self
    }
    
    fn storage(mut self, storage: String) -> Self {
        self.storage = Some(storage);
        self
    }
    
    fn graphics(mut self, graphics: String) -> Self {
        self.graphics = Some(graphics);
        self
    }
    
    fn network(mut self, network: String) -> Self {
        self.network = Some(network);
        self
    }
    
    fn build(self) -> Result<Computer, String> {
        let cpu = self.cpu.ok_or("CPU is required")?;
        let memory = self.memory.ok_or("Memory is required")?;
        let storage = self.storage.ok_or("Storage is required")?;
        
        Ok(Computer {
            cpu,
            memory,
            storage,
            graphics: self.graphics,
            network: self.network,
        })
    }
}

// 使用示例
fn use_fluent_builder() {
    let computer = FluentComputerBuilder::new()
        .cpu("Intel i7".to_string())
        .memory("16GB DDR4".to_string())
        .storage("512GB SSD".to_string())
        .graphics("NVIDIA RTX 3080".to_string())
        .network("WiFi 6".to_string())
        .build()
        .unwrap();
    
    println!("Computer: {:?}", computer);
}
```

### 3. 类型安全建造者
```rust
// 类型安全建造者
struct ComputerBuilderState<CPU, MEMORY, STORAGE> {
    cpu: CPU,
    memory: MEMORY,
    storage: STORAGE,
    graphics: Option<String>,
    network: Option<String>,
}

// 未设置状态
struct Unset;
// 已设置状态
struct Set(String);

// 空建造者
type EmptyBuilder = ComputerBuilderState<Unset, Unset, Unset>;

// CPU已设置
type CpuSetBuilder = ComputerBuilderState<Set, Unset, Unset>;

// CPU和内存已设置
type CpuMemorySetBuilder = ComputerBuilderState<Set, Set, Unset>;

// 完整建造者
type CompleteBuilder = ComputerBuilderState<Set, Set, Set>;

impl ComputerBuilderState<Unset, Unset, Unset> {
    fn new() -> Self {
        Self {
            cpu: Unset,
            memory: Unset,
            storage: Unset,
            graphics: None,
            network: None,
        }
    }
    
    fn cpu(self, cpu: String) -> ComputerBuilderState<Set, Unset, Unset> {
        ComputerBuilderState {
            cpu: Set(cpu),
            memory: self.memory,
            storage: self.storage,
            graphics: self.graphics,
            network: self.network,
        }
    }
}

impl ComputerBuilderState<Set, Unset, Unset> {
    fn memory(self, memory: String) -> ComputerBuilderState<Set, Set, Unset> {
        ComputerBuilderState {
            cpu: self.cpu,
            memory: Set(memory),
            storage: self.storage,
            graphics: self.graphics,
            network: self.network,
        }
    }
}

impl ComputerBuilderState<Set, Set, Unset> {
    fn storage(self, storage: String) -> ComputerBuilderState<Set, Set, Set> {
        ComputerBuilderState {
            cpu: self.cpu,
            memory: self.memory,
            storage: Set(storage),
            graphics: self.graphics,
            network: self.network,
        }
    }
}

impl ComputerBuilderState<Set, Set, Set> {
    fn graphics(mut self, graphics: String) -> Self {
        self.graphics = Some(graphics);
        self
    }
    
    fn network(mut self, network: String) -> Self {
        self.network = Some(network);
        self
    }
    
    fn build(self) -> Computer {
        let Set(cpu) = self.cpu;
        let Set(memory) = self.memory;
        let Set(storage) = self.storage;
        
        Computer {
            cpu,
            memory,
            storage,
            graphics: self.graphics,
            network: self.network,
        }
    }
}

// 使用示例
fn use_type_safe_builder() {
    let computer = ComputerBuilderState::new()
        .cpu("Intel i7".to_string())
        .memory("16GB DDR4".to_string())
        .storage("512GB SSD".to_string())
        .graphics("NVIDIA RTX 3080".to_string())
        .network("WiFi 6".to_string())
        .build();
    
    println!("Computer: {:?}", computer);
}
```

### 4. 函数式建造者
```rust
// 函数式建造者
struct FunctionalComputerBuilder {
    cpu: Option<String>,
    memory: Option<String>,
    storage: Option<String>,
    graphics: Option<String>,
    network: Option<String>,
}

impl FunctionalComputerBuilder {
    fn new() -> Self {
        Self {
            cpu: None,
            memory: None,
            storage: None,
            graphics: None,
            network: None,
        }
    }
    
    fn with_cpu(mut self, cpu: String) -> Self {
        self.cpu = Some(cpu);
        self
    }
    
    fn with_memory(mut self, memory: String) -> Self {
        self.memory = Some(memory);
        self
    }
    
    fn with_storage(mut self, storage: String) -> Self {
        self.storage = Some(storage);
        self
    }
    
    fn with_graphics(mut self, graphics: String) -> Self {
        self.graphics = Some(graphics);
        self
    }
    
    fn with_network(mut self, network: String) -> Self {
        self.network = Some(network);
        self
    }
    
    fn build(self) -> Result<Computer, String> {
        let cpu = self.cpu.ok_or("CPU is required")?;
        let memory = self.memory.ok_or("Memory is required")?;
        let storage = self.storage.ok_or("Storage is required")?;
        
        Ok(Computer {
            cpu,
            memory,
            storage,
            graphics: self.graphics,
            network: self.network,
        })
    }
}

// 使用示例
fn use_functional_builder() {
    let computer = FunctionalComputerBuilder::new()
        .with_cpu("Intel i7".to_string())
        .with_memory("16GB DDR4".to_string())
        .with_storage("512GB SSD".to_string())
        .with_graphics("NVIDIA RTX 3080".to_string())
        .with_network("WiFi 6".to_string())
        .build()
        .unwrap();
    
    println!("Computer: {:?}", computer);
}
```

## Haskell实现示例

```haskell
-- 复杂对象
data Computer = Computer
    { cpu :: String
    , memory :: String
    , storage :: String
    , graphics :: Maybe String
    , network :: Maybe String
    } deriving (Show, Eq)

-- 基本建造者
data ComputerBuilder = ComputerBuilder
    { builderCpu :: String
    , builderMemory :: String
    , builderStorage :: String
    , builderGraphics :: Maybe String
    , builderNetwork :: Maybe String
    }

newComputerBuilder :: ComputerBuilder
newComputerBuilder = ComputerBuilder
    { builderCpu = ""
    , builderMemory = ""
    , builderStorage = ""
    , builderGraphics = Nothing
    , builderNetwork = Nothing
    }

setCpu :: String -> ComputerBuilder -> ComputerBuilder
setCpu cpu builder = builder { builderCpu = cpu }

setMemory :: String -> ComputerBuilder -> ComputerBuilder
setMemory memory builder = builder { builderMemory = memory }

setStorage :: String -> ComputerBuilder -> ComputerBuilder
setStorage storage builder = builder { builderStorage = storage }

setGraphics :: String -> ComputerBuilder -> ComputerBuilder
setGraphics graphics builder = builder { builderGraphics = Just graphics }

setNetwork :: String -> ComputerBuilder -> ComputerBuilder
setNetwork network builder = builder { builderNetwork = Just network }

build :: ComputerBuilder -> Either String Computer
build builder
    | null (builderCpu builder) = Left "CPU is required"
    | null (builderMemory builder) = Left "Memory is required"
    | null (builderStorage builder) = Left "Storage is required"
    | otherwise = Right Computer
        { cpu = builderCpu builder
        , memory = builderMemory builder
        , storage = builderStorage builder
        , graphics = builderGraphics builder
        , network = builderNetwork builder
        }

-- 流式接口建造者
data FluentComputerBuilder = FluentComputerBuilder
    { fluentCpu :: Maybe String
    , fluentMemory :: Maybe String
    , fluentStorage :: Maybe String
    , fluentGraphics :: Maybe String
    , fluentNetwork :: Maybe String
    }

newFluentBuilder :: FluentComputerBuilder
newFluentBuilder = FluentComputerBuilder
    { fluentCpu = Nothing
    , fluentMemory = Nothing
    , fluentStorage = Nothing
    , fluentGraphics = Nothing
    , fluentNetwork = Nothing
    }

cpu :: String -> FluentComputerBuilder -> FluentComputerBuilder
cpu cpu builder = builder { fluentCpu = Just cpu }

memory :: String -> FluentComputerBuilder -> FluentComputerBuilder
memory memory builder = builder { fluentMemory = Just memory }

storage :: String -> FluentComputerBuilder -> FluentComputerBuilder
storage storage builder = builder { fluentStorage = Just storage }

graphics :: String -> FluentComputerBuilder -> FluentComputerBuilder
graphics graphics builder = builder { fluentGraphics = Just graphics }

network :: String -> FluentComputerBuilder -> FluentComputerBuilder
network network builder = builder { fluentNetwork = Just network }

buildFluent :: FluentComputerBuilder -> Either String Computer
buildFluent builder = do
    cpu <- maybe (Left "CPU is required") Right (fluentCpu builder)
    memory <- maybe (Left "Memory is required") Right (fluentMemory builder)
    storage <- maybe (Left "Storage is required") Right (fluentStorage builder)
    return Computer
        { cpu = cpu
        , memory = memory
        , storage = storage
        , graphics = fluentGraphics builder
        , network = fluentNetwork builder
        }

-- 类型安全建造者
data BuilderState = Unset | Set String

data TypeSafeComputerBuilder cpu memory storage = TypeSafeComputerBuilder
    { tsCpu :: cpu
    , tsMemory :: memory
    , tsStorage :: storage
    , tsGraphics :: Maybe String
    , tsNetwork :: Maybe String
    }

newTypeSafeBuilder :: TypeSafeComputerBuilder Unset Unset Unset
newTypeSafeBuilder = TypeSafeComputerBuilder
    { tsCpu = Unset
    , tsMemory = Unset
    , tsStorage = Unset
    , tsGraphics = Nothing
    , tsNetwork = Nothing
    }

setTypeSafeCpu :: String -> TypeSafeComputerBuilder Unset memory storage 
                -> TypeSafeComputerBuilder (Set String) memory storage
setTypeSafeCpu cpu builder = builder { tsCpu = Set cpu }

setTypeSafeMemory :: String -> TypeSafeComputerBuilder (Set String) Unset storage 
                  -> TypeSafeComputerBuilder (Set String) (Set String) storage
setTypeSafeMemory memory builder = builder { tsMemory = Set memory }

setTypeSafeStorage :: String -> TypeSafeComputerBuilder (Set String) (Set String) Unset 
                   -> TypeSafeComputerBuilder (Set String) (Set String) (Set String)
setTypeSafeStorage storage builder = builder { tsStorage = Set storage }

setTypeSafeGraphics :: String -> TypeSafeComputerBuilder (Set String) (Set String) (Set String) 
                    -> TypeSafeComputerBuilder (Set String) (Set String) (Set String)
setTypeSafeGraphics graphics builder = builder { tsGraphics = Just graphics }

setTypeSafeNetwork :: String -> TypeSafeComputerBuilder (Set String) (Set String) (Set String) 
                   -> TypeSafeComputerBuilder (Set String) (Set String) (Set String)
setTypeSafeNetwork network builder = builder { tsNetwork = Just network }

buildTypeSafe :: TypeSafeComputerBuilder (Set String) (Set String) (Set String) -> Computer
buildTypeSafe builder = Computer
    { cpu = case tsCpu builder of Set cpu => cpu
    , memory = case tsMemory builder of Set memory => memory
    , storage = case tsStorage builder of Set storage => storage
    , graphics = tsGraphics builder
    , network = tsNetwork builder
    }

-- 使用示例
useBasicBuilder :: IO ()
useBasicBuilder = do
    let builder = newComputerBuilder
    let builder' = setCpu "Intel i7" builder
    let builder'' = setMemory "16GB DDR4" builder'
    let builder''' = setStorage "512GB SSD" builder''
    let builder'''' = setGraphics "NVIDIA RTX 3080" builder'''
    let builder''''' = setNetwork "WiFi 6" builder''''
    case build builder''''' of
        Left err -> putStrLn $ "Error: " ++ err
        Right computer -> print computer

useFluentBuilder :: IO ()
useFluentBuilder = do
    let computer = newFluentBuilder
        & cpu "Intel i7"
        & memory "16GB DDR4"
        & storage "512GB SSD"
        & graphics "NVIDIA RTX 3080"
        & network "WiFi 6"
        & buildFluent
    case computer of
        Left err -> putStrLn $ "Error: " ++ err
        Right comp -> print comp

useTypeSafeBuilder :: IO ()
useTypeSafeBuilder = do
    let computer = newTypeSafeBuilder
        & setTypeSafeCpu "Intel i7"
        & setTypeSafeMemory "16GB DDR4"
        & setTypeSafeStorage "512GB SSD"
        & setTypeSafeGraphics "NVIDIA RTX 3080"
        & setTypeSafeNetwork "WiFi 6"
        & buildTypeSafe
    print computer
```

## Lean实现思路

```lean
-- 复杂对象
structure Computer where
  cpu : String
  memory : String
  storage : String
  graphics : Option String
  network : Option String

-- 基本建造者
structure ComputerBuilder where
  builderCpu : String
  builderMemory : String
  builderStorage : String
  builderGraphics : Option String
  builderNetwork : Option String

def newComputerBuilder : ComputerBuilder :=
  { builderCpu := ""
  , builderMemory := ""
  , builderStorage := ""
  , builderGraphics := none
  , builderNetwork := none
  }

def setCpu (cpu : String) (builder : ComputerBuilder) : ComputerBuilder :=
  { builder with builderCpu := cpu }

def setMemory (memory : String) (builder : ComputerBuilder) : ComputerBuilder :=
  { builder with builderMemory := memory }

def setStorage (storage : String) (builder : ComputerBuilder) : ComputerBuilder :=
  { builder with builderStorage := storage }

def setGraphics (graphics : String) (builder : ComputerBuilder) : ComputerBuilder :=
  { builder with builderGraphics := some graphics }

def setNetwork (network : String) (builder : ComputerBuilder) : ComputerBuilder :=
  { builder with builderNetwork := some network }

def build (builder : ComputerBuilder) : Option Computer :=
  if builder.builderCpu.isEmpty then none
  else if builder.builderMemory.isEmpty then none
  else if builder.builderStorage.isEmpty then none
  else some
    { cpu := builder.builderCpu
    , memory := builder.builderMemory
    , storage := builder.builderStorage
    , graphics := builder.builderGraphics
    , network := builder.builderNetwork
    }

-- 流式接口建造者
structure FluentComputerBuilder where
  fluentCpu : Option String
  fluentMemory : Option String
  fluentStorage : Option String
  fluentGraphics : Option String
  fluentNetwork : Option String

def newFluentBuilder : FluentComputerBuilder :=
  { fluentCpu := none
  , fluentMemory := none
  , fluentStorage := none
  , fluentGraphics := none
  , fluentNetwork := none
  }

def cpu (cpu : String) (builder : FluentComputerBuilder) : FluentComputerBuilder :=
  { builder with fluentCpu := some cpu }

def memory (memory : String) (builder : FluentComputerBuilder) : FluentComputerBuilder :=
  { builder with fluentMemory := some memory }

def storage (storage : String) (builder : FluentComputerBuilder) : FluentComputerBuilder :=
  { builder with fluentStorage := some storage }

def graphics (graphics : String) (builder : FluentComputerBuilder) : FluentComputerBuilder :=
  { builder with fluentGraphics := some graphics }

def network (network : String) (builder : FluentComputerBuilder) : FluentComputerBuilder :=
  { builder with fluentNetwork := some network }

def buildFluent (builder : FluentComputerBuilder) : Option Computer :=
  match builder.fluentCpu, builder.fluentMemory, builder.fluentStorage with
  | some cpu, some memory, some storage => some
    { cpu := cpu
    , memory := memory
    , storage := storage
    , graphics := builder.fluentGraphics
    , network := builder.fluentNetwork
    }
  | _, _, _ => none

-- 类型安全建造者
inductive BuilderState where
  | unset : BuilderState
  | set : String → BuilderState

structure TypeSafeComputerBuilder (cpu memory storage : BuilderState) where
  tsCpu : cpu
  tsMemory : memory
  tsStorage : storage
  tsGraphics : Option String
  tsNetwork : Option String

def newTypeSafeBuilder : TypeSafeComputerBuilder BuilderState.unset BuilderState.unset BuilderState.unset :=
  { tsCpu := BuilderState.unset
  , tsMemory := BuilderState.unset
  , tsStorage := BuilderState.unset
  , tsGraphics := none
  , tsNetwork := none
  }

def setTypeSafeCpu (cpu : String) 
  (builder : TypeSafeComputerBuilder BuilderState.unset memory storage) :
  TypeSafeComputerBuilder (BuilderState.set cpu) memory storage :=
  { builder with tsCpu := BuilderState.set cpu }

def setTypeSafeMemory (memory : String)
  (builder : TypeSafeComputerBuilder (BuilderState.set cpu) BuilderState.unset storage) :
  TypeSafeComputerBuilder (BuilderState.set cpu) (BuilderState.set memory) storage :=
  { builder with tsMemory := BuilderState.set memory }

def setTypeSafeStorage (storage : String)
  (builder : TypeSafeComputerBuilder (BuilderState.set cpu) (BuilderState.set memory) BuilderState.unset) :
  TypeSafeComputerBuilder (BuilderState.set cpu) (BuilderState.set memory) (BuilderState.set storage) :=
  { builder with tsStorage := BuilderState.set storage }

def buildTypeSafe 
  (builder : TypeSafeComputerBuilder (BuilderState.set cpu) (BuilderState.set memory) (BuilderState.set storage)) :
  Computer :=
  { cpu := match builder.tsCpu with | BuilderState.set cpu => cpu
  , memory := match builder.tsMemory with | BuilderState.set memory => memory
  , storage := match builder.tsStorage with | BuilderState.set storage => storage
  , graphics := builder.tsGraphics
  , network := builder.tsNetwork
  }
```

## 应用场景

### 1. 配置对象
- **应用配置**: 构建复杂的应用配置
- **数据库配置**: 构建数据库连接配置
- **网络配置**: 构建网络连接配置

### 2. 复杂对象
- **UI组件**: 构建复杂的UI组件
- **文档对象**: 构建复杂的文档结构
- **游戏对象**: 构建游戏中的复杂对象

### 3. 数据转换
- **查询构建器**: 构建数据库查询
- **API请求**: 构建HTTP请求
- **序列化**: 构建序列化对象

### 4. 测试对象
- **测试数据**: 构建测试用的复杂对象
- **模拟对象**: 构建模拟对象
- **测试配置**: 构建测试配置

## 最佳实践

### 1. 设计原则
- 使用链式调用
- 提供合理的默认值
- 进行参数验证

### 2. 错误处理
- 提供清晰的错误信息
- 使用Result类型
- 处理验证失败

### 3. 性能考虑
- 避免不必要的分配
- 使用引用传递
- 考虑内存使用

### 4. 可读性
- 使用描述性的方法名
- 提供清晰的文档
- 遵循命名约定

## 性能考虑

### 1. 对象创建
- 减少临时对象
- 使用移动语义
- 优化内存分配

### 2. 方法调用
- 内联简单方法
- 减少函数调用开销
- 使用常量折叠

### 3. 类型检查
- 编译时类型检查
- 减少运行时检查
- 使用泛型优化

## 总结

建造者模式是创建复杂对象的重要设计模式，通过分步骤构建和链式调用，提供了灵活且易用的对象创建方式。合理使用建造者模式可以简化复杂对象的创建过程，提高代码的可读性和可维护性。 