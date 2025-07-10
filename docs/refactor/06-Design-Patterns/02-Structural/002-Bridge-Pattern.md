# 桥接模式 (Bridge Pattern)

## 概述

桥接模式是一种结构型设计模式，它将抽象部分与实现部分分离，使它们都可以独立地变化。桥接模式通过组合关系替代继承关系，降低了抽象和实现这两个可变维度的耦合度。

## 核心概念

### 1. 基本特征

- **抽象与实现分离**: 将抽象和实现解耦
- **组合优于继承**: 使用组合关系而非继承
- **双重维度**: 支持两个独立变化的维度
- **扩展性**: 易于添加新的抽象和实现

### 2. 设计原则

- **开闭原则**: 对扩展开放，对修改关闭
- **单一职责**: 每个类只负责一个职责
- **依赖倒置**: 依赖抽象而非具体实现

## 理论基础

### 1. 基本桥接模式

```rust
// 实现接口
trait Implementor {
    fn operation_impl(&self) -> String;
}

// 具体实现A
struct ConcreteImplementorA;

impl Implementor for ConcreteImplementorA {
    fn operation_impl(&self) -> String {
        String::from("ConcreteImplementorA operation")
    }
}

// 具体实现B
struct ConcreteImplementorB;

impl Implementor for ConcreteImplementorB {
    fn operation_impl(&self) -> String {
        String::from("ConcreteImplementorB operation")
    }
}

// 抽象类
struct Abstraction {
    implementor: Box<dyn Implementor>,
}

impl Abstraction {
    fn new(implementor: Box<dyn Implementor>) -> Self {
        Self { implementor }
    }
    
    fn operation(&self) -> String {
        format!("Abstraction: {}", self.implementor.operation_impl())
    }
    
    fn set_implementor(&mut self, implementor: Box<dyn Implementor>) {
        self.implementor = implementor;
    }
}

// 扩展抽象类
struct RefinedAbstraction {
    implementor: Box<dyn Implementor>,
}

impl RefinedAbstraction {
    fn new(implementor: Box<dyn Implementor>) -> Self {
        Self { implementor }
    }
    
    fn operation(&self) -> String {
        format!("RefinedAbstraction: {}", self.implementor.operation_impl())
    }
    
    fn additional_operation(&self) -> String {
        format!("Additional operation with {}", self.implementor.operation_impl())
    }
}

// 使用示例
fn use_basic_bridge() {
    let implementor_a = ConcreteImplementorA;
    let implementor_b = ConcreteImplementorB;
    
    let mut abstraction = Abstraction::new(Box::new(implementor_a));
    println!("{}", abstraction.operation());
    
    abstraction.set_implementor(Box::new(implementor_b));
    println!("{}", abstraction.operation());
    
    let refined = RefinedAbstraction::new(Box::new(implementor_a));
    println!("{}", refined.operation());
    println!("{}", refined.additional_operation());
}
```

### 2. 图形绘制桥接模式

```rust
// 绘图实现接口
trait DrawingAPI {
    fn draw_circle(&self, x: i32, y: i32, radius: i32) -> String;
    fn draw_rectangle(&self, x: i32, y: i32, width: i32, height: i32) -> String;
}

// Windows绘图实现
struct WindowsDrawingAPI;

impl DrawingAPI for WindowsDrawingAPI {
    fn draw_circle(&self, x: i32, y: i32, radius: i32) -> String {
        format!("Windows: Drawing circle at ({}, {}) with radius {}", x, y, radius)
    }
    
    fn draw_rectangle(&self, x: i32, y: i32, width: i32, height: i32) -> String {
        format!("Windows: Drawing rectangle at ({}, {}) with size {}x{}", x, y, width, height)
    }
}

// Linux绘图实现
struct LinuxDrawingAPI;

impl DrawingAPI for LinuxDrawingAPI {
    fn draw_circle(&self, x: i32, y: i32, radius: i32) -> String {
        format!("Linux: Drawing circle at ({}, {}) with radius {}", x, y, radius)
    }
    
    fn draw_rectangle(&self, x: i32, y: i32, width: i32, height: i32) -> String {
        format!("Linux: Drawing rectangle at ({}, {}) with size {}x{}", x, y, width, height)
    }
}

// macOS绘图实现
struct MacOSDrawingAPI;

impl DrawingAPI for MacOSDrawingAPI {
    fn draw_circle(&self, x: i32, y: i32, radius: i32) -> String {
        format!("macOS: Drawing circle at ({}, {}) with radius {}", x, y, radius)
    }
    
    fn draw_rectangle(&self, x: i32, y: i32, width: i32, height: i32) -> String {
        format!("macOS: Drawing rectangle at ({}, {}) with size {}x{}", x, y, width, height)
    }
}

// 形状抽象类
struct Shape {
    drawing_api: Box<dyn DrawingAPI>,
}

impl Shape {
    fn new(drawing_api: Box<dyn DrawingAPI>) -> Self {
        Self { drawing_api }
    }
    
    fn draw(&self) -> String {
        String::from("Base shape draw")
    }
    
    fn resize_by_percentage(&self, percentage: f32) -> String {
        format!("Resizing shape by {}%", percentage)
    }
}

// 圆形
struct Circle {
    shape: Shape,
    x: i32,
    y: i32,
    radius: i32,
}

impl Circle {
    fn new(drawing_api: Box<dyn DrawingAPI>, x: i32, y: i32, radius: i32) -> Self {
        Self {
            shape: Shape::new(drawing_api),
            x,
            y,
            radius,
        }
    }
    
    fn draw(&self) -> String {
        self.shape.drawing_api.draw_circle(self.x, self.y, self.radius)
    }
    
    fn resize_by_percentage(&self, percentage: f32) -> String {
        let new_radius = (self.radius as f32 * percentage) as i32;
        format!("Resizing circle from radius {} to {}", self.radius, new_radius)
    }
}

// 矩形
struct Rectangle {
    shape: Shape,
    x: i32,
    y: i32,
    width: i32,
    height: i32,
}

impl Rectangle {
    fn new(drawing_api: Box<dyn DrawingAPI>, x: i32, y: i32, width: i32, height: i32) -> Self {
        Self {
            shape: Shape::new(drawing_api),
            x,
            y,
            width,
            height,
        }
    }
    
    fn draw(&self) -> String {
        self.shape.drawing_api.draw_rectangle(self.x, self.y, self.width, self.height)
    }
    
    fn resize_by_percentage(&self, percentage: f32) -> String {
        let new_width = (self.width as f32 * percentage) as i32;
        let new_height = (self.height as f32 * percentage) as i32;
        format!("Resizing rectangle from {}x{} to {}x{}", self.width, self.height, new_width, new_height)
    }
}
```

### 3. 高级桥接模式

```rust
use std::collections::HashMap;

// 消息发送实现接口
trait MessageSender {
    fn send_message(&self, message: &str, recipient: &str) -> String;
    fn send_bulk_message(&self, message: &str, recipients: &[String]) -> String;
}

// 邮件发送实现
struct EmailSender {
    smtp_server: String,
    port: u16,
}

impl EmailSender {
    fn new(smtp_server: String, port: u16) -> Self {
        Self { smtp_server, port }
    }
}

impl MessageSender for EmailSender {
    fn send_message(&self, message: &str, recipient: &str) -> String {
        format!("Email sent via {}:{} to {}: {}", self.smtp_server, self.port, recipient, message)
    }
    
    fn send_bulk_message(&self, message: &str, recipients: &[String]) -> String {
        let recipient_list = recipients.join(", ");
        format!("Bulk email sent via {}:{} to {}: {}", self.smtp_server, self.port, recipient_list, message)
    }
}

// SMS发送实现
struct SMSSender {
    gateway: String,
    api_key: String,
}

impl SMSSender {
    fn new(gateway: String, api_key: String) -> Self {
        Self { gateway, api_key }
    }
}

impl MessageSender for SMSSender {
    fn send_message(&self, message: &str, recipient: &str) -> String {
        format!("SMS sent via {} to {}: {}", self.gateway, recipient, message)
    }
    
    fn send_bulk_message(&self, message: &str, recipients: &[String]) -> String {
        let recipient_list = recipients.join(", ");
        format!("Bulk SMS sent via {} to {}: {}", self.gateway, recipient_list, message)
    }
}

// 消息抽象类
struct Message {
    sender: Box<dyn MessageSender>,
    content: String,
    metadata: HashMap<String, String>,
}

impl Message {
    fn new(sender: Box<dyn MessageSender>, content: String) -> Self {
        let mut metadata = HashMap::new();
        metadata.insert("created_at".to_string(), "2024-01-01".to_string());
        
        Self {
            sender,
            content,
            metadata,
        }
    }
    
    fn add_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }
    
    fn get_metadata(&self, key: &str) -> Option<&String> {
        self.metadata.get(key)
    }
}

// 文本消息
struct TextMessage {
    message: Message,
    recipient: String,
}

impl TextMessage {
    fn new(sender: Box<dyn MessageSender>, content: String, recipient: String) -> Self {
        Self {
            message: Message::new(sender, content),
            recipient,
        }
    }
    
    fn send(&self) -> String {
        self.message.sender.send_message(&self.message.content, &self.recipient)
    }
    
    fn get_content(&self) -> &str {
        &self.message.content
    }
    
    fn get_recipient(&self) -> &str {
        &self.recipient
    }
}

// 群发消息
struct BulkMessage {
    message: Message,
    recipients: Vec<String>,
}

impl BulkMessage {
    fn new(sender: Box<dyn MessageSender>, content: String, recipients: Vec<String>) -> Self {
        Self {
            message: Message::new(sender, content),
            recipients,
        }
    }
    
    fn send(&self) -> String {
        self.message.sender.send_bulk_message(&self.message.content, &self.recipients)
    }
    
    fn add_recipient(&mut self, recipient: String) {
        self.recipients.push(recipient);
    }
    
    fn get_recipient_count(&self) -> usize {
        self.recipients.len()
    }
}

// 消息工厂
struct MessageFactory;

impl MessageFactory {
    fn create_text_message(sender: Box<dyn MessageSender>, content: String, recipient: String) -> TextMessage {
        TextMessage::new(sender, content, recipient)
    }
    
    fn create_bulk_message(sender: Box<dyn MessageSender>, content: String, recipients: Vec<String>) -> BulkMessage {
        BulkMessage::new(sender, content, recipients)
    }
}
```

### 4. 异步桥接模式

```rust
use std::future::Future;
use std::pin::Pin;
use tokio::sync::Mutex;

// 异步实现接口
trait AsyncImplementor {
    fn operation_async<'a>(&'a self) -> Pin<Box<dyn Future<Output = String> + Send + 'a>>;
}

// 同步实现接口
trait SyncImplementor {
    fn operation_sync(&self) -> String;
}

// 异步适配器
struct AsyncAdapter {
    sync_implementor: Box<dyn SyncImplementor>,
}

impl AsyncAdapter {
    fn new(sync_implementor: Box<dyn SyncImplementor>) -> Self {
        Self { sync_implementor }
    }
}

impl AsyncImplementor for AsyncAdapter {
    fn operation_async<'a>(&'a self) -> Pin<Box<dyn Future<Output = String> + Send + 'a>> {
        Box::pin(async move {
            // 模拟异步处理
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            self.sync_implementor.operation_sync()
        })
    }
}

// 具体同步实现
struct ConcreteSyncImplementor;

impl SyncImplementor for ConcreteSyncImplementor {
    fn operation_sync(&self) -> String {
        String::from("Concrete sync operation")
    }
}

// 异步抽象类
struct AsyncAbstraction {
    implementor: Box<dyn AsyncImplementor>,
}

impl AsyncAbstraction {
    fn new(implementor: Box<dyn AsyncImplementor>) -> Self {
        Self { implementor }
    }
    
    async fn operation(&self) -> String {
        self.implementor.operation_async().await
    }
}

// 线程安全桥接
struct ThreadSafeBridge {
    implementor: Arc<Mutex<Box<dyn SyncImplementor>>>,
}

impl ThreadSafeBridge {
    fn new(implementor: Box<dyn SyncImplementor>) -> Self {
        Self {
            implementor: Arc::new(Mutex::new(implementor)),
        }
    }
    
    async fn operation(&self) -> String {
        let implementor = self.implementor.lock().await;
        implementor.operation_sync()
    }
}
```

## Haskell实现示例

```haskell
-- 实现类型类
class Implementor a where
    operationImpl :: a -> String

-- 具体实现A
data ConcreteImplementorA = ConcreteImplementorA

instance Implementor ConcreteImplementorA where
    operationImpl _ = "ConcreteImplementorA operation"

-- 具体实现B
data ConcreteImplementorB = ConcreteImplementorB

instance Implementor ConcreteImplementorB where
    operationImpl _ = "ConcreteImplementorB operation"

-- 抽象类
data Abstraction = Abstraction
    { implementor :: ConcreteImplementorA -- 简化，实际应该支持多态
    }

newAbstraction :: ConcreteImplementorA -> Abstraction
newAbstraction impl = Abstraction impl

operation :: Abstraction -> String
operation abstraction = "Abstraction: " ++ operationImpl (implementor abstraction)

-- 扩展抽象类
data RefinedAbstraction = RefinedAbstraction
    { refinedImplementor :: ConcreteImplementorA
    }

newRefinedAbstraction :: ConcreteImplementorA -> RefinedAbstraction
newRefinedAbstraction impl = RefinedAbstraction impl

refinedOperation :: RefinedAbstraction -> String
refinedOperation abstraction = "RefinedAbstraction: " ++ operationImpl (refinedImplementor abstraction)

additionalOperation :: RefinedAbstraction -> String
additionalOperation abstraction = "Additional operation with " ++ operationImpl (refinedImplementor abstraction)

-- 绘图API类型类
class DrawingAPI a where
    drawCircle :: a -> Int -> Int -> Int -> String
    drawRectangle :: a -> Int -> Int -> Int -> Int -> String

-- Windows绘图实现
data WindowsDrawingAPI = WindowsDrawingAPI

instance DrawingAPI WindowsDrawingAPI where
    drawCircle _ x y radius = "Windows: Drawing circle at (" ++ show x ++ ", " ++ show y ++ ") with radius " ++ show radius
    drawRectangle _ x y width height = "Windows: Drawing rectangle at (" ++ show x ++ ", " ++ show y ++ ") with size " ++ show width ++ "x" ++ show height

-- Linux绘图实现
data LinuxDrawingAPI = LinuxDrawingAPI

instance DrawingAPI LinuxDrawingAPI where
    drawCircle _ x y radius = "Linux: Drawing circle at (" ++ show x ++ ", " ++ show y ++ ") with radius " ++ show radius
    drawRectangle _ x y width height = "Linux: Drawing rectangle at (" ++ show x ++ ", " ++ show y ++ ") with size " ++ show width ++ "x" ++ show height

-- macOS绘图实现
data MacOSDrawingAPI = MacOSDrawingAPI

instance DrawingAPI MacOSDrawingAPI where
    drawCircle _ x y radius = "macOS: Drawing circle at (" ++ show x ++ ", " ++ show y ++ ") with radius " ++ show radius
    drawRectangle _ x y width height = "macOS: Drawing rectangle at (" ++ show x ++ ", " ++ show y ++ ") with size " ++ show width ++ "x" ++ show height

-- 形状抽象类
data Shape a = Shape
    { drawingAPI :: a
    }

newShape :: (DrawingAPI a) => a -> Shape a
newShape api = Shape api

draw :: (DrawingAPI a) => Shape a -> String
draw shape = "Base shape draw"

resizeByPercentage :: (DrawingAPI a) => Shape a -> Float -> String
resizeByPercentage _ percentage = "Resizing shape by " ++ show percentage ++ "%"

-- 圆形
data Circle a = Circle
    { circleShape :: Shape a
    , circleX :: Int
    , circleY :: Int
    , circleRadius :: Int
    }

newCircle :: (DrawingAPI a) => a -> Int -> Int -> Int -> Circle a
newCircle api x y radius = Circle (newShape api) x y radius

circleDraw :: (DrawingAPI a) => Circle a -> String
circleDraw circle = drawCircle (drawingAPI (circleShape circle)) (circleX circle) (circleY circle) (circleRadius circle)

circleResizeByPercentage :: Circle a -> Float -> String
circleResizeByPercentage circle percentage = 
    let newRadius = round (fromIntegral (circleRadius circle) * percentage)
    in "Resizing circle from radius " ++ show (circleRadius circle) ++ " to " ++ show newRadius

-- 矩形
data Rectangle a = Rectangle
    { rectangleShape :: Shape a
    , rectangleX :: Int
    , rectangleY :: Int
    , rectangleWidth :: Int
    , rectangleHeight :: Int
    }

newRectangle :: (DrawingAPI a) => a -> Int -> Int -> Int -> Int -> Rectangle a
newRectangle api x y width height = Rectangle (newShape api) x y width height

rectangleDraw :: (DrawingAPI a) => Rectangle a -> String
rectangleDraw rectangle = drawRectangle (drawingAPI (rectangleShape rectangle)) (rectangleX rectangle) (rectangleY rectangle) (rectangleWidth rectangle) (rectangleHeight rectangle)

rectangleResizeByPercentage :: Rectangle a -> Float -> String
rectangleResizeByPercentage rectangle percentage = 
    let newWidth = round (fromIntegral (rectangleWidth rectangle) * percentage)
        newHeight = round (fromIntegral (rectangleHeight rectangle) * percentage)
    in "Resizing rectangle from " ++ show (rectangleWidth rectangle) ++ "x" ++ show (rectangleHeight rectangle) ++ " to " ++ show newWidth ++ "x" ++ show newHeight

-- 消息发送类型类
class MessageSender a where
    sendMessage :: a -> String -> String -> String
    sendBulkMessage :: a -> String -> [String] -> String

-- 邮件发送实现
data EmailSender = EmailSender
    { smtpServer :: String
    , port :: Int
    }

newEmailSender :: String -> Int -> EmailSender
newEmailSender server port = EmailSender server port

instance MessageSender EmailSender where
    sendMessage sender message recipient = 
        "Email sent via " ++ smtpServer sender ++ ":" ++ show (port sender) ++ " to " ++ recipient ++ ": " ++ message
    sendBulkMessage sender message recipients = 
        let recipientList = intercalate ", " recipients
        in "Bulk email sent via " ++ smtpServer sender ++ ":" ++ show (port sender) ++ " to " ++ recipientList ++ ": " ++ message

-- SMS发送实现
data SMSSender = SMSSender
    { gateway :: String
    , apiKey :: String
    }

newSMSSender :: String -> String -> SMSSender
newSMSSender gateway apiKey = SMSSender gateway apiKey

instance MessageSender SMSSender where
    sendMessage sender message recipient = 
        "SMS sent via " ++ gateway sender ++ " to " ++ recipient ++ ": " ++ message
    sendBulkMessage sender message recipients = 
        let recipientList = intercalate ", " recipients
        in "Bulk SMS sent via " ++ gateway sender ++ " to " ++ recipientList ++ ": " ++ message

-- 消息抽象类
data Message a = Message
    { sender :: a
    , content :: String
    , metadata :: [(String, String)]
    }

newMessage :: (MessageSender a) => a -> String -> Message a
newMessage sender content = Message sender content [("created_at", "2024-01-01")]

addMetadata :: Message a -> String -> String -> Message a
addMetadata message key value = message { metadata = (key, value) : metadata message }

getMetadata :: Message a -> String -> Maybe String
getMetadata message key = lookup key (metadata message)

-- 文本消息
data TextMessage a = TextMessage
    { textMessage :: Message a
    , recipient :: String
    }

newTextMessage :: (MessageSender a) => a -> String -> String -> TextMessage a
newTextMessage sender content recipient = TextMessage (newMessage sender content) recipient

sendTextMessage :: (MessageSender a) => TextMessage a -> String
sendTextMessage message = sendMessage (sender (textMessage message)) (content (textMessage message)) (recipient message)

getTextContent :: TextMessage a -> String
getTextContent message = content (textMessage message)

getTextRecipient :: TextMessage a -> String
getTextRecipient message = recipient message

-- 群发消息
data BulkMessage a = BulkMessage
    { bulkMessage :: Message a
    , recipients :: [String]
    }

newBulkMessage :: (MessageSender a) => a -> String -> [String] -> BulkMessage a
newBulkMessage sender content recipients = BulkMessage (newMessage sender content) recipients

sendBulkMessage :: (MessageSender a) => BulkMessage a -> String
sendBulkMessage message = sendBulkMessage (sender (bulkMessage message)) (content (bulkMessage message)) (recipients message)

addBulkRecipient :: BulkMessage a -> String -> BulkMessage a
addBulkRecipient message recipient = message { recipients = recipient : recipients message }

getRecipientCount :: BulkMessage a -> Int
getRecipientCount message = length (recipients message)

-- 使用示例
useBasicBridge :: IO ()
useBasicBridge = do
    let implementorA = ConcreteImplementorA
    let implementorB = ConcreteImplementorB
    
    let abstraction = newAbstraction implementorA
    putStrLn $ operation abstraction
    
    let refined = newRefinedAbstraction implementorA
    putStrLn $ refinedOperation refined
    putStrLn $ additionalOperation refined

useDrawingBridge :: IO ()
useDrawingBridge = do
    let windowsAPI = WindowsDrawingAPI
    let linuxAPI = LinuxDrawingAPI
    let macosAPI = MacOSDrawingAPI
    
    let circle = newCircle windowsAPI 10 20 30
    putStrLn $ circleDraw circle
    putStrLn $ circleResizeByPercentage circle 1.5
    
    let rectangle = newRectangle linuxAPI 5 15 25 35
    putStrLn $ rectangleDraw rectangle
    putStrLn $ rectangleResizeByPercentage rectangle 0.8
    
    let macCircle = newCircle macosAPI 100 200 300
    putStrLn $ circleDraw macCircle

useMessageBridge :: IO ()
useMessageBridge = do
    let emailSender = newEmailSender "smtp.gmail.com" 587
    let smsSender = newSMSSender "twilio.com" "api_key_123"
    
    let textMessage = newTextMessage emailSender "Hello World" "user@example.com"
    putStrLn $ sendTextMessage textMessage
    
    let bulkMessage = newBulkMessage smsSender "Bulk SMS" ["+1234567890", "+0987654321"]
    putStrLn $ sendBulkMessage bulkMessage
    putStrLn $ "Recipient count: " ++ show (getRecipientCount bulkMessage)
```

## Lean实现思路

```lean
-- 实现类型类
class Implementor (α : Type) where
  operationImpl : α → String

-- 具体实现A
inductive ConcreteImplementorA where
  | ConcreteImplementorA : ConcreteImplementorA

instance : Implementor ConcreteImplementorA where
  operationImpl _ := "ConcreteImplementorA operation"

-- 具体实现B
inductive ConcreteImplementorB where
  | ConcreteImplementorB : ConcreteImplementorB

instance : Implementor ConcreteImplementorB where
  operationImpl _ := "ConcreteImplementorB operation"

-- 抽象类
structure Abstraction where
  implementor : ConcreteImplementorA -- 简化，实际应该支持多态

def newAbstraction (impl : ConcreteImplementorA) : Abstraction :=
  { implementor := impl }

def operation (abstraction : Abstraction) : String :=
  "Abstraction: " ++ Implementor.operationImpl abstraction.implementor

-- 扩展抽象类
structure RefinedAbstraction where
  refinedImplementor : ConcreteImplementorA

def newRefinedAbstraction (impl : ConcreteImplementorA) : RefinedAbstraction :=
  { refinedImplementor := impl }

def refinedOperation (abstraction : RefinedAbstraction) : String :=
  "RefinedAbstraction: " ++ Implementor.operationImpl abstraction.refinedImplementor

def additionalOperation (abstraction : RefinedAbstraction) : String :=
  "Additional operation with " ++ Implementor.operationImpl abstraction.refinedImplementor

-- 绘图API类型类
class DrawingAPI (α : Type) where
  drawCircle : α → Nat → Nat → Nat → String
  drawRectangle : α → Nat → Nat → Nat → Nat → String

-- Windows绘图实现
inductive WindowsDrawingAPI where
  | WindowsDrawingAPI : WindowsDrawingAPI

instance : DrawingAPI WindowsDrawingAPI where
  drawCircle _ x y radius := s!"Windows: Drawing circle at ({x}, {y}) with radius {radius}"
  drawRectangle _ x y width height := s!"Windows: Drawing rectangle at ({x}, {y}) with size {width}x{height}"

-- Linux绘图实现
inductive LinuxDrawingAPI where
  | LinuxDrawingAPI : LinuxDrawingAPI

instance : DrawingAPI LinuxDrawingAPI where
  drawCircle _ x y radius := s!"Linux: Drawing circle at ({x}, {y}) with radius {radius}"
  drawRectangle _ x y width height := s!"Linux: Drawing rectangle at ({x}, {y}) with size {width}x{height}"

-- macOS绘图实现
inductive MacOSDrawingAPI where
  | MacOSDrawingAPI : MacOSDrawingAPI

instance : DrawingAPI MacOSDrawingAPI where
  drawCircle _ x y radius := s!"macOS: Drawing circle at ({x}, {y}) with radius {radius}"
  drawRectangle _ x y width height := s!"macOS: Drawing rectangle at ({x}, {y}) with size {width}x{height}"

-- 形状抽象类
structure Shape (α : Type) where
  drawingAPI : α

def newShape (api : α) : Shape α :=
  { drawingAPI := api }

def draw (shape : Shape α) : String :=
  "Base shape draw"

def resizeByPercentage (shape : Shape α) (percentage : Float) : String :=
  s!"Resizing shape by {percentage}%"

-- 圆形
structure Circle (α : Type) where
  circleShape : Shape α
  circleX : Nat
  circleY : Nat
  circleRadius : Nat

def newCircle (api : α) (x y radius : Nat) : Circle α :=
  { circleShape := newShape api
  , circleX := x
  , circleY := y
  , circleRadius := radius
  }

def circleDraw (circle : Circle α) : String :=
  DrawingAPI.drawCircle circle.circleShape.drawingAPI circle.circleX circle.circleY circle.circleRadius

def circleResizeByPercentage (circle : Circle α) (percentage : Float) : String :=
  let newRadius := (circle.circleRadius.toFloat * percentage).toNat
  s!"Resizing circle from radius {circle.circleRadius} to {newRadius}"

-- 矩形
structure Rectangle (α : Type) where
  rectangleShape : Shape α
  rectangleX : Nat
  rectangleY : Nat
  rectangleWidth : Nat
  rectangleHeight : Nat

def newRectangle (api : α) (x y width height : Nat) : Rectangle α :=
  { rectangleShape := newShape api
  , rectangleX := x
  , rectangleY := y
  , rectangleWidth := width
  , rectangleHeight := height
  }

def rectangleDraw (rectangle : Rectangle α) : String :=
  DrawingAPI.drawRectangle rectangle.rectangleShape.drawingAPI rectangle.rectangleX rectangle.rectangleY rectangle.rectangleWidth rectangle.rectangleHeight

def rectangleResizeByPercentage (rectangle : Rectangle α) (percentage : Float) : String :=
  let newWidth := (rectangle.rectangleWidth.toFloat * percentage).toNat
  let newHeight := (rectangle.rectangleHeight.toFloat * percentage).toNat
  s!"Resizing rectangle from {rectangle.rectangleWidth}x{rectangle.rectangleHeight} to {newWidth}x{newHeight}"

-- 消息发送类型类
class MessageSender (α : Type) where
  sendMessage : α → String → String → String
  sendBulkMessage : α → String → List String → String

-- 邮件发送实现
structure EmailSender where
  smtpServer : String
  port : Nat

def newEmailSender (server : String) (port : Nat) : EmailSender :=
  { smtpServer := server
  , port := port
  }

instance : MessageSender EmailSender where
  sendMessage sender message recipient := 
    s!"Email sent via {sender.smtpServer}:{sender.port} to {recipient}: {message}"
  sendBulkMessage sender message recipients := 
    let recipientList := String.intercalate ", " recipients
    s!"Bulk email sent via {sender.smtpServer}:{sender.port} to {recipientList}: {message}"

-- SMS发送实现
structure SMSSender where
  gateway : String
  apiKey : String

def newSMSSender (gateway apiKey : String) : SMSSender :=
  { gateway := gateway
  , apiKey := apiKey
  }

instance : MessageSender SMSSender where
  sendMessage sender message recipient := 
    s!"SMS sent via {sender.gateway} to {recipient}: {message}"
  sendBulkMessage sender message recipients := 
    let recipientList := String.intercalate ", " recipients
    s!"Bulk SMS sent via {sender.gateway} to {recipientList}: {message}"

-- 消息抽象类
structure Message (α : Type) where
  sender : α
  content : String
  metadata : List (String × String)

def newMessage (sender : α) (content : String) : Message α :=
  { sender := sender
  , content := content
  , metadata := [("created_at", "2024-01-01")]
  }

def addMetadata (message : Message α) (key value : String) : Message α :=
  { message with metadata := (key, value) :: message.metadata }

def getMetadata (message : Message α) (key : String) : Option String :=
  message.metadata.find? (fun (k, _) => k == key) |>.map (fun (_, v) => v)

-- 文本消息
structure TextMessage (α : Type) where
  textMessage : Message α
  recipient : String

def newTextMessage (sender : α) (content recipient : String) : TextMessage α :=
  { textMessage := newMessage sender content
  , recipient := recipient
  }

def sendTextMessage (message : TextMessage α) : String :=
  MessageSender.sendMessage message.textMessage.sender message.textMessage.content message.recipient

def getTextContent (message : TextMessage α) : String :=
  message.textMessage.content

def getTextRecipient (message : TextMessage α) : String :=
  message.recipient

-- 群发消息
structure BulkMessage (α : Type) where
  bulkMessage : Message α
  recipients : List String

def newBulkMessage (sender : α) (content : String) (recipients : List String) : BulkMessage α :=
  { bulkMessage := newMessage sender content
  , recipients := recipients
  }

def sendBulkMessage (message : BulkMessage α) : String :=
  MessageSender.sendBulkMessage message.bulkMessage.sender message.bulkMessage.content message.recipients

def addBulkRecipient (message : BulkMessage α) (recipient : String) : BulkMessage α :=
  { message with recipients := recipient :: message.recipients }

def getRecipientCount (message : BulkMessage α) : Nat :=
  message.recipients.length
```

## 应用场景

### 1. 图形系统

- **跨平台绘图**: 支持不同操作系统的绘图API
- **渲染引擎**: 支持不同的渲染后端
- **UI框架**: 支持不同的UI组件库

### 2. 消息系统

- **多渠道发送**: 支持邮件、短信、推送等
- **协议适配**: 支持不同的通信协议
- **格式转换**: 支持不同的消息格式

### 3. 数据库系统

- **多数据库支持**: 支持MySQL、PostgreSQL等
- **ORM框架**: 提供统一的数据库访问接口
- **连接池管理**: 管理不同类型的数据库连接

### 4. 网络通信

- **协议抽象**: 支持不同的网络协议
- **序列化**: 支持不同的数据格式
- **认证机制**: 支持不同的认证方式

## 最佳实践

### 1. 设计原则

- 遵循开闭原则
- 使用组合优于继承
- 保持抽象和实现的分离

### 2. 性能考虑

- 减少桥接开销
- 使用对象池
- 优化内存分配

### 3. 扩展性

- 易于添加新的实现
- 支持运行时切换
- 提供默认实现

### 4. 错误处理

- 处理实现失败
- 提供回退机制
- 记录错误日志

## 性能考虑

### 1. 桥接开销

- 方法调用开销
- 对象创建成本
- 内存分配

### 2. 缓存策略

- 实现缓存
- 结果缓存
- 配置缓存

### 3. 并发安全

- 线程安全设计
- 锁机制
- 原子操作

## 总结

桥接模式是分离抽象和实现的重要设计模式，通过组合关系替代继承关系，降低了系统的耦合度。合理使用桥接模式可以提高系统的灵活性和可扩展性，特别是在需要支持多个独立变化维度的场景中发挥重要作用。
