# Petri网模式（Petri Net Pattern）

## 概述
Petri网模式是一种工作流设计模式，使用Petri网理论来建模和执行业务流程，通过库所（Place）和变迁（Transition）来描述系统的状态和转换。

## 理论基础
- **库所（Place）**：表示系统状态
- **变迁（Transition）**：表示状态转换
- **令牌（Token）**：表示资源或条件
- **点火（Firing）**：执行变迁的条件

## Rust实现示例
```rust
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use uuid::Uuid;

// 库所（Place）
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Place {
    id: String,
    name: String,
    tokens: u32,
    capacity: Option<u32>,
}

impl Place {
    fn new(name: String, capacity: Option<u32>) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            name,
            tokens: 0,
            capacity,
        }
    }
    
    fn add_token(&mut self) -> Result<(), String> {
        if let Some(capacity) = self.capacity {
            if self.tokens >= capacity {
                return Err("库所容量已满".to_string());
            }
        }
        self.tokens += 1;
        Ok(())
    }
    
    fn remove_token(&mut self) -> Result<(), String> {
        if self.tokens == 0 {
            return Err("库所没有令牌".to_string());
        }
        self.tokens -= 1;
        Ok(())
    }
    
    fn can_add_token(&self) -> bool {
        match self.capacity {
            Some(capacity) => self.tokens < capacity,
            None => true,
        }
    }
    
    fn has_token(&self) -> bool {
        self.tokens > 0
    }
}

// 变迁（Transition）
#[derive(Debug, Clone)]
struct Transition {
    id: String,
    name: String,
    input_places: Vec<String>,
    output_places: Vec<String>,
    guard: Option<Box<dyn Fn(&HashMap<String, Place>) -> bool + Send + Sync>>,
    action: Option<Box<dyn Fn(&mut HashMap<String, Place>) -> Result<(), String> + Send + Sync>>,
}

impl Transition {
    fn new(name: String) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            name,
            input_places: Vec::new(),
            output_places: Vec::new(),
            guard: None,
            action: None,
        }
    }
    
    fn add_input_place(&mut self, place_id: String) {
        self.input_places.push(place_id);
    }
    
    fn add_output_place(&mut self, place_id: String) {
        self.output_places.push(place_id);
    }
    
    fn set_guard(&mut self, guard: Box<dyn Fn(&HashMap<String, Place>) -> bool + Send + Sync>) {
        self.guard = Some(guard);
    }
    
    fn set_action(&mut self, action: Box<dyn Fn(&mut HashMap<String, Place>) -> Result<(), String> + Send + Sync>) {
        self.action = Some(action);
    }
    
    fn can_fire(&self, places: &HashMap<String, Place>) -> bool {
        // 检查输入库所是否有足够的令牌
        for place_id in &self.input_places {
            if let Some(place) = places.get(place_id) {
                if !place.has_token() {
                    return false;
                }
            } else {
                return false;
            }
        }
        
        // 检查输出库所是否有足够容量
        for place_id in &self.output_places {
            if let Some(place) = places.get(place_id) {
                if !place.can_add_token() {
                    return false;
                }
            }
        }
        
        // 检查守卫条件
        if let Some(ref guard) = self.guard {
            if !guard(places) {
                return false;
            }
        }
        
        true
    }
    
    fn fire(&self, places: &mut HashMap<String, Place>) -> Result<(), String> {
        if !self.can_fire(places) {
            return Err("变迁无法点火".to_string());
        }
        
        // 执行动作
        if let Some(ref action) = self.action {
            action(places)?;
        }
        
        // 从输入库所移除令牌
        for place_id in &self.input_places {
            if let Some(place) = places.get_mut(place_id) {
                place.remove_token()?;
            }
        }
        
        // 向输出库所添加令牌
        for place_id in &self.output_places {
            if let Some(place) = places.get_mut(place_id) {
                place.add_token()?;
            }
        }
        
        println!("变迁 {} 点火成功", self.name);
        Ok(())
    }
}

// Petri网
struct PetriNet {
    places: HashMap<String, Place>,
    transitions: HashMap<String, Transition>,
    marking: HashMap<String, u32>, // 当前标记
}

impl PetriNet {
    fn new() -> Self {
        Self {
            places: HashMap::new(),
            transitions: HashMap::new(),
            marking: HashMap::new(),
        }
    }
    
    fn add_place(&mut self, place: Place) {
        let place_id = place.id.clone();
        self.marking.insert(place_id.clone(), place.tokens);
        self.places.insert(place_id, place);
    }
    
    fn add_transition(&mut self, transition: Transition) {
        let transition_id = transition.id.clone();
        self.transitions.insert(transition_id, transition);
    }
    
    fn connect_place_to_transition(&mut self, place_id: &str, transition_id: &str) {
        if let Some(transition) = self.transitions.get_mut(transition_id) {
            transition.add_input_place(place_id.to_string());
        }
    }
    
    fn connect_transition_to_place(&mut self, transition_id: &str, place_id: &str) {
        if let Some(transition) = self.transitions.get_mut(transition_id) {
            transition.add_output_place(place_id.to_string());
        }
    }
    
    fn get_enabled_transitions(&self) -> Vec<&Transition> {
        let mut enabled = Vec::new();
        
        for transition in self.transitions.values() {
            if self.can_fire_transition(transition) {
                enabled.push(transition);
            }
        }
        
        enabled
    }
    
    fn can_fire_transition(&self, transition: &Transition) -> bool {
        // 检查输入库所是否有足够的令牌
        for place_id in &transition.input_places {
            if let Some(tokens) = self.marking.get(place_id) {
                if *tokens == 0 {
                    return false;
                }
            } else {
                return false;
            }
        }
        
        // 检查输出库所是否有足够容量
        for place_id in &transition.output_places {
            if let Some(place) = self.places.get(place_id) {
                if !place.can_add_token() {
                    return false;
                }
            }
        }
        
        // 检查守卫条件
        if let Some(ref guard) = transition.guard {
            if !guard(&self.places) {
                return false;
            }
        }
        
        true
    }
    
    fn fire_transition(&mut self, transition_id: &str) -> Result<(), String> {
        if let Some(transition) = self.transitions.get(transition_id) {
            if !self.can_fire_transition(transition) {
                return Err("变迁无法点火".to_string());
            }
            
            // 执行动作
            if let Some(ref action) = transition.action {
                action(&mut self.places)?;
            }
            
            // 更新标记
            for place_id in &transition.input_places {
                if let Some(tokens) = self.marking.get_mut(place_id) {
                    *tokens -= 1;
                }
            }
            
            for place_id in &transition.output_places {
                if let Some(tokens) = self.marking.get_mut(place_id) {
                    *tokens += 1;
                } else {
                    self.marking.insert(place_id.clone(), 1);
                }
            }
            
            println!("变迁 {} 点火成功", transition.name);
            Ok(())
        } else {
            Err("变迁不存在".to_string())
        }
    }
    
    fn get_marking(&self) -> &HashMap<String, u32> {
        &self.marking
    }
    
    fn set_initial_marking(&mut self, place_id: &str, tokens: u32) {
        self.marking.insert(place_id.to_string(), tokens);
    }
    
    fn is_deadlock(&self) -> bool {
        self.get_enabled_transitions().is_empty()
    }
    
    fn is_live(&self) -> bool {
        // 简化的活性检查
        !self.is_deadlock()
    }
}

// 工作流引擎
struct WorkflowEngine {
    petri_net: Arc<Mutex<PetriNet>>,
    execution_history: Arc<Mutex<Vec<String>>>,
}

impl WorkflowEngine {
    fn new(petri_net: PetriNet) -> Self {
        Self {
            petri_net: Arc::new(Mutex::new(petri_net)),
            execution_history: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    async fn execute_workflow(&self) -> Result<(), String> {
        let mut iteration = 0;
        let max_iterations = 100;
        
        while iteration < max_iterations {
            let enabled_transitions = {
                let petri_net = self.petri_net.lock().unwrap();
                petri_net.get_enabled_transitions()
                    .iter()
                    .map(|t| t.id.clone())
                    .collect::<Vec<_>>()
            };
            
            if enabled_transitions.is_empty() {
                println!("工作流执行完成或进入死锁");
                break;
            }
            
            // 选择第一个可用的变迁
            if let Some(transition_id) = enabled_transitions.first() {
                let result = {
                    let mut petri_net = self.petri_net.lock().unwrap();
                    petri_net.fire_transition(transition_id)
                };
                
                match result {
                    Ok(_) => {
                        let mut history = self.execution_history.lock().unwrap();
                        history.push(transition_id.clone());
                    }
                    Err(error) => {
                        println!("执行变迁失败: {}", error);
                        return Err(error);
                    }
                }
            }
            
            iteration += 1;
        }
        
        if iteration >= max_iterations {
            return Err("工作流执行超时".to_string());
        }
        
        Ok(())
    }
    
    fn get_execution_history(&self) -> Vec<String> {
        let history = self.execution_history.lock().unwrap();
        history.clone()
    }
    
    fn get_current_marking(&self) -> HashMap<String, u32> {
        let petri_net = self.petri_net.lock().unwrap();
        petri_net.get_marking().clone()
    }
}

// 订单处理工作流示例
fn create_order_workflow() -> PetriNet {
    let mut net = PetriNet::new();
    
    // 创建库所
    let start = Place::new("开始".to_string(), None);
    let order_created = Place::new("订单已创建".to_string(), None);
    let inventory_checked = Place::new("库存已检查".to_string(), None);
    let payment_processed = Place::new("支付已处理".to_string(), None);
    let order_shipped = Place::new("订单已发货".to_string(), None);
    let order_completed = Place::new("订单已完成".to_string(), None);
    
    net.add_place(start);
    net.add_place(order_created);
    net.add_place(inventory_checked);
    net.add_place(payment_processed);
    net.add_place(order_shipped);
    net.add_place(order_completed);
    
    // 创建变迁
    let mut create_order = Transition::new("创建订单".to_string());
    let mut check_inventory = Transition::new("检查库存".to_string());
    let mut process_payment = Transition::new("处理支付".to_string());
    let mut ship_order = Transition::new("发货".to_string());
    let mut complete_order = Transition::new("完成订单".to_string());
    
    // 设置守卫条件
    create_order.set_guard(Box::new(|_places| {
        // 简化的守卫条件
        true
    }));
    
    check_inventory.set_guard(Box::new(|_places| {
        // 检查库存是否充足
        true
    }));
    
    process_payment.set_guard(Box::new(|_places| {
        // 检查支付是否成功
        true
    }));
    
    // 设置动作
    create_order.set_action(Box::new(|_places| {
        println!("执行：创建订单");
        Ok(())
    }));
    
    check_inventory.set_action(Box::new(|_places| {
        println!("执行：检查库存");
        Ok(())
    }));
    
    process_payment.set_action(Box::new(|_places| {
        println!("执行：处理支付");
        Ok(())
    }));
    
    ship_order.set_action(Box::new(|_places| {
        println!("执行：发货");
        Ok(())
    }));
    
    complete_order.set_action(Box::new(|_places| {
        println!("执行：完成订单");
        Ok(())
    }));
    
    net.add_transition(create_order);
    net.add_transition(check_inventory);
    net.add_transition(process_payment);
    net.add_transition(ship_order);
    net.add_transition(complete_order);
    
    // 连接库所和变迁
    net.connect_place_to_transition("开始", "创建订单");
    net.connect_transition_to_place("创建订单", "订单已创建");
    
    net.connect_place_to_transition("订单已创建", "检查库存");
    net.connect_transition_to_place("检查库存", "库存已检查");
    
    net.connect_place_to_transition("库存已检查", "处理支付");
    net.connect_transition_to_place("处理支付", "支付已处理");
    
    net.connect_place_to_transition("支付已处理", "发货");
    net.connect_transition_to_place("发货", "订单已发货");
    
    net.connect_place_to_transition("订单已发货", "完成订单");
    net.connect_transition_to_place("完成订单", "订单已完成");
    
    // 设置初始标记
    net.set_initial_marking("开始", 1);
    
    net
}

#[tokio::main]
async fn main() {
    // 创建订单处理工作流
    let petri_net = create_order_workflow();
    let engine = WorkflowEngine::new(petri_net);
    
    println!("=== 订单处理工作流执行 ===");
    
    match engine.execute_workflow().await {
        Ok(_) => {
            println!("工作流执行成功");
            println!("执行历史: {:?}", engine.get_execution_history());
            println!("最终标记: {:?}", engine.get_current_marking());
        }
        Err(error) => {
            println!("工作流执行失败: {}", error);
        }
    }
    
    // 测试死锁检测
    println!("\n=== 死锁检测测试 ===");
    let mut test_net = PetriNet::new();
    
    let place1 = Place::new("P1".to_string(), None);
    let place2 = Place::new("P2".to_string(), None);
    
    test_net.add_place(place1);
    test_net.add_place(place2);
    
    let mut transition = Transition::new("T1".to_string());
    transition.add_input_place("P1".to_string());
    transition.add_output_place("P2".to_string());
    
    test_net.add_transition(transition);
    test_net.set_initial_marking("P1", 0); // 没有令牌，会导致死锁
    
    if test_net.is_deadlock() {
        println!("检测到死锁");
    } else {
        println!("没有死锁");
    }
    
    if test_net.is_live() {
        println!("Petri网是活的");
    } else {
        println!("Petri网不是活的");
    }
} 