# 断路器模式（Circuit Breaker Pattern）

## 概述
断路器模式是一种分布式系统设计模式，用于防止级联故障，通过监控服务调用的失败率，在达到阈值时自动断开电路，避免对故障服务的持续调用。

## 理论基础
- **关闭状态**：正常调用服务
- **开启状态**：快速失败，不调用服务
- **半开状态**：允许少量请求测试服务恢复

## Rust实现示例
```rust
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::time::sleep;

// 断路器状态
#[derive(Debug, Clone, PartialEq)]
enum CircuitState {
    Closed,    // 关闭状态：正常调用
    Open,      // 开启状态：快速失败
    HalfOpen,  // 半开状态：测试调用
}

// 断路器配置
#[derive(Debug, Clone)]
struct CircuitBreakerConfig {
    failure_threshold: u32,      // 失败阈值
    timeout_duration: Duration,  // 超时时间
    success_threshold: u32,      // 成功阈值（半开状态）
    window_size: Duration,       // 滑动窗口大小
}

impl Default for CircuitBreakerConfig {
    fn default() -> Self {
        Self {
            failure_threshold: 5,
            timeout_duration: Duration::from_secs(60),
            success_threshold: 3,
            window_size: Duration::from_secs(60),
        }
    }
}

// 断路器
struct CircuitBreaker {
    state: Arc<Mutex<CircuitState>>,
    failure_count: Arc<Mutex<u32>>,
    success_count: Arc<Mutex<u32>>,
    last_failure_time: Arc<Mutex<Option<Instant>>>,
    config: CircuitBreakerConfig,
}

impl CircuitBreaker {
    fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            state: Arc::new(Mutex::new(CircuitState::Closed)),
            failure_count: Arc::new(Mutex::new(0)),
            success_count: Arc::new(Mutex::new(0)),
            last_failure_time: Arc::new(Mutex::new(None)),
            config,
        }
    }
    
    fn can_execute(&self) -> bool {
        let state = { *self.state.lock().unwrap() };
        
        match state {
            CircuitState::Closed => true,
            CircuitState::Open => {
                // 检查是否超时，可以进入半开状态
                if let Some(last_failure) = { *self.last_failure_time.lock().unwrap() } {
                    if Instant::now().duration_since(last_failure) >= self.config.timeout_duration {
                        self.transition_to_half_open();
                        true
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            CircuitState::HalfOpen => true,
        }
    }
    
    fn on_success(&self) {
        let mut state = self.state.lock().unwrap();
        let mut failure_count = self.failure_count.lock().unwrap();
        let mut success_count = self.success_count.lock().unwrap();
        
        match *state {
            CircuitState::Closed => {
                // 重置失败计数
                *failure_count = 0;
            }
            CircuitState::HalfOpen => {
                *success_count += 1;
                if *success_count >= self.config.success_threshold {
                    self.transition_to_closed();
                }
            }
            CircuitState::Open => {
                // 不应该在开启状态收到成功
            }
        }
    }
    
    fn on_failure(&self) {
        let mut state = self.state.lock().unwrap();
        let mut failure_count = self.failure_count.lock().unwrap();
        let mut last_failure_time = self.last_failure_time.lock().unwrap();
        
        match *state {
            CircuitState::Closed => {
                *failure_count += 1;
                *last_failure_time = Some(Instant::now());
                
                if *failure_count >= self.config.failure_threshold {
                    self.transition_to_open();
                }
            }
            CircuitState::HalfOpen => {
                // 半开状态失败，立即回到开启状态
                self.transition_to_open();
            }
            CircuitState::Open => {
                // 更新最后失败时间
                *last_failure_time = Some(Instant::now());
            }
        }
    }
    
    fn transition_to_open(&self) {
        let mut state = self.state.lock().unwrap();
        let mut failure_count = self.failure_count.lock().unwrap();
        let mut success_count = self.success_count.lock().unwrap();
        
        *state = CircuitState::Open;
        *failure_count = 0;
        *success_count = 0;
        
        println!("断路器状态: 开启");
    }
    
    fn transition_to_half_open(&self) {
        let mut state = self.state.lock().unwrap();
        let mut success_count = self.success_count.lock().unwrap();
        
        *state = CircuitState::HalfOpen;
        *success_count = 0;
        
        println!("断路器状态: 半开");
    }
    
    fn transition_to_closed(&self) {
        let mut state = self.state.lock().unwrap();
        let mut failure_count = self.failure_count.lock().unwrap();
        let mut success_count = self.success_count.lock().unwrap();
        
        *state = CircuitState::Closed;
        *failure_count = 0;
        *success_count = 0;
        
        println!("断路器状态: 关闭");
    }
    
    fn get_state(&self) -> CircuitState {
        { *self.state.lock().unwrap() }
    }
}

// 异步服务调用包装器
struct CircuitBreakerCall<T, E> {
    circuit_breaker: Arc<CircuitBreaker>,
    call_fn: Box<dyn Fn() -> Result<T, E> + Send + Sync>,
}

impl<T, E> CircuitBreakerCall<T, E> {
    fn new(
        circuit_breaker: Arc<CircuitBreaker>,
        call_fn: Box<dyn Fn() -> Result<T, E> + Send + Sync>,
    ) -> Self {
        Self {
            circuit_breaker,
            call_fn,
        }
    }
    
    async fn execute(&self) -> Result<T, String> {
        if !self.circuit_breaker.can_execute() {
            return Err("断路器开启，快速失败".to_string());
        }
        
        match (self.call_fn)() {
            Ok(result) => {
                self.circuit_breaker.on_success();
                Ok(result)
            }
            Err(_) => {
                self.circuit_breaker.on_failure();
                Err("服务调用失败".to_string())
            }
        }
    }
}

// 模拟服务
struct MockService {
    failure_rate: f64,
    call_count: Arc<Mutex<u32>>,
}

impl MockService {
    fn new(failure_rate: f64) -> Self {
        Self {
            failure_rate,
            call_count: Arc::new(Mutex::new(0)),
        }
    }
    
    fn call(&self) -> Result<String, String> {
        let mut call_count = self.call_count.lock().unwrap();
        *call_count += 1;
        
        // 模拟失败率
        if rand::random::<f64>() < self.failure_rate {
            Err("服务调用失败".to_string())
        } else {
            Ok(format!("服务调用成功，调用次数: {}", *call_count))
        }
    }
}

// 滑动窗口断路器
struct SlidingWindowCircuitBreaker {
    state: Arc<Mutex<CircuitState>>,
    window: Arc<Mutex<Vec<Instant>>>,
    config: CircuitBreakerConfig,
}

impl SlidingWindowCircuitBreaker {
    fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            state: Arc::new(Mutex::new(CircuitState::Closed)),
            window: Arc::new(Mutex::new(Vec::new())),
            config,
        }
    }
    
    fn record_call(&self, success: bool) {
        let now = Instant::now();
        let mut window = self.window.lock().unwrap();
        
        // 添加当前调用记录
        window.push(now);
        
        // 清理过期的记录
        window.retain(|&time| now.duration_since(time) <= self.config.window_size);
        
        // 计算失败率
        let total_calls = window.len();
        let failure_count = if success { 0 } else { 1 };
        
        if total_calls >= self.config.failure_threshold as usize {
            let failure_rate = failure_count as f64 / total_calls as f64;
            
            if failure_rate > 0.5 {
                // 失败率超过50%，开启断路器
                let mut state = self.state.lock().unwrap();
                *state = CircuitState::Open;
                println!("滑动窗口断路器开启，失败率: {:.2}", failure_rate);
            }
        }
    }
    
    fn can_execute(&self) -> bool {
        let state = { *self.state.lock().unwrap() };
        state != CircuitState::Open
    }
}

// 分布式断路器
struct DistributedCircuitBreaker {
    local_breaker: Arc<CircuitBreaker>,
    remote_breakers: Arc<Mutex<Vec<Arc<CircuitBreaker>>>>,
}

impl DistributedCircuitBreaker {
    fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            local_breaker: Arc::new(CircuitBreaker::new(config.clone())),
            remote_breakers: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    fn add_remote_breaker(&self, breaker: Arc<CircuitBreaker>) {
        let mut remote_breakers = self.remote_breakers.lock().unwrap();
        remote_breakers.push(breaker);
    }
    
    fn can_execute(&self) -> bool {
        // 检查本地断路器
        if !self.local_breaker.can_execute() {
            return false;
        }
        
        // 检查远程断路器
        let remote_breakers = self.remote_breakers.lock().unwrap();
        for breaker in remote_breakers.iter() {
            if !breaker.can_execute() {
                return false;
            }
        }
        
        true
    }
}

#[tokio::main]
async fn main() {
    // 基本断路器测试
    println!("=== 基本断路器测试 ===");
    let config = CircuitBreakerConfig::default();
    let circuit_breaker = Arc::new(CircuitBreaker::new(config));
    let service = MockService::new(0.8); // 80%失败率
    
    let call_wrapper = CircuitBreakerCall::new(
        Arc::clone(&circuit_breaker),
        Box::new(move || service.call()),
    );
    
    // 模拟多次调用
    for i in 0..10 {
        match call_wrapper.execute().await {
            Ok(result) => println!("调用 {}: {}", i, result),
            Err(error) => println!("调用 {}: {}", i, error),
        }
        
        sleep(Duration::from_millis(100)).await;
    }
    
    // 滑动窗口断路器测试
    println!("\n=== 滑动窗口断路器测试 ===");
    let sliding_config = CircuitBreakerConfig {
        failure_threshold: 3,
        timeout_duration: Duration::from_secs(30),
        success_threshold: 2,
        window_size: Duration::from_secs(10),
    };
    
    let sliding_breaker = SlidingWindowCircuitBreaker::new(sliding_config);
    
    for i in 0..5 {
        let success = rand::random::<f64>() > 0.7;
        sliding_breaker.record_call(success);
        
        if sliding_breaker.can_execute() {
            println!("调用 {}: 允许执行", i);
        } else {
            println!("调用 {}: 断路器开启", i);
        }
        
        sleep(Duration::from_millis(200)).await;
    }
    
    // 分布式断路器测试
    println!("\n=== 分布式断路器测试 ===");
    let distributed_config = CircuitBreakerConfig::default();
    let distributed_breaker = DistributedCircuitBreaker::new(distributed_config);
    
    // 添加远程断路器
    let remote_breaker1 = Arc::new(CircuitBreaker::new(CircuitBreakerConfig::default()));
    let remote_breaker2 = Arc::new(CircuitBreaker::new(CircuitBreakerConfig::default()));
    
    distributed_breaker.add_remote_breaker(Arc::clone(&remote_breaker1));
    distributed_breaker.add_remote_breaker(Arc::clone(&remote_breaker2));
    
    for i in 0..5 {
        if distributed_breaker.can_execute() {
            println!("分布式调用 {}: 允许执行", i);
        } else {
            println!("分布式调用 {}: 断路器开启", i);
        }
        
        sleep(Duration::from_millis(100)).await;
    }
} 