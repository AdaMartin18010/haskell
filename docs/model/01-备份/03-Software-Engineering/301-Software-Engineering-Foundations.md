# 软件工程基础

## 概述

软件工程是将工程原理应用于软件开发的学科。本文档介绍基于函数式编程和形式方法的现代软件工程实践，重点关注Haskell、Rust和Lean在软件开发生命周期中的应用。

## 软件开发生命周期

### 需求分析与建模

```haskell
-- 需求的形式化建模
{-# LANGUAGE GADTs #-}

-- 需求规约DSL
data Requirement where
  Functional :: String -> [Input] -> Output -> Requirement
  NonFunctional :: NFRType -> Constraint -> Requirement
  
data NFRType = Performance | Security | Usability | Reliability

data Constraint = Constraint
  { metric :: String
  , operator :: ComparisonOp
  , threshold :: Double
  , unit :: String
  }

data ComparisonOp = LTE | GTE | EQ | NEQ

-- 示例需求
userAuthRequirement :: Requirement
userAuthRequirement = Functional 
  "用户认证"
  [Username, Password]
  (Either AuthError AuthToken)

performanceRequirement :: Requirement  
performanceRequirement = NonFunctional
  Performance
  (Constraint "响应时间" LTE 200 "毫秒")

-- 需求验证
validateRequirement :: Requirement -> [ValidationError]
validateRequirement req = case req of
  Functional name inputs output -> 
    validateFunctionalReq name inputs output
  NonFunctional nfrType constraint -> 
    validateNonFunctionalReq nfrType constraint

validateFunctionalReq :: String -> [Input] -> Output -> [ValidationError]
validateFunctionalReq name inputs output = 
  catMaybes [ validateName name
            , validateInputs inputs  
            , validateOutput output ]

data ValidationError 
  = EmptyName
  | InvalidInput String
  | InvalidOutput String
  deriving (Show, Eq)
```

### 设计模式与架构

```rust
// 设计模式的类型安全实现

// 建造者模式
#[derive(Debug, Default)]
pub struct DatabaseConfig {
    host: Option<String>,
    port: Option<u16>,
    username: Option<String>,
    password: Option<String>,
    database: Option<String>,
}

pub struct DatabaseConfigBuilder {
    config: DatabaseConfig,
}

impl DatabaseConfigBuilder {
    pub fn new() -> Self {
        Self {
            config: DatabaseConfig::default(),
        }
    }
    
    pub fn host(mut self, host: impl Into<String>) -> Self {
        self.config.host = Some(host.into());
        self
    }
    
    pub fn port(mut self, port: u16) -> Self {
        self.config.port = Some(port);
        self
    }
    
    pub fn credentials(mut self, username: impl Into<String>, password: impl Into<String>) -> Self {
        self.config.username = Some(username.into());
        self.config.password = Some(password.into());
        self
    }
    
    pub fn database(mut self, database: impl Into<String>) -> Self {
        self.config.database = Some(database.into());
        self
    }
    
    pub fn build(self) -> Result<DatabaseConfig, ConfigError> {
        match (self.config.host, self.config.port, self.config.username, 
               self.config.password, self.config.database) {
            (Some(host), Some(port), Some(username), Some(password), Some(database)) => {
                Ok(DatabaseConfig {
                    host: Some(host),
                    port: Some(port),
                    username: Some(username),
                    password: Some(password),
                    database: Some(database),
                })
            }
            _ => Err(ConfigError::MissingFields),
        }
    }
}

#[derive(Debug)]
pub enum ConfigError {
    MissingFields,
}

// 策略模式
pub trait SortStrategy<T> {
    fn sort(&self, data: &mut [T]);
}

pub struct BubbleSort;
pub struct QuickSort;
pub struct MergeSort;

impl<T: Ord> SortStrategy<T> for BubbleSort {
    fn sort(&self, data: &mut [T]) {
        let len = data.len();
        for i in 0..len {
            for j in 0..len - 1 - i {
                if data[j] > data[j + 1] {
                    data.swap(j, j + 1);
                }
            }
        }
    }
}

impl<T: Ord> SortStrategy<T> for QuickSort {
    fn sort(&self, data: &mut [T]) {
        if data.len() <= 1 {
            return;
        }
        // 快速排序实现
        let pivot_index = partition(data);
        let (left, right) = data.split_at_mut(pivot_index);
        self.sort(left);
        self.sort(&mut right[1..]);
    }
}

fn partition<T: Ord>(data: &mut [T]) -> usize {
    let len = data.len();
    let pivot_index = len - 1;
    let mut store_index = 0;
    
    for i in 0..len - 1 {
        if data[i] <= data[pivot_index] {
            data.swap(i, store_index);
            store_index += 1;
        }
    }
    
    data.swap(store_index, pivot_index);
    store_index
}

// 上下文使用策略
pub struct Sorter<T, S: SortStrategy<T>> {
    strategy: S,
    _phantom: std::marker::PhantomData<T>,
}

impl<T, S: SortStrategy<T>> Sorter<T, S> {
    pub fn new(strategy: S) -> Self {
        Self {
            strategy,
            _phantom: std::marker::PhantomData,
        }
    }
    
    pub fn sort(&self, data: &mut [T]) {
        self.strategy.sort(data);
    }
}
```

## 测试驱动开发

### 单元测试

```haskell
-- QuickCheck属性测试
import Test.QuickCheck

-- 要测试的函数
reverse' :: [a] -> [a]
reverse' [] = []
reverse' (x:xs) = reverse' xs ++ [x]

-- 属性测试
prop_reverseReverse :: [Int] -> Bool
prop_reverseReverse xs = reverse' (reverse' xs) == xs

prop_reverseLength :: [Int] -> Bool  
prop_reverseLength xs = length (reverse' xs) == length xs

prop_reverseHead :: [Int] -> Property
prop_reverseHead xs = not (null xs) ==> 
  head (reverse' xs) == last xs

-- 自定义生成器
newtype SortedList a = SortedList [a] deriving (Show, Eq)

instance (Ord a, Arbitrary a) => Arbitrary (SortedList a) where
  arbitrary = SortedList . sort <$> arbitrary

-- 运行测试
main :: IO ()
main = do
  quickCheck prop_reverseReverse
  quickCheck prop_reverseLength  
  quickCheck prop_reverseHead
```

```rust
// Rust单元测试和集成测试
#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    
    // 基本单元测试
    #[test]
    fn test_bubble_sort() {
        let mut data = vec![64, 34, 25, 12, 22, 11, 90];
        let sorter = Sorter::new(BubbleSort);
        sorter.sort(&mut data);
        assert_eq!(data, vec![11, 12, 22, 25, 34, 64, 90]);
    }
    
    #[test]
    fn test_empty_sort() {
        let mut data: Vec<i32> = vec![];
        let sorter = Sorter::new(QuickSort);
        sorter.sort(&mut data);
        assert!(data.is_empty());
    }
    
    // 属性测试
    proptest! {
        #[test]
        fn test_sort_preserves_length(mut data: Vec<i32>) {
            let original_len = data.len();
            let sorter = Sorter::new(QuickSort);
            sorter.sort(&mut data);
            prop_assert_eq!(data.len(), original_len);
        }
        
        #[test]
        fn test_sort_is_sorted(mut data: Vec<i32>) {
            let sorter = Sorter::new(MergeSort);
            sorter.sort(&mut data);
            prop_assert!(data.windows(2).all(|w| w[0] <= w[1]));
        }
        
        #[test]
        fn test_sort_contains_same_elements(mut data: Vec<i32>) {
            let mut original = data.clone();
            original.sort();
            
            let sorter = Sorter::new(BubbleSort);
            sorter.sort(&mut data);
            
            prop_assert_eq!(data, original);
        }
    }
    
    // 基准测试
    #[bench]
    fn bench_quick_sort(b: &mut test::Bencher) {
        let data: Vec<i32> = (0..1000).rev().collect();
        let sorter = Sorter::new(QuickSort);
        
        b.iter(|| {
            let mut test_data = data.clone();
            sorter.sort(&mut test_data);
            test_data
        });
    }
}

// 集成测试
#[test]
fn test_database_config_builder() {
    let config = DatabaseConfigBuilder::new()
        .host("localhost")
        .port(5432)
        .credentials("user", "password")
        .database("myapp")
        .build()
        .expect("Failed to build config");
    
    assert_eq!(config.host, Some("localhost".to_string()));
    assert_eq!(config.port, Some(5432));
}

// 错误情况测试
#[test]
fn test_incomplete_config_fails() {
    let result = DatabaseConfigBuilder::new()
        .host("localhost")
        .build();
    
    assert!(result.is_err());
    assert!(matches!(result, Err(ConfigError::MissingFields)));
}
```

### 行为驱动开发

```cucumber
# Cucumber特性文件 (user_management.feature)
Feature: 用户管理
  作为系统管理员
  我想要管理用户账户
  以便控制系统访问

  Background:
    Given 系统已初始化
    And 管理员已登录

  Scenario: 创建新用户
    Given 用户"john.doe@example.com"不存在
    When 我创建用户:
      | 邮箱                | john.doe@example.com |
      | 姓名                | John Doe            |
      | 角色                | 普通用户              |
    Then 用户创建成功
    And 用户"john.doe@example.com"存在于系统中

  Scenario: 删除用户
    Given 用户"jane.doe@example.com"存在
    When 我删除用户"jane.doe@example.com"
    Then 用户删除成功
    And 用户"jane.doe@example.com"不存在于系统中

  Scenario Outline: 用户输入验证
    When 我尝试创建用户邮箱为"<邮箱>"
    Then 系统应该返回"<结果>"

    Examples:
      | 邮箱                | 结果     |
      | valid@example.com   | 成功     |
      | invalid-email       | 邮箱格式错误 |
      | ""                  | 邮箱不能为空 |
```

```rust
// BDD步骤定义
use cucumber::{given, when, then, World};
use std::collections::HashMap;

#[derive(Debug, World)]
struct UserWorld {
    users: HashMap<String, User>,
    last_result: Option<Result<User, String>>,
    admin_logged_in: bool,
}

impl Default for UserWorld {
    fn default() -> Self {
        Self {
            users: HashMap::new(),
            last_result: None,
            admin_logged_in: false,
        }
    }
}

#[given("系统已初始化")]
fn system_initialized(world: &mut UserWorld) {
    // 初始化测试数据
    world.users.clear();
}

#[given("管理员已登录")]
fn admin_logged_in(world: &mut UserWorld) {
    world.admin_logged_in = true;
}

#[given(regex = r"用户\"(.*)\"不存在")]
fn user_does_not_exist(world: &mut UserWorld, email: String) {
    assert!(!world.users.contains_key(&email));
}

#[when("我创建用户:")]
fn create_user(world: &mut UserWorld, table: &cucumber::Table) {
    let row = &table.rows[0];
    let email = row[1].clone();
    let name = row[3].clone();
    let role = row[5].clone();
    
    let user = User {
        id: uuid::Uuid::new_v4().to_string(),
        email: email.clone(),
        name,
    };
    
    world.users.insert(email, user.clone());
    world.last_result = Some(Ok(user));
}

#[then("用户创建成功")]
fn user_created_successfully(world: &mut UserWorld) {
    assert!(world.last_result.as_ref().unwrap().is_ok());
}

#[then(regex = r"用户\"(.*)\"存在于系统中")]
fn user_exists_in_system(world: &mut UserWorld, email: String) {
    assert!(world.users.contains_key(&email));
}
```

## 持续集成/持续部署

### CI/CD管道

```yaml
# GitHub Actions工作流
name: CI/CD Pipeline

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

jobs:
  test:
    runs-on: ubuntu-latest
    
    strategy:
      matrix:
        rust-version: [1.70.0, stable]
        
    steps:
    - uses: actions/checkout@v3
    
    - name: Setup Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: ${{ matrix.rust-version }}
        override: true
        components: rustfmt, clippy
    
    - name: Cache dependencies
      uses: actions/cache@v3
      with:
        path: |
          ~/.cargo/registry
          ~/.cargo/git
          target
        key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}
    
    - name: Format check
      run: cargo fmt -- --check
    
    - name: Lint
      run: cargo clippy -- -D warnings
    
    - name: Test
      run: cargo test --verbose
    
    - name: Integration tests
      run: cargo test --test integration_tests
    
    - name: Benchmark
      run: cargo bench
      
  security:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3
    
    - name: Security audit
      uses: actions-rs/audit@v1
      
    - name: Dependency check
      run: |
        cargo install cargo-deny
        cargo deny check
        
  build:
    needs: [test, security]
    runs-on: ubuntu-latest
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Build Docker image
      run: |
        docker build -t myapp:${{ github.sha }} .
        docker build -t myapp:latest .
    
    - name: Push to registry
      if: github.ref == 'refs/heads/main'
      run: |
        echo ${{ secrets.DOCKER_PASSWORD }} | docker login -u ${{ secrets.DOCKER_USERNAME }} --password-stdin
        docker push myapp:${{ github.sha }}
        docker push myapp:latest
        
  deploy:
    needs: build
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    
    steps:
    - name: Deploy to staging
      run: |
        # 部署到测试环境
        kubectl set image deployment/myapp-staging myapp=myapp:${{ github.sha }}
        kubectl rollout status deployment/myapp-staging
    
    - name: Run smoke tests
      run: |
        # 运行冒烟测试
        curl -f http://staging.myapp.com/health || exit 1
    
    - name: Deploy to production
      run: |
        # 部署到生产环境
        kubectl set image deployment/myapp-prod myapp=myapp:${{ github.sha }}
        kubectl rollout status deployment/myapp-prod
```

## 代码质量保证

### 静态分析

```haskell
-- HLint配置
{-# ANN module "HLint: ignore Use camelCase" #-}

-- 代码质量规则
import qualified Data.List as L

-- 好的实践：使用具体类型
getUserName :: User -> Text
getUserName = name

-- 避免：过于通用的类型
-- getField :: a -> b  -- 太通用

-- 好的实践：使用newtype包装
newtype UserId = UserId Text

-- 避免：直接使用基本类型  
-- type UserId = Text  -- 容易混淆

-- 好的实践：使用模式匹配
processResult :: Either Error Success -> IO ()
processResult (Left err) = putStrLn $ "Error: " <> show err
processResult (Right success) = putStrLn $ "Success: " <> show success

-- 代码复杂度分析
calculateComplexity :: AST -> Int
calculateComplexity ast = case ast of
  If _ then_ else_ -> 1 + calculateComplexity then_ + calculateComplexity else_
  While _ body -> 1 + calculateComplexity body
  For _ _ body -> 1 + calculateComplexity body
  Sequence stmts -> sum $ map calculateComplexity stmts
  _ -> 0
```

```rust
// Clippy配置和代码质量
#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![allow(clippy::module_name_repetitions)]

use std::collections::HashMap;

// 好的实践：错误处理
pub fn divide(a: f64, b: f64) -> Result<f64, DivisionError> {
    if b == 0.0 {
        Err(DivisionError::DivideByZero)
    } else {
        Ok(a / b)
    }
}

#[derive(Debug, thiserror::Error)]
pub enum DivisionError {
    #[error("Cannot divide by zero")]
    DivideByZero,
}

// 避免：unwrap和panic
// let result = risky_operation().unwrap(); // 不好

// 好的实践：使用Result和?操作符
pub fn complex_operation() -> Result<String, Box<dyn std::error::Error>> {
    let data = fetch_data()?;
    let processed = process_data(data)?;
    let formatted = format_output(processed)?;
    Ok(formatted)
}

// 内存安全和性能
pub fn efficient_string_processing(items: &[String]) -> String {
    // 预分配容量避免重复分配
    let capacity = items.iter().map(String::len).sum::<usize>() + items.len();
    let mut result = String::with_capacity(capacity);
    
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            result.push(',');
        }
        result.push_str(item);
    }
    
    result
}

// 生命周期和借用检查
pub struct DataProcessor<'a> {
    data: &'a [u8],
    config: &'a ProcessorConfig,
}

impl<'a> DataProcessor<'a> {
    pub fn new(data: &'a [u8], config: &'a ProcessorConfig) -> Self {
        Self { data, config }
    }
    
    pub fn process(&self) -> ProcessResult {
        // 安全的数据处理，无需克隆
        ProcessResult {
            bytes_processed: self.data.len(),
            checksum: calculate_checksum(self.data),
        }
    }
}
```

## 形式化验证

```lean
-- 软件规约的形式化验证
structure SoftwareSystem where
  components : Set Component
  interfaces : Component → Set Interface
  dependencies : Component → Component → Prop

-- 系统不变量
def SystemInvariant (sys : SoftwareSystem) : Prop :=
  -- 组件隔离：组件只能通过接口通信
  ∀ c1 c2, sys.dependencies c1 c2 → 
    ∃ i ∈ sys.interfaces c2, communicates_through c1 c2 i

-- 安全属性
def SecurityProperty (sys : SoftwareSystem) : Prop :=
  ∀ c1 c2, sys.dependencies c1 c2 → 
    security_level c1 ≤ security_level c2

-- 性能属性  
def PerformanceProperty (sys : SoftwareSystem) (load : Load) : Prop :=
  response_time sys load ≤ max_response_time ∧
  throughput sys load ≥ min_throughput

-- 正确性证明
theorem system_correctness (sys : SoftwareSystem) 
  (h1 : SystemInvariant sys)
  (h2 : SecurityProperty sys)
  (h3 : ∀ load, PerformanceProperty sys load) :
  correct_system sys :=
by
  constructor
  · exact h1
  · exact h2  
  · exact h3

-- 测试覆盖率形式化
def TestCoverage (tests : Set Test) (code : Program) : ℝ :=
  (executed_lines tests code).card / code.total_lines.card

theorem adequate_testing (tests : Set Test) (code : Program)
  (h : TestCoverage tests code ≥ 0.8) :
  high_confidence_correctness code :=
sorry
```

## 文档与知识管理

### 文档即代码

```markdown
# API文档生成

## 用户API

### 创建用户

```http
POST /api/users
Content-Type: application/json

{
  "email": "user@example.com",
  "name": "John Doe",
  "role": "user"
}
```

**响应:**

```json
{
  "id": "uuid",
  "email": "user@example.com", 
  "name": "John Doe",
  "role": "user",
  "created_at": "2024-01-01T00:00:00Z"
}
```

**错误码:**

- `400` - 请求格式错误
- `409` - 用户已存在
- `422` - 验证失败

```rust
// 自动生成API文档
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

/// 创建用户请求
#[derive(Debug, Serialize, Deserialize, JsonSchema)]
pub struct CreateUserRequest {
    /// 用户邮箱地址
    #[schemars(example = "user@example.com")]
    pub email: String,
    
    /// 用户姓名
    #[schemars(example = "John Doe")]
    pub name: String,
    
    /// 用户角色
    #[serde(default = "default_role")]
    pub role: UserRole,
}

/// 用户角色枚举
#[derive(Debug, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "lowercase")]
pub enum UserRole {
    Admin,
    User,
    Guest,
}

fn default_role() -> UserRole {
    UserRole::User
}

// 生成OpenAPI规范
pub fn generate_openapi_spec() -> openapi::OpenApi {
    use utoipa::OpenApi;
    
    #[derive(OpenApi)]
    #[openapi(
        paths(create_user, get_user, delete_user),
        components(schemas(CreateUserRequest, User, UserRole))
    )]
    struct ApiDoc;
    
    ApiDoc::openapi()
}
```

## 团队协作与项目管理

### 敏捷开发实践

```yaml
# 项目配置文件
project:
  name: "UserManagementSystem"
  version: "1.0.0"
  
team:
  product_owner: "alice@company.com"
  scrum_master: "bob@company.com"
  developers:
    - "charlie@company.com"
    - "diana@company.com"

sprints:
  duration: "2 weeks"
  current: 5
  
definition_of_done:
  - "代码审查通过"
  - "所有测试通过"
  - "文档更新"
  - "性能基准满足要求"
  - "安全扫描通过"

story_points:
  small: 1-3
  medium: 5-8
  large: 13-21
```

### 代码审查流程

```markdown
# 代码审查清单

## 功能性
- [ ] 代码实现了需求规范
- [ ] 边界条件处理正确
- [ ] 错误处理适当
- [ ] 性能满足要求

## 代码质量
- [ ] 命名清晰有意义
- [ ] 函数职责单一
- [ ] 复杂度合理
- [ ] 无重复代码

## 安全性
- [ ] 输入验证
- [ ] 权限检查
- [ ] 敏感信息保护
- [ ] SQL注入防护

## 测试
- [ ] 单元测试覆盖
- [ ] 集成测试
- [ ] 边界条件测试
- [ ] 性能测试

## 文档
- [ ] 代码注释
- [ ] API文档
- [ ] 变更日志
- [ ] 部署说明
```

## 总结

现代软件工程强调：

1. **类型安全**: 通过类型系统防止错误
2. **测试驱动**: 确保代码质量和可靠性
3. **自动化**: CI/CD管道自动化构建和部署
4. **形式化验证**: 数学证明确保正确性
5. **协作**: 团队协作和知识共享
6. **持续改进**: 基于反馈的迭代开发

函数式编程和形式方法为软件工程提供了强大的理论基础和实践工具，帮助构建更可靠、更可维护的软件系统。
