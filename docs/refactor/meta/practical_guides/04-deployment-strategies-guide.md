# Lean与Haskell部署策略实用指南

## 🎯 概述

本文档提供Lean和Haskell编程语言的部署策略实用指南，涵盖容器化部署、云平台部署、持续集成/持续部署(CI/CD)、监控和日志管理等方面的最佳实践和实用技巧。

## 🐳 容器化部署

### 1. Haskell容器化部署

#### 1.1 Dockerfile优化

```dockerfile
# 多阶段构建的Haskell Dockerfile
FROM haskell:9.4 as builder

WORKDIR /app
COPY package.yaml stack.yaml ./
COPY app app/
COPY src src/
COPY test test/

RUN stack build --dependencies-only
RUN stack build --copy-bins

FROM ubuntu:22.04

RUN apt-get update && apt-get install -y \
    ca-certificates \
    libgmp-dev \
    && rm -rf /var/lib/apt/lists/*

RUN useradd -m -u 1000 appuser
WORKDIR /app

COPY --from=builder /root/.local/bin/app /app/app
COPY config config/

RUN chown -R appuser:appuser /app
USER appuser

EXPOSE 8080

HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/health || exit 1

CMD ["./app"]
```

#### 1.2 Docker Compose配置

```yaml
version: '3.8'

services:
  app:
    build: .
    ports:
      - "8080:8080"
    environment:
      - DATABASE_URL=postgresql://user:password@db:5432/app
      - REDIS_URL=redis://redis:6379
      - LOG_LEVEL=INFO
    depends_on:
      - db
      - redis
    volumes:
      - ./logs:/app/logs
    restart: unless-stopped
    networks:
      - app-network

  db:
    image: postgres:15
    environment:
      - POSTGRES_DB=app
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=password
    volumes:
      - postgres_data:/var/lib/postgresql/data
    ports:
      - "5432:5432"
    networks:
      - app-network

  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis_data:/data
    networks:
      - app-network

volumes:
  postgres_data:
  redis_data:

networks:
  app-network:
    driver: bridge
```

### 2. Lean容器化部署

#### 2.1 Lean Dockerfile

```dockerfile
FROM leanprover/lean4:latest as builder

WORKDIR /app
COPY leanpkg.toml ./
COPY src src/
COPY test test/

RUN lean --make src/Main.lean

FROM ubuntu:22.04

RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

RUN useradd -m -u 1000 appuser
WORKDIR /app

COPY --from=builder /app/build/bin/Main /app/app
COPY config config/

RUN chown -R appuser:appuser /app
USER appuser

EXPOSE 8080

HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/health || exit 1

CMD ["./app"]
```

## ☁️ 云平台部署

### 1. Kubernetes部署

#### 1.1 Kubernetes配置文件

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: haskell-app
  labels:
    app: haskell-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: haskell-app
  template:
    metadata:
      labels:
        app: haskell-app
    spec:
      containers:
      - name: app
        image: haskell-app:latest
        ports:
        - containerPort: 8080
        env:
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: app-secrets
              key: database-url
        - name: REDIS_URL
          value: "redis://redis-service:6379"
        - name: LOG_LEVEL
          value: "INFO"
        resources:
          requests:
            memory: "256Mi"
            cpu: "250m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5

---
apiVersion: v1
kind: Service
metadata:
  name: haskell-app-service
spec:
  selector:
    app: haskell-app
  ports:
  - protocol: TCP
    port: 80
    targetPort: 8080
  type: LoadBalancer
```

### 2. AWS部署

#### 2.1 ECS部署配置

```json
{
  "family": "haskell-app",
  "networkMode": "awsvpc",
  "requiresCompatibilities": ["FARGATE"],
  "cpu": "256",
  "memory": "512",
  "executionRoleArn": "arn:aws:iam::123456789012:role/ecsTaskExecutionRole",
  "taskRoleArn": "arn:aws:iam::123456789012:role/ecsTaskRole",
  "containerDefinitions": [
    {
      "name": "haskell-app",
      "image": "123456789012.dkr.ecr.us-west-2.amazonaws.com/haskell-app:latest",
      "portMappings": [
        {
          "containerPort": 8080,
          "protocol": "tcp"
        }
      ],
      "environment": [
        {
          "name": "LOG_LEVEL",
          "value": "INFO"
        }
      ],
      "secrets": [
        {
          "name": "DATABASE_URL",
          "valueFrom": "arn:aws:secretsmanager:us-west-2:123456789012:secret:app/database-url"
        }
      ],
      "logConfiguration": {
        "logDriver": "awslogs",
        "options": {
          "awslogs-group": "/ecs/haskell-app",
          "awslogs-region": "us-west-2",
          "awslogs-stream-prefix": "ecs"
        }
      },
      "healthCheck": {
        "command": ["CMD-SHELL", "curl -f http://localhost:8080/health || exit 1"],
        "interval": 30,
        "timeout": 5,
        "retries": 3,
        "startPeriod": 60
      }
    }
  ]
}
```

## 🔄 持续集成/持续部署

### 1. GitHub Actions配置

#### 1.1 Haskell CI/CD流水线

```yaml
name: Haskell CI/CD

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

jobs:
  test:
    runs-on: ubuntu-latest
    
    services:
      postgres:
        image: postgres:15
        env:
          POSTGRES_PASSWORD: postgres
          POSTGRES_DB: test_db
        options: >-
          --health-cmd pg_isready
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5
        ports:
          - 5432:5432
      
      redis:
        image: redis:7-alpine
        options: >-
          --health-cmd "redis-cli ping"
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5
        ports:
          - 6379:6379

    steps:
    - uses: actions/checkout@v4
    
    - name: Setup Haskell
      uses: haskell/actions/setup@v2
      with:
        ghc-version: '9.4'
        cabal-version: '3.10'
    
    - name: Cache dependencies
      uses: actions/cache@v3
      with:
        path: |
          ~/.cabal/packages
          ~/.cabal/store
          dist-newstyle
        key: ${{ runner.os }}-${{ hashFiles('**/*.cabal') }}
        restore-keys: |
          ${{ runner.os }}-
    
    - name: Install dependencies
      run: cabal update && cabal build --only-dependencies
    
    - name: Run tests
      run: cabal test
      env:
        DATABASE_URL: postgresql://postgres:postgres@localhost:5432/test_db
        REDIS_URL: redis://localhost:6379
    
    - name: Run linting
      run: |
        cabal install hlint
        hlint src/

  build:
    needs: test
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    
    steps:
    - uses: actions/checkout@v4
    
    - name: Setup Docker Buildx
      uses: docker/setup-buildx-action@v3
    
    - name: Login to ECR
      uses: aws-actions/amazon-ecr-login@v2
    
    - name: Build and push Docker image
      uses: docker/build-push-action@v5
      with:
        context: .
        push: true
        tags: |
          ${{ steps.ecr.outputs.registry }}/haskell-app:${{ github.sha }}
          ${{ steps.ecr.outputs.registry }}/haskell-app:latest
        cache-from: type=gha
        cache-to: type=gha,mode=max

  deploy:
    needs: build
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    
    steps:
    - uses: actions/checkout@v4
    
    - name: Configure AWS credentials
      uses: aws-actions/configure-aws-credentials@v4
      with:
        aws-access-key-id: ${{ secrets.AWS_ACCESS_KEY_ID }}
        aws-secret-access-key: ${{ secrets.AWS_SECRET_ACCESS_KEY }}
        aws-region: us-west-2
    
    - name: Update ECS service
      run: |
        aws ecs update-service \
          --cluster haskell-app-cluster \
          --service haskell-app-service \
          --force-new-deployment
    
    - name: Wait for deployment
      run: |
        aws ecs wait services-stable \
          --cluster haskell-app-cluster \
          --services haskell-app-service
```

#### 1.2 Lean CI/CD流水线

```yaml
name: Lean CI/CD

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

jobs:
  test:
    runs-on: ubuntu-latest
    
    steps:
    - uses: actions/checkout@v4
    
    - name: Setup Lean
      uses: leanprover/lean4-action@v1
      with:
        lean-version: 'leanprover/lean4:nightly'
    
    - name: Build project
      run: lean --make src/Main.lean
    
    - name: Run tests
      run: lean --make test/
    
    - name: Check proofs
      run: lean --make src/Proofs.lean

  build:
    needs: test
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    
    steps:
    - uses: actions/checkout@v4
    
    - name: Setup Docker Buildx
      uses: docker/setup-buildx-action@v3
    
    - name: Login to ECR
      uses: aws-actions/amazon-ecr-login@v2
    
    - name: Build and push Docker image
      uses: docker/build-push-action@v5
      with:
        context: .
        push: true
        tags: |
          ${{ steps.ecr.outputs.registry }}/lean-app:${{ github.sha }}
          ${{ steps.ecr.outputs.registry }}/lean-app:latest
        cache-from: type=gha
        cache-to: type=gha,mode=max

  deploy:
    needs: build
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    
    steps:
    - uses: actions/checkout@v4
    
    - name: Configure AWS credentials
      uses: aws-actions/configure-aws-credentials@v4
      with:
        aws-access-key-id: ${{ secrets.AWS_ACCESS_KEY_ID }}
        aws-secret-access-key: ${{ secrets.AWS_SECRET_ACCESS_KEY }}
        aws-region: us-west-2
    
    - name: Deploy to ECS
      run: |
        aws ecs update-service \
          --cluster lean-app-cluster \
          --service lean-app-service \
          --force-new-deployment
```

## 📊 监控和日志管理

### 1. 应用监控

#### 1.1 Prometheus指标收集

```haskell
-- Prometheus指标收集
module Metrics where

import Prometheus
import Prometheus.Metric.Gauge
import Prometheus.Metric.Counter
import Prometheus.Metric.Histogram
import Data.Time

-- 应用指标
data AppMetrics = AppMetrics
    { requestCounter :: Counter
    , requestDuration :: Histogram
    , activeConnections :: Gauge
    , errorCounter :: Counter
    , memoryUsage :: Gauge
    }

-- 创建指标
createMetrics :: IO AppMetrics
createMetrics = do
    reqCounter <- counter (Info "http_requests_total" "Total HTTP requests")
    reqDuration <- histogram (Info "http_request_duration_seconds" "HTTP request duration")
        [0.1, 0.5, 1.0, 2.0, 5.0]
    activeConn <- gauge (Info "http_active_connections" "Active HTTP connections")
    errCounter <- counter (Info "http_errors_total" "Total HTTP errors")
    memUsage <- gauge (Info "app_memory_bytes" "Application memory usage")
    
    return AppMetrics
        { requestCounter = reqCounter
        , requestDuration = reqDuration
        , activeConnections = activeConn
        , errorCounter = errCounter
        , memoryUsage = memUsage
        }

-- 指标中间件
metricsMiddleware :: AppMetrics -> Middleware
metricsMiddleware metrics app request respond = do
    startTime <- getCurrentTime
    
    -- 增加请求计数
    incCounter (requestCounter metrics)
    
    -- 增加活跃连接数
    incGauge (activeConnections metrics)
    
    app request $ \response -> do
        -- 减少活跃连接数
        decGauge (activeConnections metrics)
        
        -- 记录请求持续时间
        endTime <- getCurrentTime
        let duration = diffUTCTime endTime startTime
        observeHistogram (requestDuration metrics) (realToFrac duration)
        
        -- 记录错误
        when (statusCode response >= 400) $
            incCounter (errorCounter metrics)
        
        respond response

-- 指标端点
metricsEndpoint :: AppMetrics -> Application
metricsEndpoint metrics request respond = do
    case pathInfo request of
        ["metrics"] -> do
            metricsText <- exportMetricsAsText
            respond $ responseLBS
                status200
                [("Content-Type", "text/plain; version=0.0.4")]
                metricsText
        _ -> respond $ responseLBS status404 [] "Not found"
```

#### 1.2 健康检查端点

```haskell
-- 健康检查
module HealthCheck where

import Network.HTTP.Types
import Network.Wai
import Data.Aeson
import Data.Time

-- 健康状态
data HealthStatus = HealthStatus
    { status :: String
    , timestamp :: UTCTime
    , version :: String
    , uptime :: NominalDiffTime
    , checks :: [HealthCheck]
    }

data HealthCheck = HealthCheck
    { name :: String
    , status :: String
    , message :: Maybe String
    }

instance ToJSON HealthStatus where
    toJSON HealthStatus{..} = object
        [ "status" .= status
        , "timestamp" .= timestamp
        , "version" .= version
        , "uptime" .= uptime
        , "checks" .= checks
        ]

instance ToJSON HealthCheck where
    toJSON HealthCheck{..} = object
        [ "name" .= name
        , "status" .= status
        , "message" .= message
        ]

-- 健康检查函数
type HealthChecker = IO HealthCheck

-- 数据库健康检查
databaseHealthCheck :: HealthChecker
databaseHealthCheck = do
    result <- checkDatabaseConnection
    case result of
        Right _ -> return HealthCheck
            { name = "database"
            , status = "healthy"
            , message = Nothing
            }
        Left err -> return HealthCheck
            { name = "database"
            , status = "unhealthy"
            , message = Just err
            }

-- 健康检查端点
healthCheckEndpoint :: [HealthChecker] -> Application
healthCheckEndpoint checkers request respond = do
    case pathInfo request of
        ["health"] -> do
            startTime <- getCurrentTime
            checks <- mapM ($) checkers
            
            let allHealthy = all (\check -> status check == "healthy") checks
            let overallStatus = if allHealthy then "healthy" else "unhealthy"
            let statusCode = if allHealthy then status200 else status503
            
            healthStatus <- HealthStatus
                <$> return overallStatus
                <*> getCurrentTime
                <*> return "1.0.0"
                <*> return (diffUTCTime startTime startTime)
                <*> return checks
            
            respond $ responseLBS
                statusCode
                [("Content-Type", "application/json")]
                (encode healthStatus)
        
        ["ready"] -> do
            respond $ responseLBS status200 [] "ready"
        
        _ -> respond $ responseLBS status404 [] "Not found"
```

### 2. 日志管理

#### 2.1 结构化日志

```haskell
-- 结构化日志
module Logging where

import Data.Aeson
import Data.Text (Text)
import Data.Time
import System.Log.FastLogger
import Control.Monad.IO.Class

-- 日志级别
data LogLevel = Debug | Info | Warn | Error
    deriving (Show, Eq, Ord)

-- 日志条目
data LogEntry = LogEntry
    { timestamp :: UTCTime
    , level :: LogLevel
    , message :: Text
    , fields :: [(Text, Value)]
    , traceId :: Maybe Text
    , userId :: Maybe Text
    }

instance ToJSON LogLevel where
    toJSON Debug = String "debug"
    toJSON Info = String "info"
    toJSON Warn = String "warn"
    toJSON Error = String "error"

instance ToJSON LogEntry where
    toJSON LogEntry{..} = object
        [ "timestamp" .= timestamp
        , "level" .= level
        , "message" .= message
        , "fields" .= object fields
        , "traceId" .= traceId
        , "userId" .= userId
        ]

-- 日志记录器
data Logger = Logger
    { logger :: FastLogger
    , minLevel :: LogLevel
    }

-- 创建日志记录器
createLogger :: LogLevel -> IO Logger
createLogger minLevel = do
    logger <- newFastLogger (LogStdout defaultBufSize)
    return Logger { logger = logger, minLevel = minLevel }

-- 记录日志
logMessage :: (MonadIO m) => Logger -> LogLevel -> Text -> [(Text, Value)] -> m ()
logMessage Logger{..} level message fields = when (level >= minLevel) $ do
    timestamp <- liftIO getCurrentTime
    let entry = LogEntry
            { timestamp = timestamp
            , level = level
            , message = message
            , fields = fields
            , traceId = Nothing
            , userId = Nothing
            }
    liftIO $ logger $ toLogStr $ encode entry <> "\n"

-- 便捷函数
logDebug :: (MonadIO m) => Logger -> Text -> [(Text, Value)] -> m ()
logDebug logger = logMessage logger Debug

logInfo :: (MonadIO m) => Logger -> Text -> [(Text, Value)] -> m ()
logInfo logger = logMessage logger Info

logWarn :: (MonadIO m) => Logger -> Text -> [(Text, Value)] -> m ()
logWarn logger = logMessage logger Warn

logError :: (MonadIO m) => Logger -> Text -> [(Text, Value)] -> m ()
logError logger = logMessage logger Error

-- 请求日志中间件
requestLoggingMiddleware :: Logger -> Middleware
requestLoggingMiddleware logger app request respond = do
    startTime <- getCurrentTime
    
    logInfo logger "Request started"
        [ ("method", String $ pack $ show $ requestMethod request)
        , ("path", String $ pack $ show $ pathInfo request)
        , ("userAgent", String $ pack $ show $ lookup "User-Agent" (requestHeaders request))
        ]
    
    app request $ \response -> do
        endTime <- getCurrentTime
        let duration = diffUTCTime endTime startTime
        
        logInfo logger "Request completed"
            [ ("method", String $ pack $ show $ requestMethod request)
            , ("path", String $ pack $ show $ pathInfo request)
            , ("status", Number $ fromIntegral $ statusCode response)
            , ("duration", Number $ realToFrac duration)
            ]
        
        respond response
```

## 🎯 最佳实践总结

### 1. 部署原则

1. **自动化部署**：使用CI/CD流水线自动化部署过程
2. **蓝绿部署**：使用蓝绿部署策略减少停机时间
3. **滚动更新**：使用滚动更新策略确保服务可用性
4. **回滚策略**：制定快速回滚策略应对部署问题

### 2. 监控原则

1. **全面监控**：监控应用、基础设施和业务指标
2. **告警机制**：设置合理的告警阈值和通知机制
3. **日志聚合**：使用集中式日志管理系统
4. **性能分析**：定期分析性能瓶颈和优化机会

### 3. 安全原则

1. **最小权限**：使用最小权限原则配置访问控制
2. **密钥管理**：使用安全的密钥管理系统
3. **网络安全**：配置适当的网络安全策略
4. **漏洞扫描**：定期进行安全漏洞扫描

### 4. 可扩展性原则

1. **水平扩展**：设计支持水平扩展的架构
2. **负载均衡**：使用负载均衡器分发流量
3. **缓存策略**：实施适当的缓存策略
4. **数据库优化**：优化数据库性能和连接池

通过遵循这些最佳实践，可以构建可靠、安全、可扩展的部署系统。 