# 微服务监控 - 形式化理论与Haskell实现

## 📋 概述

微服务监控关注系统的可观测性、性能指标收集和故障诊断。本文档从形式化角度分析微服务监控机制，并提供Haskell实现。

## 🎯 核心概念

### 监控的形式化模型

#### 定义 1.1 (监控系统)
监控系统定义为：
$$\text{Monitoring} = (M, L, T, \text{collect}, \text{analyze}, \text{alert})$$

其中：
- $M$ 是指标类型
- $L$ 是日志类型
- $T$ 是追踪类型

#### 定义 1.2 (可观测性)
可观测性定义为：
$$\text{Observability} = \text{Metrics} \times \text{Logs} \times \text{Traces}$$

## 📊 指标监控

### 指标收集

#### 定义 2.1 (指标)
指标定义为：
$$\text{Metric} = (N, V, T, \text{tags})$$

其中：
- $N$ 是指标名称
- $V$ 是指标值
- $T$ 是时间戳
- $\text{tags}$ 是标签集合

### Haskell实现

```haskell
-- 指标类型
data Metric = Metric
    { name :: String
    , value :: Double
    , timestamp :: UTCTime
    , tags :: Map String String
    , metricType :: MetricType
    }

data MetricType = Counter | Gauge | Histogram | Summary

-- 指标收集器
class MetricCollector c where
    type MetricType c
    collect :: c -> IO [MetricType c]
    aggregate :: c -> TimeRange -> AggregationFunction -> IO Double

-- 计数器
data Counter = Counter
    { counterName :: String
    , counterValue :: MVar Double
    , counterTags :: Map String String
    }

-- 创建计数器
newCounter :: String -> Map String String -> IO Counter
newCounter name tags = do
    value <- newMVar 0.0
    return $ Counter name value tags

-- 增加计数器
incrementCounter :: Counter -> Double -> IO ()
incrementCounter counter delta = do
    modifyMVar_ (counterValue counter) (return . (+ delta))

-- 获取计数器值
getCounterValue :: Counter -> IO Double
getCounterValue counter = readMVar (counterValue counter)

-- 仪表盘
data Gauge = Gauge
    { gaugeName :: String
    , gaugeValue :: MVar Double
    , gaugeTags :: Map String String
    }

-- 创建仪表盘
newGauge :: String -> Map String String -> IO Gauge
newGauge name tags = do
    value <- newMVar 0.0
    return $ Gauge name value tags

-- 设置仪表盘值
setGaugeValue :: Gauge -> Double -> IO ()
setGaugeValue gauge value = do
    putMVar (gaugeValue gauge) value

-- 增加仪表盘值
incrementGauge :: Gauge -> Double -> IO ()
incrementGauge gauge delta = do
    modifyMVar_ (gaugeValue gauge) (return . (+ delta))

-- 减少仪表盘值
decrementGauge :: Gauge -> Double -> IO ()
decrementGauge gauge delta = do
    modifyMVar_ (gaugeValue gauge) (return . subtract delta)

-- 直方图
data Histogram = Histogram
    { histogramName :: String
    , histogramBuckets :: MVar [Double]
    , histogramCount :: MVar Int
    , histogramSum :: MVar Double
    , histogramTags :: Map String String
    }

-- 创建直方图
newHistogram :: String -> [Double] -> Map String String -> IO Histogram
newHistogram name buckets tags = do
    bucketsVar <- newMVar buckets
    count <- newMVar 0
    sum <- newMVar 0.0
    return $ Histogram name bucketsVar count sum tags

-- 观察值
observeHistogram :: Histogram -> Double -> IO ()
observeHistogram histogram value = do
    modifyMVar_ (histogramCount histogram) (return . (+ 1))
    modifyMVar_ (histogramSum histogram) (return . (+ value))

-- 获取直方图统计
getHistogramStats :: Histogram -> IO (Int, Double, Double)
getHistogramStats histogram = do
    count <- readMVar (histogramCount histogram)
    sum <- readMVar (histogramSum histogram)
    let average = if count > 0 then sum / fromIntegral count else 0.0
    return (count, sum, average)

-- 指标注册表
data MetricRegistry = MetricRegistry
    { counters :: MVar (Map String Counter)
    , gauges :: MVar (Map String Gauge)
    , histograms :: MVar (Map String Histogram)
    }

-- 创建指标注册表
newMetricRegistry :: IO MetricRegistry
newMetricRegistry = do
    counters <- newMVar Map.empty
    gauges <- newMVar Map.empty
    histograms <- newMVar Map.empty
    return $ MetricRegistry counters gauges histograms

-- 注册计数器
registerCounter :: MetricRegistry -> String -> Map String String -> IO Counter
registerCounter registry name tags = do
    counter <- newCounter name tags
    modifyMVar_ (counters registry) (return . Map.insert name counter)
    return counter

-- 注册仪表盘
registerGauge :: MetricRegistry -> String -> Map String String -> IO Gauge
registerGauge registry name tags = do
    gauge <- newGauge name tags
    modifyMVar_ (gauges registry) (return . Map.insert name gauge)
    return gauge

-- 注册直方图
registerHistogram :: MetricRegistry -> String -> [Double] -> Map String String -> IO Histogram
registerHistogram registry name buckets tags = do
    histogram <- newHistogram name buckets tags
    modifyMVar_ (histograms registry) (return . Map.insert name histogram)
    return histogram

-- 收集所有指标
collectAllMetrics :: MetricRegistry -> IO [Metric]
collectAllMetrics registry = do
    now <- getCurrentTime
    
    -- 收集计数器
    currentCounters <- readMVar (counters registry)
    counterMetrics <- mapM (\(name, counter) -> do
        value <- getCounterValue counter
        return $ Metric name value now (counterTags counter) Counter
    ) $ Map.toList currentCounters
    
    -- 收集仪表盘
    currentGauges <- readMVar (gauges registry)
    gaugeMetrics <- mapM (\(name, gauge) -> do
        value <- readMVar (gaugeValue gauge)
        return $ Metric name value now (gaugeTags gauge) Gauge
    ) $ Map.toList currentGauges
    
    -- 收集直方图
    currentHistograms <- readMVar (histograms registry)
    histogramMetrics <- mapM (\(name, histogram) -> do
        (count, sum, avg) <- getHistogramStats histogram
        return $ Metric (name ++ ".count") (fromIntegral count) now (histogramTags histogram) Histogram
    ) $ Map.toList currentHistograms
    
    return $ counterMetrics ++ gaugeMetrics ++ histogramMetrics

-- 使用示例
exampleMetrics :: IO ()
exampleMetrics = do
    registry <- newMetricRegistry
    
    -- 注册指标
    requestCounter <- registerCounter registry "http_requests_total" (Map.singleton "service" "user-service")
    responseTimeHistogram <- registerHistogram registry "http_response_time_seconds" [0.1, 0.5, 1.0, 2.0, 5.0] (Map.singleton "service" "user-service")
    activeConnectionsGauge <- registerGauge registry "active_connections" (Map.singleton "service" "user-service")
    
    -- 模拟请求
    replicateM_ 10 $ do
        incrementCounter requestCounter 1
        responseTime <- randomRIO (0.1, 3.0)
        observeHistogram responseTimeHistogram responseTime
        incrementGauge activeConnectionsGauge 1
        threadDelay 100000  -- 100ms
        decrementGauge activeConnectionsGauge 1
    
    -- 收集指标
    metrics <- collectAllMetrics registry
    mapM_ (\metric -> putStrLn $ show metric) metrics
```

### 形式化证明

#### 定理 2.1 (指标的单调性)
对于计数器 $C$：
$$\text{increment}(C, v_1) \land \text{increment}(C, v_2) \Rightarrow \text{value}(C) = v_1 + v_2$$

**证明**：
计数器只能增加，满足单调性性质。

## 📝 日志监控

### 结构化日志

#### 定义 3.1 (日志)
日志定义为：
$$\text{Log} = (L, T, \text{level}, \text{message}, \text{context})$$

其中：
- $L$ 是日志级别
- $T$ 是时间戳
- $\text{message}$ 是日志消息
- $\text{context}$ 是上下文信息

### Haskell实现

```haskell
-- 日志级别
data LogLevel = DEBUG | INFO | WARN | ERROR | FATAL

-- 日志条目
data LogEntry = LogEntry
    { timestamp :: UTCTime
    , level :: LogLevel
    , message :: String
    , context :: Map String String
    , traceId :: Maybe String
    , spanId :: Maybe String
    }

-- 日志记录器
data Logger = Logger
    { loggerName :: String
    , logLevel :: LogLevel
    , appenders :: [LogAppender]
    }

-- 日志追加器
class LogAppender a where
    append :: a -> LogEntry -> IO ()

-- 控制台追加器
data ConsoleAppender = ConsoleAppender

instance LogAppender ConsoleAppender where
    append appender entry = do
        putStrLn $ formatLogEntry entry

-- 文件追加器
data FileAppender = FileAppender
    { filePath :: String
    , fileHandle :: MVar Handle
    }

-- 创建文件追加器
newFileAppender :: String -> IO FileAppender
newFileAppender path = do
    handle <- openFile path AppendMode
    handleVar <- newMVar handle
    return $ FileAppender path handleVar

instance LogAppender FileAppender where
    append appender entry = do
        handle <- readMVar (fileHandle appender)
        hPutStrLn handle $ formatLogEntry entry
        hFlush handle

-- 格式化日志条目
formatLogEntry :: LogEntry -> String
formatLogEntry entry = 
    show (timestamp entry) ++ " [" ++ show (level entry) ++ "] " ++ 
    message entry ++ " " ++ show (context entry) ++
    maybe "" (\tid -> " traceId=" ++ tid) (traceId entry) ++
    maybe "" (\sid -> " spanId=" ++ sid) (spanId entry)

-- 创建日志记录器
newLogger :: String -> LogLevel -> [LogAppender] -> IO Logger
newLogger name level appenders = do
    return $ Logger name level appenders

-- 记录日志
logMessage :: Logger -> LogLevel -> String -> Map String String -> IO ()
logMessage logger level message context = do
    if level >= logLevel logger
    then do
        now <- getCurrentTime
        let entry = LogEntry now level message context Nothing Nothing
        mapM_ (\appender -> append appender entry) (appenders logger)
    else return ()

-- 便捷日志方法
debug :: Logger -> String -> Map String String -> IO ()
debug logger message context = logMessage logger DEBUG message context

info :: Logger -> String -> Map String String -> IO ()
info logger message context = logMessage logger INFO message context

warn :: Logger -> String -> Map String String -> IO ()
warn logger message context = logMessage logger WARN message context

error :: Logger -> String -> Map String String -> IO ()
error logger message context = logMessage logger ERROR message context

-- 结构化日志记录器
data StructuredLogger = StructuredLogger
    { logger :: Logger
    , defaultContext :: Map String String
    }

-- 创建结构化日志记录器
newStructuredLogger :: String -> LogLevel -> [LogAppender] -> Map String String -> IO StructuredLogger
newStructuredLogger name level appenders context = do
    logger <- newLogger name level appenders
    return $ StructuredLogger logger context

-- 记录结构化日志
logStructured :: StructuredLogger -> LogLevel -> String -> Map String String -> IO ()
logStructured structuredLogger level message additionalContext = do
    let combinedContext = Map.union additionalContext (defaultContext structuredLogger)
    logMessage (logger structuredLogger) level message combinedContext

-- 使用示例
exampleLogging :: IO ()
exampleLogging = do
    -- 创建控制台追加器
    let consoleAppender = ConsoleAppender
    
    -- 创建文件追加器
    fileAppender <- newFileAppender "app.log"
    
    -- 创建日志记录器
    logger <- newLogger "user-service" INFO [consoleAppender, fileAppender]
    
    -- 记录日志
    info logger "User service started" (Map.singleton "port" "8080")
    info logger "User created" (Map.fromList [("userId", "123"), ("username", "john")])
    warn logger "Database connection slow" (Map.singleton "responseTime" "2.5s")
    error logger "Failed to create user" (Map.fromList [("userId", "456"), ("error", "Validation failed")])
    
    -- 创建结构化日志记录器
    structuredLogger <- newStructuredLogger "user-service" INFO [consoleAppender] 
                        (Map.fromList [("service", "user-service"), ("version", "1.0.0")])
    
    -- 记录结构化日志
    logStructured structuredLogger INFO "User authenticated" 
                  (Map.fromList [("userId", "123"), ("method", "password")])
```

### 形式化证明

#### 定理 3.1 (日志的完整性)
对于任意日志系统：
$$\text{log}(m, l) \Rightarrow \text{persistent}(m, l)$$

**证明**：
日志系统确保所有日志消息都被持久化存储。

## 🔍 分布式追踪

### 追踪系统

#### 定义 4.1 (追踪)
追踪定义为：
$$\text{Trace} = (T, S, \text{span}, \text{context})$$

其中：
- $T$ 是追踪ID
- $S$ 是跨度集合
- $\text{span}$ 是跨度函数
- $\text{context}$ 是上下文函数

### Haskell实现

```haskell
-- 追踪ID
type TraceId = String

-- 跨度ID
type SpanId = String

-- 跨度
data Span = Span
    { spanId :: SpanId
    , traceId :: TraceId
    , parentSpanId :: Maybe SpanId
    , name :: String
    , startTime :: UTCTime
    , endTime :: Maybe UTCTime
    , tags :: Map String String
    , logs :: [LogEntry]
    }

-- 追踪上下文
data TraceContext = TraceContext
    { traceId :: TraceId
    , spanId :: SpanId
    , parentSpanId :: Maybe SpanId
    , sampled :: Bool
    }

-- 追踪器
data Tracer = Tracer
    { tracerName :: String
    , spans :: MVar [Span]
    }

-- 创建追踪器
newTracer :: String -> IO Tracer
newTracer name = do
    spans <- newMVar []
    return $ Tracer name spans

-- 开始跨度
startSpan :: Tracer -> String -> Maybe TraceContext -> IO (Span, TraceContext)
startTracer spanName maybeParentContext = do
    now <- getCurrentTime
    spanId <- generateId
    traceId <- case maybeParentContext of
        Just context -> return $ traceId context
        Nothing -> generateId
    let parentSpanId = case maybeParentContext of
            Just context -> Just $ spanId context
            Nothing -> Nothing
    
    let span = Span spanId traceId parentSpanId spanName now Nothing Map.empty []
    let context = TraceContext traceId spanId parentSpanId True
    
    modifyMVar_ (spans tracer) (return . (span :))
    return (span, context)

-- 结束跨度
endSpan :: Tracer -> Span -> IO ()
endTracer span = do
    now <- getCurrentTime
    let updatedSpan = span { endTime = Just now }
    modifyMVar_ (spans tracer) $ \currentSpans -> do
        let updatedSpans = map (\s -> if spanId s == spanId span then updatedSpan else s) currentSpans
        return updatedSpans

-- 添加标签
addSpanTag :: Span -> String -> String -> Span
addSpanTag span key value = 
    span { tags = Map.insert key value (tags span) }

-- 添加日志
addSpanLog :: Span -> LogLevel -> String -> Span
addSpanLog span level message = 
    span { logs = LogEntry (getCurrentTime) level message Map.empty Nothing Nothing : logs span }

-- 追踪中间件
data TracingMiddleware = TracingMiddleware
    { tracer :: Tracer
    , logger :: Logger
    }

-- 创建追踪中间件
newTracingMiddleware :: String -> Logger -> IO TracingMiddleware
newTracingMiddleware name logger = do
    tracer <- newTracer name
    return $ TracingMiddleware tracer logger

-- 追踪HTTP请求
traceHttpRequest :: TracingMiddleware -> String -> String -> (TraceContext -> IO a) -> IO a
traceHttpRequest middleware method path handler = do
    (span, context) <- startSpan (tracer middleware) "http.request" Nothing
    let spanWithTags = addSpanTag (addSpanTag span "http.method" method) "http.path" path
    
    -- 记录请求开始
    let spanWithLog = addSpanLog spanWithTags INFO $ "Started " ++ method ++ " " ++ path
    
    -- 执行处理器
    result <- handler context
    
    -- 记录请求结束
    let finalSpan = addSpanLog spanWithLog INFO $ "Completed " ++ method ++ " " ++ path
    endSpan (tracer middleware) finalSpan
    
    return result

-- 追踪数据库操作
traceDatabaseOperation :: TracingMiddleware -> String -> String -> (TraceContext -> IO a) -> IO a
traceDatabaseOperation middleware operation table handler = do
    (span, context) <- startSpan (tracer middleware) "database.operation" Nothing
    let spanWithTags = addSpanTag (addSpanTag span "db.operation" operation) "db.table" table
    
    -- 记录操作开始
    let spanWithLog = addSpanLog spanWithTags INFO $ "Started " ++ operation ++ " on " ++ table
    
    -- 执行处理器
    result <- handler context
    
    -- 记录操作结束
    let finalSpan = addSpanLog spanWithLog INFO $ "Completed " ++ operation ++ " on " ++ table
    endSpan (tracer middleware) finalSpan
    
    return result

-- 获取追踪
getTrace :: Tracer -> TraceId -> IO [Span]
getTrace tracer traceId = do
    currentSpans <- readMVar (spans tracer)
    return $ filter (\span -> traceId span == traceId) currentSpans

-- 使用示例
exampleTracing :: IO ()
exampleTracing = do
    -- 创建日志记录器
    logger <- newLogger "user-service" INFO [ConsoleAppender]
    
    -- 创建追踪中间件
    middleware <- newTracingMiddleware "user-service" logger
    
    -- 追踪HTTP请求
    result <- traceHttpRequest middleware "POST" "/users" $ \context -> do
        putStrLn $ "Processing request with trace ID: " ++ traceId context
        
        -- 追踪数据库操作
        user <- traceDatabaseOperation middleware "INSERT" "users" $ \dbContext -> do
            putStrLn $ "Executing database operation with trace ID: " ++ traceId dbContext
            return $ User "123" "john" "john@example.com" "hash"
        
        return user
    
    putStrLn $ "Created user: " ++ show result
    
    -- 获取追踪
    traces <- getTrace (tracer middleware) "trace-123"
    putStrLn $ "Found " ++ show (length traces) ++ " spans in trace"
```

### 形式化证明

#### 定理 4.1 (追踪的因果性)
对于任意追踪系统：
$$\text{span}_1 \rightarrow \text{span}_2 \Rightarrow \text{causal}(\text{span}_1, \text{span}_2)$$

**证明**：
追踪系统通过父子关系建立跨度的因果链。

## 🚨 告警系统

### 告警规则

#### 定义 5.1 (告警)
告警定义为：
$$\text{Alert} = (R, C, \text{condition}, \text{action})$$

其中：
- $R$ 是规则类型
- $C$ 是条件类型
- $\text{condition}$ 是条件函数
- $\text{action}$ 是动作函数

### Haskell实现

```haskell
-- 告警条件
data AlertCondition = AlertCondition
    { metricName :: String
    , threshold :: Double
    , operator :: ComparisonOperator
    , duration :: Int  -- 持续时间（秒）
    }

data ComparisonOperator = GreaterThan | LessThan | Equals | NotEquals

-- 告警动作
data AlertAction = AlertAction
    { actionType :: ActionType
    , target :: String
    , message :: String
    }

data ActionType = Email | Slack | Webhook | PagerDuty

-- 告警规则
data AlertRule = AlertRule
    { ruleId :: String
    , name :: String
    , condition :: AlertCondition
    , action :: AlertAction
    , enabled :: Bool
    }

-- 告警状态
data AlertStatus = Firing | Resolved | Pending

-- 告警实例
data AlertInstance = AlertInstance
    { ruleId :: String
    , status :: AlertStatus
    , startTime :: UTCTime
    , endTime :: Maybe UTCTime
    , value :: Double
    }

-- 告警管理器
data AlertManager = AlertManager
    { rules :: MVar [AlertRule]
    , instances :: MVar [AlertInstance]
    , actionExecutor :: ActionExecutor
    }

-- 动作执行器
data ActionExecutor = ActionExecutor
    { emailSender :: EmailSender
    , slackSender :: SlackSender
    , webhookSender :: WebhookSender
    }

-- 创建告警管理器
newAlertManager :: ActionExecutor -> IO AlertManager
newAlertManager executor = do
    rules <- newMVar []
    instances <- newMVar []
    return $ AlertManager rules instances executor

-- 添加告警规则
addAlertRule :: AlertManager -> AlertRule -> IO ()
addAlertManager rule = do
    modifyMVar_ (rules manager) (return . (rule :))

-- 检查告警条件
checkAlertCondition :: AlertCondition -> Double -> Bool
checkAlertCondition condition value = 
    case operator condition of
        GreaterThan -> value > threshold condition
        LessThan -> value < threshold condition
        Equals -> value == threshold condition
        NotEquals -> value /= threshold condition

-- 评估告警
evaluateAlert :: AlertManager -> String -> Double -> IO ()
evaluateAlert manager metricName value = do
    currentRules <- readMVar (rules manager)
    let matchingRules = filter (\rule -> 
        metricName (condition rule) == metricName && enabled rule
    ) currentRules
    
    mapM_ (\rule -> do
        let condition = condition rule
        let isFiring = checkAlertCondition condition value
        
        if isFiring
        then triggerAlert manager rule value
        else resolveAlert manager rule
    ) matchingRules

-- 触发告警
triggerAlert :: AlertManager -> AlertRule -> Double -> IO ()
triggerAlert manager rule value = do
    now <- getCurrentTime
    currentInstances <- readMVar (instances manager)
    
    -- 检查是否已经触发
    let existingInstance = find (\instance -> 
        ruleId instance == ruleId rule && status instance == Firing
    ) currentInstances
    
    case existingInstance of
        Just _ -> return ()  -- 已经触发
        Nothing -> do
            -- 创建新的告警实例
            let instance = AlertInstance (ruleId rule) Firing now Nothing value
            modifyMVar_ (instances manager) (return . (instance :))
            
            -- 执行告警动作
            executeAlertAction (actionExecutor manager) (action rule) value

-- 解决告警
resolveAlert :: AlertManager -> AlertRule -> IO ()
resolveAlert manager rule = do
    now <- getCurrentTime
    modifyMVar_ (instances manager) $ \currentInstances -> do
        let updatedInstances = map (\instance -> 
            if ruleId instance == ruleId rule && status instance == Firing
            then instance { status = Resolved, endTime = Just now }
            else instance
        ) currentInstances
        return updatedInstances

-- 执行告警动作
executeAlertAction :: ActionExecutor -> AlertAction -> Double -> IO ()
executeAlertAction executor action value = 
    case actionType action of
        Email -> sendEmail (emailSender executor) (target action) (message action)
        Slack -> sendSlack (slackSender executor) (target action) (message action)
        Webhook -> sendWebhook (webhookSender executor) (target action) (message action)
        PagerDuty -> sendPagerDuty (pagerDutySender executor) (target action) (message action)

-- 简化的动作发送器
data EmailSender = EmailSender
data SlackSender = SlackSender
data WebhookSender = WebhookSender
data PagerDutySender = PagerDutySender

sendEmail :: EmailSender -> String -> String -> IO ()
sendEmail sender target message = 
    putStrLn $ "Sending email to " ++ target ++ ": " ++ message

sendSlack :: SlackSender -> String -> String -> IO ()
sendSlack sender target message = 
    putStrLn $ "Sending Slack message to " ++ target ++ ": " ++ message

sendWebhook :: WebhookSender -> String -> String -> IO ()
sendWebhook sender target message = 
    putStrLn $ "Sending webhook to " ++ target ++ ": " ++ message

sendPagerDuty :: PagerDutySender -> String -> String -> IO ()
sendPagerDuty sender target message = 
    putStrLn $ "Sending PagerDuty alert to " ++ target ++ ": " ++ message

-- 使用示例
exampleAlerting :: IO ()
exampleAlerting = do
    -- 创建动作执行器
    let executor = ActionExecutor EmailSender SlackSender WebhookSender PagerDutySender
    
    -- 创建告警管理器
    manager <- newAlertManager executor
    
    -- 添加告警规则
    let cpuAlert = AlertRule "cpu-high" "High CPU Usage" 
                    (AlertCondition "cpu.usage" 80.0 GreaterThan 300) 
                    (AlertAction Email "admin@example.com" "CPU usage is above 80%") 
                    True
    
    let memoryAlert = AlertRule "memory-high" "High Memory Usage" 
                     (AlertCondition "memory.usage" 90.0 GreaterThan 300) 
                     (AlertAction Slack "#alerts" "Memory usage is above 90%") 
                     True
    
    addAlertRule manager cpuAlert
    addAlertRule manager memoryAlert
    
    -- 模拟指标值
    replicateM_ 5 $ do
        cpuUsage <- randomRIO (70.0, 95.0)
        memoryUsage <- randomRIO (85.0, 98.0)
        
        putStrLn $ "CPU Usage: " ++ show cpuUsage ++ "%"
        putStrLn $ "Memory Usage: " ++ show memoryUsage ++ "%"
        
        evaluateAlert manager "cpu.usage" cpuUsage
        evaluateAlert manager "memory.usage" memoryUsage
        
        threadDelay 1000000  -- 等待1秒
```

### 形式化证明

#### 定理 5.1 (告警的及时性)
对于任意告警系统：
$$\text{condition}(m) \land \text{threshold}(m) \Rightarrow \text{eventually}(\text{alert}(m))$$

**证明**：
告警系统确保满足条件的指标最终触发告警。

## 🎯 最佳实践

### 1. 监控原则

- **全面监控**：监控所有关键指标
- **分层监控**：基础设施、应用、业务分层监控
- **实时监控**：及时发现和处理问题
- **历史分析**：分析趋势和模式

### 2. 日志原则

- **结构化日志**：使用结构化格式
- **适当级别**：选择合适的日志级别
- **上下文信息**：包含足够的上下文
- **性能考虑**：避免日志影响性能

### 3. 追踪原则

- **采样策略**：合理设置采样率
- **上下文传播**：正确传播追踪上下文
- **性能影响**：最小化追踪对性能的影响
- **数据管理**：合理管理追踪数据

### 4. 告警原则

- **避免告警疲劳**：设置合理的阈值
- **分级告警**：不同级别不同处理
- **自动恢复**：支持自动恢复机制
- **告警收敛**：避免重复告警

## 🔗 相关链接

- [服务设计](../01-Service-Design/README.md)
- [服务通信](../02-Service-Communication/README.md)
- [服务治理](../03-Service-Governance/README.md)
- [微服务架构总览](../README.md)

---

*本文档提供了微服务监控的完整形式化理论和Haskell实现，为微服务架构提供了坚实的理论基础。* 