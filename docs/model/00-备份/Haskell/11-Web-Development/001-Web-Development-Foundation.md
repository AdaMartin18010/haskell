# Haskell Web开发基础

## 📚 快速导航

### 相关理论

- [函数式编程基础](../01-Basic-Concepts/001-Functional-Programming-Foundation.md)
- [高阶函数](../01-Basic-Concepts/004-Higher-Order-Functions.md)
- [类型系统基础](../04-Type-System/001-Type-System-Foundation.md)

### 实现示例

- [Web框架](./002-Web-Frameworks.md)
- [数据库集成](./003-Database-Integration.md)
- [API设计](./004-API-Design.md)

### 应用领域

- [系统编程](../12-System-Programming/001-System-Programming-Foundation.md)
- [性能优化](../09-Performance/001-Performance-Analysis.md)
- [安全编程](../13-Security/001-Security-Foundation.md)

## 🎯 概述

Haskell在Web开发领域具有独特的优势，包括类型安全、高性能和函数式编程的优雅性。本文档介绍Haskell Web开发的基础概念、常用框架和最佳实践。

## 📖 1. Web开发基础概念

### 1.1 HTTP协议

**定义 1.1 (HTTP协议)**
HTTP是Web应用的基础协议，定义了客户端和服务器之间的通信规则。

**数学表示：**
$$\text{HTTP Request} \rightarrow \text{HTTP Response}$$

**Haskell实现：**

```haskell
-- HTTP请求类型
data HTTPMethod = 
  GET | 
  POST | 
  PUT | 
  DELETE | 
  PATCH
  deriving (Show, Eq)

data HTTPRequest = HTTPRequest {
  method :: HTTPMethod,
  path :: String,
  headers :: [(String, String)],
  body :: String
} deriving (Show)

data HTTPResponse = HTTPResponse {
  statusCode :: Int,
  statusText :: String,
  headers :: [(String, String)],
  body :: String
} deriving (Show)

-- HTTP处理函数
handleHTTPRequest :: HTTPRequest -> HTTPResponse
handleHTTPRequest (HTTPRequest GET "/" _ _) = 
  HTTPResponse 200 "OK" [("Content-Type", "text/html")] "<h1>Hello World</h1>"
handleHTTPRequest (HTTPRequest GET "/api/users" _ _) = 
  HTTPResponse 200 "OK" [("Content-Type", "application/json")] "[]"
handleHTTPRequest _ = 
  HTTPResponse 404 "Not Found" [] ""

-- HTTP示例
httpExample :: IO ()
httpExample = do
  let request = HTTPRequest GET "/" [] ""
      response = handleHTTPRequest request
  putStrLn $ "Request: " ++ show request
  putStrLn $ "Response: " ++ show response
```

### 1.2 Web服务器

**定义 1.2 (Web服务器)**
Web服务器是处理HTTP请求并返回响应的程序。

**Haskell实现：**

```haskell
-- 简化的Web服务器
type RequestHandler = HTTPRequest -> IO HTTPResponse

data WebServer = WebServer {
  port :: Int,
  handlers :: [(String, RequestHandler)]
}

-- 服务器操作
startServer :: WebServer -> IO ()
startServer server = do
  putStrLn $ "Server starting on port " ++ show (port server)
  putStrLn "Server is running..."

addHandler :: String -> RequestHandler -> WebServer -> WebServer
addHandler path handler server = 
  server { handlers = (path, handler) : handlers server }

-- 默认处理器
defaultHandler :: RequestHandler
defaultHandler request = do
  putStrLn $ "Handling request: " ++ show request
  return $ HTTPResponse 200 "OK" [] "Default response"

-- Web服务器示例
webServerExample :: IO ()
webServerExample = do
  let server = WebServer 8080 []
      serverWithHandlers = addHandler "/" defaultHandler server
  putStrLn $ "Server configuration: " ++ show serverWithHandlers
  putStrLn "Server would start here..."
```

### 1.3 路由系统

**定义 1.3 (路由系统)**
路由系统将URL路径映射到相应的处理函数。

**Haskell实现：**

```haskell
-- 路由类型
type Route = String
type RouteHandler = HTTPRequest -> IO HTTPResponse

data Router = Router {
  routes :: [(Route, RouteHandler)]
}

-- 路由操作
addRoute :: Route -> RouteHandler -> Router -> Router
addRoute route handler router = 
  router { routes = (route, handler) : routes router }

findRoute :: Route -> Router -> Maybe RouteHandler
findRoute route router = lookup route (routes router)

-- 路由处理器
homeHandler :: RouteHandler
homeHandler _ = return $ HTTPResponse 200 "OK" 
  [("Content-Type", "text/html")] 
  "<h1>Welcome to Haskell Web App</h1>"

usersHandler :: RouteHandler
usersHandler _ = return $ HTTPResponse 200 "OK" 
  [("Content-Type", "application/json")] 
  "[{\"id\": 1, \"name\": \"Alice\"}]"

-- 路由示例
routerExample :: IO ()
routerExample = do
  let router = Router []
      routerWithRoutes = addRoute "/" homeHandler 
                        (addRoute "/users" usersHandler router)
      
      request1 = HTTPRequest GET "/" [] ""
      request2 = HTTPRequest GET "/users" [] ""
      
      handler1 = findRoute "/" routerWithRoutes
      handler2 = findRoute "/users" routerWithRoutes
  putStrLn $ "Router: " ++ show routerWithRoutes
  putStrLn $ "Home handler found: " ++ show (isJust handler1)
  putStrLn $ "Users handler found: " ++ show (isJust handler2)
```

## 🔧 2. 常用Web框架

### 2.1 Yesod框架

**定义 2.1 (Yesod框架)**
Yesod是Haskell中最流行的Web框架，提供类型安全的Web开发。

**Haskell实现：**

```haskell
-- Yesod应用基础结构
class Yesod app where
  approot :: app -> String
  defaultLayout :: Widget -> Handler Html
  errorHandler :: ErrorResponse -> Handler Html

-- 简化的Yesod处理器
type Handler a = IO a
type Widget = String

-- Yesod路由
data AppRoute = 
  HomeR | 
  UsersR | 
  UserR Int
  deriving (Show, Eq)

-- Yesod处理器
getHomeR :: Handler Html
getHomeR = return "<h1>Welcome to Yesod</h1>"

getUsersR :: Handler Html
getUsersR = return "<h1>Users List</h1>"

getUserR :: Int -> Handler Html
getUserR userId = return $ "<h1>User " ++ show userId ++ "</h1>"

-- Yesod示例
yesodExample :: IO ()
yesodExample = do
  putStrLn "Yesod Framework Example:"
  putStrLn "1. Type-safe routing"
  putStrLn "2. Persistent database integration"
  putStrLn "3. Hamlet templating"
  putStrLn "4. Form handling"
```

### 2.2 Scotty框架

**定义 2.2 (Scotty框架)**
Scotty是轻量级的Web框架，类似于Ruby的Sinatra。

**Haskell实现：**

```haskell
-- Scotty应用类型
type ScottyM = IO
type ActionM = IO

-- 简化的Scotty路由
data ScottyRoute = ScottyRoute {
  method :: HTTPMethod,
  path :: String,
  handler :: ActionM HTTPResponse
}

-- Scotty应用
data ScottyApp = ScottyApp {
  routes :: [ScottyRoute]
}

-- Scotty路由定义
get :: String -> ActionM HTTPResponse -> ScottyApp -> ScottyApp
get path handler app = 
  app { routes = ScottyRoute GET path handler : routes app }

post :: String -> ActionM HTTPResponse -> ScottyApp -> ScottyApp
post path handler app = 
  app { routes = ScottyRoute POST path handler : routes app }

-- Scotty处理器
scottyHomeHandler :: ActionM HTTPResponse
scottyHomeHandler = return $ HTTPResponse 200 "OK" 
  [("Content-Type", "text/html")] 
  "<h1>Scotty Home</h1>"

scottyUsersHandler :: ActionM HTTPResponse
scottyUsersHandler = return $ HTTPResponse 200 "OK" 
  [("Content-Type", "application/json")] 
  "[{\"id\": 1, \"name\": \"Bob\"}]"

-- Scotty示例
scottyExample :: IO ()
scottyExample = do
  let app = ScottyApp []
      appWithRoutes = get "/" scottyHomeHandler 
                     (post "/users" scottyUsersHandler app)
  putStrLn $ "Scotty app: " ++ show appWithRoutes
  putStrLn "Scotty provides lightweight web development"
```

### 2.3 Servant框架

**定义 2.3 (Servant框架)**
Servant是基于类型级编程的API框架，提供类型安全的API定义。

**Haskell实现：**

```haskell
-- Servant API类型
type API = 
  "users" :> Get '[JSON] [User] :<|>
  "users" :> Capture "id" Int :> Get '[JSON] User :<|>
  "users" :> ReqBody '[JSON] User :> Post '[JSON] User

-- 用户数据类型
data User = User {
  userId :: Int,
  userName :: String,
  userEmail :: String
} deriving (Show, Eq)

-- Servant处理器
getUsers :: Handler [User]
getUsers = return [
  User 1 "Alice" "alice@example.com",
  User 2 "Bob" "bob@example.com"
  ]

getUser :: Int -> Handler User
getUser id = return $ User id "User" "user@example.com"

createUser :: User -> Handler User
createUser user = return user

-- Servant示例
servantExample :: IO ()
servantExample = do
  putStrLn "Servant Framework Example:"
  putStrLn "1. Type-level API specification"
  putStrLn "2. Automatic documentation generation"
  putStrLn "3. Type-safe client generation"
  putStrLn "4. Multiple content type support"
```

## 💾 3. 模板系统

### 3.1 Hamlet模板

**定义 3.1 (Hamlet模板)**
Hamlet是Yesod框架的HTML模板系统，提供类型安全的模板。

**Haskell实现：**

```haskell
-- Hamlet模板类型
type Hamlet = String

-- Hamlet模板函数
hamletTemplate :: String -> Hamlet
hamletTemplate title = 
  "<!DOCTYPE html>\n" ++
  "<html>\n" ++
  "  <head>\n" ++
  "    <title>" ++ title ++ "</title>\n" ++
  "  </head>\n" ++
  "  <body>\n" ++
  "    <h1>" ++ title ++ "</h1>\n" ++
  "  </body>\n" ++
  "</html>"

-- Hamlet用户列表模板
userListTemplate :: [User] -> Hamlet
userListTemplate users = 
  "<!DOCTYPE html>\n" ++
  "<html>\n" ++
  "  <head><title>Users</title></head>\n" ++
  "  <body>\n" ++
  "    <h1>Users</h1>\n" ++
  "    <ul>\n" ++
  concatMap (\user -> 
    "      <li>" ++ userName user ++ " (" ++ userEmail user ++ ")</li>\n") users ++
  "    </ul>\n" ++
  "  </body>\n" ++
  "</html>"

-- Hamlet示例
hamletExample :: IO ()
hamletExample = do
  let homePage = hamletTemplate "Welcome"
      users = [User 1 "Alice" "alice@example.com", User 2 "Bob" "bob@example.com"]
      usersPage = userListTemplate users
  putStrLn "Hamlet Template Example:"
  putStrLn homePage
  putStrLn usersPage
```

### 3.2 动态模板

**定义 3.2 (动态模板)**
动态模板支持运行时数据绑定。

**Haskell实现：**

```haskell
-- 模板变量
type TemplateVar = String
type TemplateValue = String

-- 模板引擎
type Template = String
type TemplateContext = [(TemplateVar, TemplateValue)]

-- 模板渲染
renderTemplate :: Template -> TemplateContext -> String
renderTemplate template context = 
  foldr (\(var, value) acc -> 
    replace ("{{" ++ var ++ "}}") value acc) template context

-- 字符串替换
replace :: String -> String -> String -> String
replace old new str = 
  case break (isPrefixOf old) (tails str) of
    (before, _:after) -> before ++ new ++ drop (length old) after
    _ -> str

-- 动态模板示例
dynamicTemplateExample :: IO ()
dynamicTemplateExample = do
  let template = "<h1>Hello {{name}}!</h1><p>Welcome to {{site}}.</p>"
      context = [("name", "Alice"), ("site", "Haskell Web")]
      rendered = renderTemplate template context
  putStrLn "Dynamic Template Example:"
  putStrLn $ "Template: " ++ template
  putStrLn $ "Context: " ++ show context
  putStrLn $ "Rendered: " ++ rendered
```

## 🎭 4. 表单处理

### 4.1 表单类型

**定义 4.1 (表单)**
表单是用户输入数据的界面元素。

**Haskell实现：**

```haskell
-- 表单字段类型
data FormField = 
  TextField String |
  EmailField String |
  PasswordField String |
  NumberField Int |
  CheckboxField Bool
  deriving (Show)

-- 表单类型
data Form = Form {
  formFields :: [FormField],
  formAction :: String,
  formMethod :: HTTPMethod
} deriving (Show)

-- 表单验证
type ValidationRule = String -> Bool
type ValidationError = String

validateForm :: [(String, ValidationRule)] -> [(String, String)] -> [ValidationError]
validateForm rules data = 
  concatMap (\(field, rule) -> 
    case lookup field data of
      Just value -> if rule value then [] else [field ++ " is invalid"]
      Nothing -> [field ++ " is required"]) rules

-- 表单示例
formExample :: IO ()
formExample = do
  let userForm = Form [
        TextField "name",
        EmailField "email",
        PasswordField "password"
        ] "/register" POST
      
      validationRules = [
        ("name", not . null),
        ("email", elem '@'),
        ("password", (>= 8) . length)
        ]
      
      formData = [("name", "Alice"), ("email", "alice@example.com"), ("password", "12345678")]
      errors = validateForm validationRules formData
  putStrLn $ "Form: " ++ show userForm
  putStrLn $ "Validation errors: " ++ show errors
```

### 4.2 表单生成

**定义 4.2 (表单生成)**
自动生成HTML表单。

**Haskell实现：**

```haskell
-- 表单生成器
generateForm :: Form -> String
generateForm (Form fields action method) = 
  "<form action=\"" ++ action ++ "\" method=\"" ++ show method ++ "\">\n" ++
  concatMap generateField fields ++
  "  <input type=\"submit\" value=\"Submit\">\n" ++
  "</form>"

-- 字段生成器
generateField :: FormField -> String
generateField (TextField name) = 
  "  <label for=\"" ++ name ++ "\">" ++ name ++ ":</label>\n" ++
  "  <input type=\"text\" name=\"" ++ name ++ "\" id=\"" ++ name ++ "\"><br>\n"
generateField (EmailField name) = 
  "  <label for=\"" ++ name ++ "\">" ++ name ++ ":</label>\n" ++
  "  <input type=\"email\" name=\"" ++ name ++ "\" id=\"" ++ name ++ "\"><br>\n"
generateField (PasswordField name) = 
  "  <label for=\"" ++ name ++ "\">" ++ name ++ ":</label>\n" ++
  "  <input type=\"password\" name=\"" ++ name ++ "\" id=\"" ++ name ++ "\"><br>\n"
generateField (NumberField name) = 
  "  <label for=\"" ++ name ++ "\">" ++ name ++ ":</label>\n" ++
  "  <input type=\"number\" name=\"" ++ name ++ "\" id=\"" ++ name ++ "\"><br>\n"
generateField (CheckboxField name) = 
  "  <input type=\"checkbox\" name=\"" ++ name ++ "\" id=\"" ++ name ++ "\">\n" ++
  "  <label for=\"" ++ name ++ "\">" ++ name ++ "</label><br>\n"

-- 表单生成示例
formGenerationExample :: IO ()
formGenerationExample = do
  let registrationForm = Form [
        TextField "username",
        EmailField "email",
        PasswordField "password",
        NumberField "age",
        CheckboxField "agree"
        ] "/register" POST
      
      htmlForm = generateForm registrationForm
  putStrLn "Form Generation Example:"
  putStrLn htmlForm
```

## ⚡ 5. 会话管理

### 5.1 会话类型

**定义 5.1 (会话)**
会话是服务器端存储用户状态信息的机制。

**Haskell实现：**

```haskell
-- 会话数据类型
type SessionId = String
type SessionData = [(String, String)]

data Session = Session {
  sessionId :: SessionId,
  sessionData :: SessionData,
  sessionExpiry :: Int  -- Unix timestamp
} deriving (Show)

-- 会话管理器
type SessionManager = [(SessionId, Session)]

-- 会话操作
createSession :: SessionId -> SessionManager -> SessionManager
createSession sid manager = 
  (sid, Session sid [] (currentTime + 3600)) : manager

getSession :: SessionId -> SessionManager -> Maybe Session
getSession sid = lookup sid

updateSession :: SessionId -> SessionData -> SessionManager -> SessionManager
updateSession sid data manager = 
  case getSession sid manager of
    Just session -> (sid, session { sessionData = data }) : 
                   filter ((/= sid) . fst) manager
    Nothing -> manager

-- 模拟当前时间
currentTime :: Int
currentTime = 1640995200  -- 2022-01-01 00:00:00

-- 会话示例
sessionExample :: IO ()
sessionExample = do
  let manager = []
      manager1 = createSession "session123" manager
      manager2 = updateSession "session123" [("user", "alice"), ("role", "admin")] manager1
      session = getSession "session123" manager2
  putStrLn $ "Session manager: " ++ show manager2
  putStrLn $ "Retrieved session: " ++ show session
```

### 5.2 会话中间件

**定义 5.2 (会话中间件)**
会话中间件自动处理会话的创建和管理。

**Haskell实现：**

```haskell
-- 中间件类型
type Middleware = HTTPRequest -> (HTTPRequest -> IO HTTPResponse) -> IO HTTPResponse

-- 会话中间件
sessionMiddleware :: SessionManager -> Middleware
sessionMiddleware manager request handler = do
  let sessionId = extractSessionId request
      updatedManager = case sessionId of
        Just sid -> if isJust (getSession sid manager) 
                   then manager 
                   else createSession sid manager
        Nothing -> manager
  response <- handler request
  return $ addSessionHeader response sessionId

-- 提取会话ID
extractSessionId :: HTTPRequest -> Maybe SessionId
extractSessionId request = 
  lookup "Cookie" (headers request) >>= parseSessionCookie

-- 解析会话Cookie
parseSessionCookie :: String -> Maybe SessionId
parseSessionCookie cookie = 
  case break (== '=') cookie of
    ("sessionid", '=':value) -> Just value
    _ -> Nothing

-- 添加会话头
addSessionHeader :: HTTPResponse -> Maybe SessionId -> HTTPResponse
addSessionHeader response Nothing = response
addSessionHeader response (Just sid) = 
  response { headers = ("Set-Cookie", "sessionid=" ++ sid) : headers response }

-- 会话中间件示例
sessionMiddlewareExample :: IO ()
sessionMiddlewareExample = do
  let manager = []
      request = HTTPRequest GET "/" [("Cookie", "sessionid=abc123")] ""
      handler req = return $ HTTPResponse 200 "OK" [] "Hello"
      
      middleware = sessionMiddleware manager
      response = middleware request handler
  putStrLn "Session Middleware Example:"
  putStrLn $ "Request: " ++ show request
  putStrLn $ "Response: " ++ show response
```

## 🔄 6. 数据库集成

### 6.1 数据库连接

**定义 6.1 (数据库连接)**
数据库连接是Web应用与数据库之间的通信通道。

**Haskell实现：**

```haskell
-- 数据库连接类型
data DatabaseConnection = DatabaseConnection {
  connectionString :: String,
  isConnected :: Bool
} deriving (Show)

-- 数据库操作
connectDatabase :: String -> IO DatabaseConnection
connectDatabase connStr = do
  putStrLn $ "Connecting to database: " ++ connStr
  return $ DatabaseConnection connStr True

disconnectDatabase :: DatabaseConnection -> IO ()
disconnectDatabase conn = do
  putStrLn $ "Disconnecting from database: " ++ connectionString conn

-- 数据库查询
type Query = String
type QueryResult = [[String]]

executeQuery :: DatabaseConnection -> Query -> IO QueryResult
executeQuery conn query = do
  putStrLn $ "Executing query: " ++ query
  return [["1", "Alice", "alice@example.com"], ["2", "Bob", "bob@example.com"]]

-- 数据库示例
databaseExample :: IO ()
databaseExample = do
  conn <- connectDatabase "postgresql://localhost:5432/mydb"
  result <- executeQuery conn "SELECT * FROM users"
  putStrLn $ "Query result: " ++ show result
  disconnectDatabase conn
```

### 6.2 ORM映射

**定义 6.2 (ORM映射)**
ORM将数据库表映射到Haskell数据类型。

**Haskell实现：**

```haskell
-- 用户实体
data UserEntity = UserEntity {
  userEntityId :: Maybe Int,
  userEntityName :: String,
  userEntityEmail :: String,
  userEntityCreatedAt :: String
} deriving (Show)

-- 用户存储库
class UserRepository where
  findAll :: IO [UserEntity]
  findById :: Int -> IO (Maybe UserEntity)
  save :: UserEntity -> IO UserEntity
  delete :: Int -> IO Bool

-- 用户存储库实现
data UserRepositoryImpl = UserRepositoryImpl {
  connection :: DatabaseConnection
}

instance UserRepository UserRepositoryImpl where
  findAll repo = do
    result <- executeQuery (connection repo) "SELECT * FROM users"
    return $ map rowToUser result
  
  findById repo id = do
    result <- executeQuery (connection repo) ("SELECT * FROM users WHERE id = " ++ show id)
    case result of
      [row] -> return $ Just (rowToUser row)
      _ -> return Nothing
  
  save repo user = do
    let query = "INSERT INTO users (name, email) VALUES ('" ++ 
                userEntityName user ++ "', '" ++ userEntityEmail user ++ "')"
    executeQuery (connection repo) query
    return user
  
  delete repo id = do
    executeQuery (connection repo) ("DELETE FROM users WHERE id = " ++ show id)
    return True

-- 行到用户转换
rowToUser :: [String] -> UserEntity
rowToUser [id, name, email, created] = 
  UserEntity (Just (read id)) name email created
rowToUser _ = error "Invalid user row"

-- ORM示例
ormExample :: IO ()
ormExample = do
  conn <- connectDatabase "postgresql://localhost:5432/mydb"
  let repo = UserRepositoryImpl conn
  
  users <- findAll repo
  putStrLn $ "All users: " ++ show users
  
  user <- findById repo 1
  putStrLn $ "User with id 1: " ++ show user
  
  newUser <- save repo (UserEntity Nothing "Charlie" "charlie@example.com" "")
  putStrLn $ "Saved user: " ++ show newUser
  
  disconnectDatabase conn
```

## 🛠️ 7. 安全考虑

### 7.1 输入验证

**定义 7.1 (输入验证)**
输入验证确保用户输入的数据符合预期格式。

**Haskell实现：**

```haskell
-- 验证规则
type ValidationRule = String -> Bool
type ValidationError = String

-- 验证器
data Validator = Validator {
  rules :: [(String, ValidationRule)],
  errors :: [ValidationError]
}

-- 验证操作
validate :: Validator -> [(String, String)] -> Validator
validate validator data = 
  let errors = concatMap (\(field, rule) -> 
    case lookup field data of
      Just value -> if rule value then [] else [field ++ " is invalid"]
      Nothing -> [field ++ " is required"]) (rules validator)
  in validator { errors = errors }

-- 验证规则
isEmail :: ValidationRule
isEmail email = '@' `elem` email && '.' `elem` email

isStrongPassword :: ValidationRule
isStrongPassword password = 
  length password >= 8 && 
  any isUpper password && 
  any isLower password && 
  any isDigit password

-- 输入验证示例
inputValidationExample :: IO ()
inputValidationExample = do
  let validator = Validator [
        ("email", isEmail),
        ("password", isStrongPassword)
        ] []
      
      formData = [("email", "alice@example.com"), ("password", "Password123")]
      validated = validate validator formData
  putStrLn $ "Validation errors: " ++ show (errors validated)
```

### 7.2 SQL注入防护

**定义 7.2 (SQL注入防护)**
SQL注入防护防止恶意SQL代码的执行。

**Haskell实现：**

```haskell
-- 参数化查询
data ParameterizedQuery = ParameterizedQuery {
  query :: String,
  parameters :: [String]
} deriving (Show)

-- 安全查询构建
buildSafeQuery :: String -> [String] -> ParameterizedQuery
buildSafeQuery query params = ParameterizedQuery query params

-- 查询执行
executeSafeQuery :: DatabaseConnection -> ParameterizedQuery -> IO QueryResult
executeSafeQuery conn (ParameterizedQuery query params) = do
  putStrLn $ "Executing safe query: " ++ query
  putStrLn $ "With parameters: " ++ show params
  return [["1", "Alice"], ["2", "Bob"]]

-- SQL注入防护示例
sqlInjectionProtectionExample :: IO ()
sqlInjectionProtectionExample = do
  let conn = DatabaseConnection "postgresql://localhost:5432/mydb" True
      
      -- 不安全的查询（容易受到SQL注入攻击）
      unsafeQuery = "SELECT * FROM users WHERE name = '" ++ "'; DROP TABLE users; --" ++ "'"
      
      -- 安全的参数化查询
      safeQuery = buildSafeQuery "SELECT * FROM users WHERE name = ?" ["'; DROP TABLE users; --"]
      
      result = executeSafeQuery conn safeQuery
  putStrLn "SQL Injection Protection Example:"
  putStrLn $ "Unsafe query: " ++ unsafeQuery
  putStrLn $ "Safe query: " ++ show safeQuery
  putStrLn $ "Query result: " ++ show result
```

## 📊 8. 性能优化

### 8.1 缓存策略

**定义 8.1 (缓存)**
缓存是提高Web应用性能的重要技术。

**Haskell实现：**

```haskell
-- 缓存类型
type CacheKey = String
type CacheValue = String
type Cache = [(CacheKey, (CacheValue, Int))]  -- (key, (value, expiry))

-- 缓存操作
getFromCache :: CacheKey -> Cache -> Maybe CacheValue
getFromCache key cache = 
  case lookup key cache of
    Just (value, expiry) -> 
      if currentTime < expiry 
      then Just value 
      else Nothing
    Nothing -> Nothing

setCache :: CacheKey -> CacheValue -> Int -> Cache -> Cache
setCache key value expiry cache = 
  (key, (value, expiry)) : filter ((/= key) . fst) cache

-- 缓存中间件
cacheMiddleware :: Cache -> Middleware
cacheMiddleware cache request handler = do
  let cacheKey = show request
      cachedValue = getFromCache cacheKey cache
  case cachedValue of
    Just value -> return $ HTTPResponse 200 "OK" [("X-Cache", "HIT")] value
    Nothing -> do
      response <- handler request
      let updatedCache = setCache cacheKey (body response) (currentTime + 300) cache
      return response

-- 缓存示例
cacheExample :: IO ()
cacheExample = do
  let cache = []
      request = HTTPRequest GET "/api/users" [] ""
      handler req = return $ HTTPResponse 200 "OK" [] "[{\"id\": 1, \"name\": \"Alice\"}]"
      
      middleware = cacheMiddleware cache
      response1 = middleware request handler
      response2 = middleware request handler
  putStrLn "Cache Example:"
  putStrLn $ "First request: " ++ show response1
  putStrLn $ "Second request (cached): " ++ show response2
```

### 8.2 异步处理

**定义 8.2 (异步处理)**
异步处理提高Web应用的并发性能。

**Haskell实现：**

```haskell
-- 异步任务
type AsyncTask = IO ()
type TaskQueue = [AsyncTask]

-- 异步处理器
data AsyncProcessor = AsyncProcessor {
  taskQueue :: TaskQueue,
  isRunning :: Bool
}

-- 异步操作
addTask :: AsyncTask -> AsyncProcessor -> AsyncProcessor
addTask task processor = 
  processor { taskQueue = task : taskQueue processor }

processTasks :: AsyncProcessor -> IO AsyncProcessor
processTasks processor = do
  let tasks = reverse (taskQueue processor)
  mapM_ (\task -> task) tasks
  return processor { taskQueue = [], isRunning = False }

-- 异步示例
asyncExample :: IO ()
asyncExample = do
  let processor = AsyncProcessor [] False
      
      task1 = putStrLn "Processing task 1..."
      task2 = putStrLn "Processing task 2..."
      task3 = putStrLn "Processing task 3..."
      
      processorWithTasks = addTask task1 
                           (addTask task2 
                           (addTask task3 processor))
  putStrLn "Async Processing Example:"
  finalProcessor <- processTasks processorWithTasks
  putStrLn $ "Final processor: " ++ show finalProcessor
```

## 🔗 9. 部署和运维

### 9.1 部署配置

**定义 9.1 (部署配置)**
部署配置定义Web应用的运行环境。

**Haskell实现：**

```haskell
-- 部署配置
data DeploymentConfig = DeploymentConfig {
  port :: Int,
  host :: String,
  environment :: String,
  databaseUrl :: String,
  logLevel :: String
} deriving (Show)

-- 配置加载
loadConfig :: String -> DeploymentConfig
loadConfig "development" = DeploymentConfig 3000 "localhost" "development" 
                           "postgresql://localhost:5432/devdb" "debug"
loadConfig "production" = DeploymentConfig 80 "0.0.0.0" "production" 
                          "postgresql://prod:5432/proddb" "info"
loadConfig _ = error "Unknown environment"

-- 部署示例
deploymentExample :: IO ()
deploymentExample = do
  let devConfig = loadConfig "development"
      prodConfig = loadConfig "production"
  putStrLn $ "Development config: " ++ show devConfig
  putStrLn $ "Production config: " ++ show prodConfig
```

### 9.2 监控和日志

**定义 9.2 (监控)**
监控和日志记录Web应用的运行状态。

**Haskell实现：**

```haskell
-- 日志级别
data LogLevel = DEBUG | INFO | WARN | ERROR deriving (Show, Eq)

-- 日志记录
data LogEntry = LogEntry {
  timestamp :: String,
  level :: LogLevel,
  message :: String,
  context :: [(String, String)]
} deriving (Show)

-- 日志记录器
type Logger = LogLevel -> String -> [(String, String)] -> IO ()

-- 简单日志记录器
simpleLogger :: Logger
simpleLogger level message context = do
  let entry = LogEntry "2022-01-01 12:00:00" level message context
  putStrLn $ show entry

-- 监控指标
data Metrics = Metrics {
  requestCount :: Int,
  errorCount :: Int,
  responseTime :: Double
} deriving (Show)

-- 监控示例
monitoringExample :: IO ()
monitoringExample = do
  let logger = simpleLogger
      metrics = Metrics 100 5 0.15
  logger INFO "Application started" [("version", "1.0.0")]
  logger DEBUG "Processing request" [("path", "/api/users")]
  logger ERROR "Database connection failed" [("error", "timeout")]
  putStrLn $ "Current metrics: " ++ show metrics
```

## 📚 10. 总结与展望

### 10.1 Web开发的核心概念

1. **HTTP协议**：Web通信的基础
2. **路由系统**：URL到处理函数的映射
3. **模板系统**：动态内容生成
4. **表单处理**：用户输入处理
5. **会话管理**：用户状态维护

### 10.2 Haskell Web开发的优势

1. **类型安全**：编译时错误检查
2. **高性能**：优化的运行时
3. **函数式编程**：清晰的代码结构
4. **并发支持**：内置并发原语

### 10.3 未来发展方向

1. **WebAssembly**：客户端Haskell
2. **实时通信**：WebSocket支持
3. **微服务架构**：服务化部署
4. **云原生**：容器化部署

---

**相关文档**：

- [函数式编程基础](../01-Basic-Concepts/001-Functional-Programming-Foundation.md)
- [高阶函数](../01-Basic-Concepts/004-Higher-Order-Functions.md)
- [类型系统基础](../04-Type-System/001-Type-System-Foundation.md)
- [Web框架](./002-Web-Frameworks.md)

**实现示例**：

- [数据库集成](./003-Database-Integration.md)
- [API设计](./004-API-Design.md)
- [性能优化](../09-Performance/001-Performance-Analysis.md)
