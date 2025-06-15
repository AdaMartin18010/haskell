# Web框架 (Web Framework)

## 概述

本章节涵盖Haskell Web开发的最佳实践，包括Web框架、路由系统、模板引擎、数据库集成等核心内容。

## 1. 基础Web框架

### 1.1 基本概念

#### 形式化定义

**定义 1.1.1 (Web应用)** Web应用是一个处理HTTP请求并返回HTTP响应的函数。

**定义 1.1.2 (中间件)** 中间件是处理请求和响应的函数，可以组合形成处理管道。

#### Haskell实现

```haskell
-- 基础Web框架实现
module WebFramework where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

-- HTTP方法
data Method = GET | POST | PUT | DELETE | PATCH
  deriving (Eq, Show)

-- HTTP状态码
data StatusCode = 
    OK200 | Created201 | BadRequest400 | NotFound404 | InternalError500
  deriving (Eq, Show)

-- HTTP请求
data Request = Request {
  method :: Method,
  path :: Text,
  headers :: Map Text Text,
  body :: Text
} deriving Show

-- HTTP响应
data Response = Response {
  status :: StatusCode,
  headers :: Map Text Text,
  body :: Text
} deriving Show

-- Web应用类型
type WebApp = Request -> IO Response

-- 中间件类型
type Middleware = WebApp -> WebApp

-- 基础响应函数
ok :: Text -> Response
ok body = Response OK200 M.empty body

notFound :: Response
notFound = Response NotFound404 M.empty "Not Found"

badRequest :: Text -> Response
badRequest body = Response BadRequest400 M.empty body

-- 路由系统
data Route = Route {
  method :: Method,
  path :: Text,
  handler :: WebApp
}

-- 路由匹配
matchRoute :: Request -> [Route] -> Maybe WebApp
matchRoute req routes = 
  find (\route -> routeMethod route == method req && 
                  routePath route == path req) routes >>= 
  Just . handler

-- 基础Web服务器
runServer :: [Route] -> IO ()
runServer routes = do
  putStrLn "Server running on port 8080"
  -- 实际实现会监听端口并处理请求
  return ()

-- 示例路由
exampleRoutes :: [Route]
exampleRoutes = [
  Route GET "/" (\_ -> return $ ok "Hello, World!"),
  Route GET "/users" (\_ -> return $ ok "User List"),
  Route POST "/users" (\req -> return $ ok $ "Created user: " <> body req)
]
```

### 1.2 高级Web框架特性

#### 形式化定义

**定义 1.2.1 (类型安全路由)** 类型安全路由确保路由参数的类型安全。

**定义 1.2.2 (依赖注入)** 依赖注入允许Web应用访问外部服务。

#### Haskell实现

```haskell
-- 高级Web框架特性
module AdvancedWebFramework where

import WebFramework
import Control.Monad.Reader
import Data.Aeson
import GHC.Generics

-- 类型安全路由参数
data RouteParams = RouteParams {
  userId :: Maybe Int,
  postId :: Maybe Int,
  query :: Maybe Text
} deriving (Show, Generic)

-- 类型安全路由
data TypedRoute a where
  Home :: TypedRoute Text
  User :: Int -> TypedRoute User
  Post :: Int -> TypedRoute Post
  CreateUser :: User -> TypedRoute User

-- 用户类型
data User = User {
  id :: Int,
  name :: Text,
  email :: Text
} deriving (Show, Generic, ToJSON, FromJSON)

-- 文章类型
data Post = Post {
  id :: Int,
  title :: Text,
  content :: Text,
  authorId :: Int
} deriving (Show, Generic, ToJSON, FromJSON)

-- 应用环境
data AppEnv = AppEnv {
  database :: Database,
  logger :: Logger,
  config :: Config
}

-- 应用单子
type AppM = ReaderT AppEnv IO

-- 类型安全处理器
type TypedHandler a = Request -> AppM (Response a)

-- JSON响应
jsonResponse :: (ToJSON a) => StatusCode -> a -> Response
jsonResponse status data_ = 
  Response status (M.singleton "Content-Type" "application/json") 
           (T.pack $ show $ toJSON data_)

-- 类型安全路由处理器
handleHome :: TypedHandler Text
handleHome _ = return $ jsonResponse OK200 "Welcome to our API"

handleUser :: Int -> TypedHandler User
handleUser userId _ = do
  env <- ask
  user <- getUser env userId
  case user of
    Just u -> return $ jsonResponse OK200 u
    Nothing -> return $ jsonResponse NotFound404 "User not found"

handleCreateUser :: TypedHandler User
handleCreateUser req = do
  env <- ask
  case decode (T.encodeUtf8 $ body req) of
    Just user -> do
      createdUser <- createUser env user
      return $ jsonResponse Created201 createdUser
    Nothing -> return $ jsonResponse BadRequest400 "Invalid user data"

-- 数据库接口
class Database where
  getUser :: Int -> IO (Maybe User)
  createUser :: User -> IO User
  getPost :: Int -> IO (Maybe Post)

-- 日志接口
class Logger where
  logInfo :: Text -> IO ()
  logError :: Text -> IO ()

-- 配置接口
class Config where
  getPort :: Int
  getDatabaseUrl :: Text

-- 中间件实现
loggingMiddleware :: Middleware
loggingMiddleware app req = do
  putStrLn $ "Request: " ++ show (method req) ++ " " ++ T.unpack (path req)
  response <- app req
  putStrLn $ "Response: " ++ show (status response)
  return response

corsMiddleware :: Middleware
corsMiddleware app req = do
  response <- app req
  return $ response { headers = M.insert "Access-Control-Allow-Origin" "*" (headers response) }

-- 组合中间件
composeMiddleware :: [Middleware] -> Middleware
composeMiddleware = foldr (.) id

-- 应用构建器
buildApp :: AppEnv -> [TypedRoute a] -> WebApp
buildApp env routes req = do
  let app = composeMiddleware [loggingMiddleware, corsMiddleware] baseApp
  runReaderT app env
  where
    baseApp = case matchTypedRoute req routes of
      Just handler -> handler req
      Nothing -> return notFound

-- 类型安全路由匹配
matchTypedRoute :: Request -> [TypedRoute a] -> Maybe (TypedHandler a)
matchTypedRoute req routes = 
  case (method req, path req) of
    (GET, "/") -> Just handleHome
    (GET, path) | Just userId <- parseUserId path -> Just $ handleUser userId
    (POST, "/users") -> Just handleCreateUser
    _ -> Nothing

-- 路径解析
parseUserId :: Text -> Maybe Int
parseUserId path = 
  if T.isPrefixOf "/users/" path
  then readMaybe $ T.unpack $ T.drop 7 path
  else Nothing
```

## 2. 模板引擎

### 2.1 基本概念

#### 形式化定义

**定义 2.1.1 (模板)** 模板是包含占位符的文本，可以在运行时替换为实际值。

**定义 2.1.2 (模板引擎)** 模板引擎是处理模板并生成最终文本的系统。

#### Haskell实现

```haskell
-- 模板引擎实现
module TemplateEngine where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M
import Text.Parsec
import Text.Parsec.Text

-- 模板表达式
data TemplateExpr = 
    Literal Text
  | Variable Text
  | If Text TemplateExpr TemplateExpr
  | For Text Text TemplateExpr
  deriving Show

-- 模板解析器
templateParser :: Parser [TemplateExpr]
templateParser = many templateExpr

templateExpr :: Parser TemplateExpr
templateExpr = 
  try ifExpr <|> try forExpr <|> try variable <|> literal

literal :: Parser TemplateExpr
literal = Literal <$> many1 (noneOf "{{}}")

variable :: Parser TemplateExpr
variable = do
  string "{{"
  spaces
  var <- many1 (noneOf "}}")
  spaces
  string "}}"
  return $ Variable $ T.pack var

ifExpr :: Parser TemplateExpr
ifExpr = do
  string "{{#if"
  spaces
  condition <- many1 (noneOf "}}")
  spaces
  string "}}"
  trueBranch <- templateParser
  string "{{/if}}"
  return $ If (T.pack condition) (Block trueBranch) (Block [])

forExpr :: Parser TemplateExpr
forExpr = do
  string "{{#each"
  spaces
  listVar <- many1 (noneOf " ")
  spaces
  itemVar <- many1 (noneOf "}}")
  spaces
  string "}}"
  body <- templateParser
  string "{{/each}}"
  return $ For (T.pack listVar) (T.pack itemVar) (Block body)

-- 模板块
data Block = Block [TemplateExpr]

-- 模板上下文
type Context = Map Text Value

-- 值类型
data Value = 
    StringValue Text
  | IntValue Int
  | BoolValue Bool
  | ListValue [Value]
  | ObjectValue (Map Text Value)
  deriving Show

-- 模板求值
evalTemplate :: [TemplateExpr] -> Context -> Text
evalTemplate exprs ctx = T.concat $ map (evalExpr ctx) exprs

evalExpr :: Context -> TemplateExpr -> Text
evalExpr ctx (Literal text) = text
evalExpr ctx (Variable name) = 
  case M.lookup name ctx of
    Just (StringValue val) -> val
    Just (IntValue val) -> T.pack $ show val
    Just (BoolValue val) -> T.pack $ show val
    _ -> T.empty
evalExpr ctx (If condition trueBranch falseBranch) = 
  case M.lookup condition ctx of
    Just (BoolValue True) -> evalTemplate [trueBranch] ctx
    _ -> evalTemplate [falseBranch] ctx
evalExpr ctx (For listVar itemVar body) = 
  case M.lookup listVar ctx of
    Just (ListValue items) -> 
      T.concat $ map (\item -> evalTemplate [body] (M.insert itemVar item ctx)) items
    _ -> T.empty

-- 模板编译
compileTemplate :: Text -> Either ParseError [TemplateExpr]
compileTemplate = parse templateParser ""

-- 示例模板
exampleTemplate :: Text
exampleTemplate = T.unlines [
  "<html>",
  "<head><title>{{title}}</title></head>",
  "<body>",
  "<h1>{{title}}</h1>",
  "{{#if user}}",
  "<p>Welcome, {{user.name}}!</p>",
  "{{/if}}",
  "<ul>",
  "{{#each items item}}",
  "<li>{{item.name}}: {{item.price}}</li>",
  "{{/each}}",
  "</ul>",
  "</body>",
  "</html>"
]

-- 示例上下文
exampleContext :: Context
exampleContext = M.fromList [
  ("title", StringValue "My Store"),
  ("user", ObjectValue $ M.fromList [
    ("name", StringValue "John Doe")
  ]),
  ("items", ListValue [
    ObjectValue $ M.fromList [
      ("name", StringValue "Product 1"),
      ("price", IntValue 100)
    ],
    ObjectValue $ M.fromList [
      ("name", StringValue "Product 2"),
      ("price", IntValue 200)
    ]
  ])
]
```

## 3. 数据库集成

### 3.1 基本概念

#### 形式化定义

**定义 3.1.1 (ORM)** 对象关系映射是将数据库表映射到编程语言对象的技术。

**定义 3.1.2 (查询构建器)** 查询构建器是构建类型安全数据库查询的工具。

#### Haskell实现

```haskell
-- 数据库集成实现
module DatabaseIntegration where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.Reader
import GHC.Generics

-- 数据库连接
data Connection = Connection {
  host :: Text,
  port :: Int,
  database :: Text,
  username :: Text,
  password :: Text
}

-- 表定义
data Table a = Table {
  tableName :: Text,
  columns :: [Column a]
}

-- 列定义
data Column a = Column {
  columnName :: Text,
  columnType :: ColumnType,
  isNullable :: Bool,
  defaultValue :: Maybe Text
}

-- 列类型
data ColumnType = 
    IntColumn
  | TextColumn
  | BoolColumn
  | DateTimeColumn
  deriving Show

-- 查询构建器
data Query a = 
    Select [Text] (Table a)
  | Where (Query a) (Condition a)
  | OrderBy (Query a) Text Order
  | Limit (Query a) Int
  | Offset (Query a) Int

-- 条件
data Condition a = 
    Equal Text Text
  | NotEqual Text Text
  | Greater Text Text
  | Less Text Text
  | And (Condition a) (Condition a)
  | Or (Condition a) (Condition a)

-- 排序
data Order = Asc | Desc

-- 查询执行
class QueryExecutor m where
  executeQuery :: Query a -> m [a]
  executeUpdate :: Query a -> m Int
  executeInsert :: Table a -> a -> m Int

-- 实体定义
data User = User {
  id :: Maybe Int,
  name :: Text,
  email :: Text,
  age :: Int
} deriving (Show, Generic)

-- 用户表定义
userTable :: Table User
userTable = Table "users" [
  Column "id" IntColumn False Nothing,
  Column "name" TextColumn False Nothing,
  Column "email" TextColumn False Nothing,
  Column "age" IntColumn True Nothing
]

-- 查询示例
findUserById :: Int -> Query User
findUserById userId = 
  Where (Select ["*"] userTable) (Equal "id" (T.pack $ show userId))

findUsersByAge :: Int -> Query User
findUsersByAge age = 
  Where (Select ["*"] userTable) (Greater "age" (T.pack $ show age))

-- 数据库操作
class DatabaseOps m where
  findById :: (Show a) => Table a -> Int -> m (Maybe a)
  findAll :: (Show a) => Table a -> m [a]
  insert :: (Show a) => Table a -> a -> m Int
  update :: (Show a) => Table a -> a -> m Bool
  delete :: (Show a) => Table a -> Int -> m Bool

-- 事务支持
class Transactional m where
  beginTransaction :: m ()
  commitTransaction :: m ()
  rollbackTransaction :: m ()
  withTransaction :: m a -> m a

-- 连接池
data ConnectionPool = ConnectionPool {
  connections :: [Connection],
  maxConnections :: Int,
  currentConnections :: Int
}

-- 连接池管理
class PoolManager m where
  getConnection :: m Connection
  releaseConnection :: Connection -> m ()
  withConnection :: (Connection -> m a) -> m a
```

## 4. 认证和授权

### 4.1 基本概念

#### 形式化定义

**定义 4.1.1 (认证)** 认证是验证用户身份的过程。

**定义 4.1.2 (授权)** 授权是确定用户是否有权限访问特定资源的过程。

#### Haskell实现

```haskell
-- 认证和授权实现
module Authentication where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M
import Data.Time
import Crypto.Hash
import Crypto.KDF.PBKDF2
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS

-- 用户认证信息
data AuthUser = AuthUser {
  id :: Int,
  username :: Text,
  passwordHash :: Text,
  email :: Text,
  roles :: [Role]
} deriving Show

-- 角色
data Role = Admin | User | Moderator
  deriving (Eq, Show)

-- JWT令牌
data JWTToken = JWTToken {
  header :: Map Text Text,
  payload :: Map Text Text,
  signature :: Text
} deriving Show

-- 认证中间件
authMiddleware :: (AuthUser -> Bool) -> Middleware
authMiddleware checkAuth app req = do
  case extractToken req of
    Just token -> do
      case validateToken token of
        Just user -> 
          if checkAuth user
          then app req
          else return $ jsonResponse Unauthorized401 "Insufficient permissions"
        Nothing -> return $ jsonResponse Unauthorized401 "Invalid token"
    Nothing -> return $ jsonResponse Unauthorized401 "Missing token"

-- 角色检查中间件
requireRole :: Role -> Middleware
requireRole role = authMiddleware (\user -> role `elem` roles user)

-- 管理员中间件
requireAdmin :: Middleware
requireAdmin = requireRole Admin

-- 密码哈希
hashPassword :: Text -> Text
hashPassword password = 
  let salt = BS.pack [1..16]  -- 实际应用中应该使用随机盐
      hash = pbkdf2 (PBKDF2_256 10000) salt (T.encodeUtf8 password)
  in T.pack $ show hash

-- 密码验证
verifyPassword :: Text -> Text -> Bool
verifyPassword password hash = 
  hashPassword password == hash

-- JWT令牌生成
generateToken :: AuthUser -> Text
generateToken user = 
  let header = M.fromList [("alg", "HS256"), ("typ", "JWT")]
      payload = M.fromList [
        ("sub", T.pack $ show $ id user),
        ("username", username user),
        ("roles", T.pack $ show $ roles user),
        ("exp", T.pack $ show $ addUTCTime 3600 $ utcToLocalTime utc)
      ]
      signature = "signature"  -- 实际应用中应该使用密钥签名
  in T.pack $ show $ JWTToken header payload signature

-- 令牌验证
validateToken :: Text -> Maybe AuthUser
validateToken token = 
  -- 实际实现会解析和验证JWT令牌
  Just $ AuthUser 1 "testuser" "" "test@example.com" [User]

-- 令牌提取
extractToken :: Request -> Maybe Text
extractToken req = 
  M.lookup "Authorization" (headers req) >>= 
  T.stripPrefix "Bearer "

-- 登录处理器
loginHandler :: TypedHandler (Map Text Text)
loginHandler req = do
  case decode (T.encodeUtf8 $ body req) of
    Just credentials -> do
      let username = M.lookup "username" credentials
          password = M.lookup "password" credentials
      case (username, password) of
        (Just user, Just pass) -> do
          -- 实际实现会查询数据库验证用户
          let user = AuthUser 1 user "" "test@example.com" [User]
              token = generateToken user
          return $ jsonResponse OK200 $ M.singleton "token" token
        _ -> return $ jsonResponse BadRequest400 "Invalid credentials"
    Nothing -> return $ jsonResponse BadRequest400 "Invalid JSON"
```

## 5. 应用实例

### 5.1 完整的Web应用

```haskell
-- 完整的Web应用示例
module CompleteWebApp where

import WebFramework
import AdvancedWebFramework
import TemplateEngine
import DatabaseIntegration
import Authentication

-- 应用配置
data AppConfig = AppConfig {
  port :: Int,
  databaseUrl :: Text,
  jwtSecret :: Text
}

-- 应用状态
data AppState = AppState {
  config :: AppConfig,
  dbPool :: ConnectionPool,
  templates :: Map Text [TemplateExpr]
}

-- 主应用
main :: IO ()
main = do
  config <- loadConfig
  dbPool <- createConnectionPool config
  templates <- loadTemplates
  let state = AppState config dbPool templates
  runServer $ buildRoutes state

-- 路由构建
buildRoutes :: AppState -> [Route]
buildRoutes state = [
  Route GET "/" (handleHomePage state),
  Route GET "/api/users" (handleGetUsers state),
  Route POST "/api/users" (handleCreateUser state),
  Route POST "/api/login" (handleLogin state),
  Route GET "/api/profile" (requireAuth $ handleProfile state)
]

-- 页面处理器
handleHomePage :: AppState -> WebApp
handleHomePage state _ = do
  let template = M.lookup "home" (templates state)
  case template of
    Just tmpl -> do
      let context = M.fromList [("title", StringValue "Welcome")]
      let html = evalTemplate tmpl context
      return $ Response OK200 
        (M.singleton "Content-Type" "text/html") html
    Nothing -> return notFound

-- API处理器
handleGetUsers :: AppState -> WebApp
handleGetUsers state _ = do
  users <- findAll userTable
  return $ jsonResponse OK200 users

handleCreateUser :: AppState -> WebApp
handleCreateUser state req = do
  case decode (T.encodeUtf8 $ body req) of
    Just user -> do
      userId <- insert userTable user
      return $ jsonResponse Created201 $ M.singleton "id" (IntValue userId)
    Nothing -> return $ jsonResponse BadRequest400 "Invalid user data"

handleLogin :: AppState -> WebApp
handleLogin state req = do
  case decode (T.encodeUtf8 $ body req) of
    Just credentials -> do
      let username = M.lookup "username" credentials
          password = M.lookup "password" credentials
      case (username, password) of
        (Just user, Just pass) -> do
          -- 验证用户
          let token = generateToken $ AuthUser 1 user "" "test@example.com" [User]
          return $ jsonResponse OK200 $ M.singleton "token" (StringValue token)
        _ -> return $ jsonResponse BadRequest400 "Invalid credentials"
    Nothing -> return $ jsonResponse BadRequest400 "Invalid JSON"

handleProfile :: AppState -> WebApp
handleProfile state req = do
  case extractToken req of
    Just token -> do
      case validateToken token of
        Just user -> return $ jsonResponse OK200 $ M.fromList [
          ("id", IntValue $ id user),
          ("username", StringValue $ username user),
          ("email", StringValue $ email user)
        ]
        Nothing -> return $ jsonResponse Unauthorized401 "Invalid token"
    Nothing -> return $ jsonResponse Unauthorized401 "Missing token"

-- 配置加载
loadConfig :: IO AppConfig
loadConfig = return $ AppConfig 8080 "postgresql://localhost/mydb" "secret"

-- 连接池创建
createConnectionPool :: AppConfig -> IO ConnectionPool
createConnectionPool config = return $ ConnectionPool [] 10 0

-- 模板加载
loadTemplates :: IO (Map Text [TemplateExpr])
loadTemplates = do
  homeTemplate <- compileTemplate exampleTemplate
  case homeTemplate of
    Right tmpl -> return $ M.singleton "home" tmpl
    Left _ -> return M.empty
```

## 总结

本章节建立了完整的Haskell Web开发体系，包括：

1. **基础Web框架**：HTTP处理、路由系统、中间件
2. **模板引擎**：类型安全的模板解析和渲染
3. **数据库集成**：ORM、查询构建器、事务支持
4. **认证授权**：JWT令牌、角色权限、安全中间件

所有组件都有严格的类型定义和Haskell实现，为构建安全、高效的Web应用提供了坚实的基础。

---

**参考文献**：
- Spock Framework Documentation
- Yesod Web Framework Book
- Scotty Web Framework Guide
- JWT RFC 7519 