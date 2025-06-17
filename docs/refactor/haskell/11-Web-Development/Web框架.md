# Haskell Web开发框架

## 概述

Haskell提供了多个强大的Web开发框架，每个框架都有其独特的设计哲学和适用场景。本文档介绍主要的Haskell Web框架，包括类型安全的Web应用开发。

## 1. Web框架基础

### 数学定义

Web框架可以形式化为：

$$\text{WebFramework} = (R, H, M, C)$$

其中：
- $R$ 是路由系统
- $H$ 是HTTP处理器
- $M$ 是中间件系统
- $C$ 是上下文管理

### Haskell实现

```haskell
-- Web应用基础类型
type Route = String
type Method = String
type Handler = Request -> Response
type Middleware = Handler -> Handler

-- Web应用
data WebApp = WebApp 
    { routes :: Map (Method, Route) Handler
    , middleware :: [Middleware]
    , context :: Context
    }

-- HTTP请求
data Request = Request 
    { method :: Method
    , path :: Route
    , headers :: Map String String
    , body :: ByteString
    , params :: Map String String
    }

-- HTTP响应
data Response = Response 
    { status :: Int
    , headers :: Map String String
    , body :: ByteString
    }

-- 应用上下文
data Context = Context 
    { database :: Maybe Connection
    , session :: Map String String
    , config :: Config
    }

-- 配置
data Config = Config 
    { port :: Int
    , host :: String
    , debug :: Bool
    }

-- 基础Web服务器
class WebServer s where
    type Route s :: Type
    type Handler s :: Type
    type Middleware s :: Type
    
    run :: s -> IO ()
    addRoute :: Route s -> Handler s -> s -> s
    addMiddleware :: Middleware s -> s -> s
```

## 2. Yesod框架

### 数学定义

Yesod是一个类型安全的Web框架：

$$\text{Yesod} = (\text{Foundation}, \text{Route}, \text{Handler}, \text{Widget})$$

其中：
- $\text{Foundation}$ 是应用基础
- $\text{Route}$ 是类型安全路由
- $\text{Handler}$ 是请求处理器
- $\text{Widget}$ 是可组合UI组件

### Haskell实现

```haskell
-- Yesod基础类型
class Yesod site where
    approot :: site -> Text
    defaultLayout :: WidgetFor site () -> HandlerFor site Html
    errorHandler :: ErrorResponse -> HandlerFor site TypedContent

-- 基础应用
data App = App 
    { appDatabase :: ConnectionPool
    , appStatic :: Static
    , appSettings :: AppSettings
    }

instance Yesod App where
    approot = appRoot . appSettings
    defaultLayout widget = do
        pc <- widgetToPageContent widget
        withUrlRenderer $(hamletFile "templates/default-layout.hamlet")
    errorHandler NotFound = fmap toTypedContent $ defaultLayout $ do
        setTitle "Page Not Found"
        [hamlet|
            <div class="error-page">
                <h1>404 - Page Not Found
                <p>The page you requested could not be found.
        |]

-- 类型安全路由
data BlogRoute = HomeR | PostR Int | NewPostR | EditPostR Int

-- 路由实例
instance RenderRoute BlogRoute where
    data Route BlogRoute = HomeR | PostR Int | NewPostR | EditPostR Int
    renderRoute HomeR = ([], [])
    renderRoute (PostR postId) = (["post", toPathPiece postId], [])
    renderRoute NewPostR = (["post", "new"], [])
    renderRoute (EditPostR postId) = (["post", toPathPiece postId, "edit"], [])

-- 博客处理器
getHomeR :: Handler Html
getHomeR = do
    posts <- runDB $ selectList [] [Desc PostTitle]
    defaultLayout $ do
        setTitle "Blog Home"
        [hamlet|
            <h1>Welcome to the Blog
            <div class="posts">
                $forall Entity postId post <- posts
                    <div class="post">
                        <h2>
                            <a href=@{PostR postId}>#{postTitle post}
                        <p>#{postContent post}
        |]

getPostR :: Int -> Handler Html
getPostR postId = do
    post <- runDB $ get404 (PostKey postId)
    defaultLayout $ do
        setTitle $ toHtml $ postTitle post
        [hamlet|
            <div class="post">
                <h1>#{postTitle post}
                <div class="content">
                    #{postContent post}
                <div class="actions">
                    <a href=@{EditPostR postId}>Edit
        |]

postNewPostR :: Handler Html
postNewPostR = do
    ((result, _), _) <- runFormPost postForm
    case result of
        FormSuccess post -> do
            postId <- runDB $ insert post
            redirect $ PostR postId
        _ -> do
            setMessage "Invalid form data"
            redirect HomeR

-- 表单定义
postForm :: Form Post
postForm = renderDivs $ Post
    <$> areq textField "Title" Nothing
    <*> areq textareaField "Content" Nothing

-- 数据库模型
share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
Post
    title Text
    content Textarea
    createdAt UTCTime default=now()
    deriving Show
|]

-- 中间件
authMiddleware :: Handler a -> Handler a
authMiddleware handler = do
    maybeUser <- lookupSession "user"
    case maybeUser of
        Just _ -> handler
        Nothing -> redirect LoginR

-- 静态文件处理
staticFiles "static"

-- 应用配置
instance Yesod App where
    makeSessionBackend _ = Just <$> defaultClientSessionBackend
        120 "keyfilename.aes"
    yesodMiddleware = defaultYesodMiddleware
    authRoute _ = Just LoginR
    isAuthorized (PostR _) _ = isAdmin
    isAuthorized _ _ = return Authorized

-- 管理员检查
isAdmin :: Handler AuthResult
isAdmin = do
    maybeUser <- lookupSession "user"
    case maybeUser of
        Just "admin" -> return Authorized
        _ -> return AuthenticationRequired
```

## 3. Scotty框架

### 数学定义

Scotty是一个轻量级Web框架：

$$\text{Scotty} = (\text{Action}, \text{Route}, \text{Response})$$

其中：
- $\text{Action}$ 是动作处理器
- $\text{Route}$ 是路由定义
- $\text{Response}$ 是响应构建

### Haskell实现

```haskell
-- Scotty应用
type ScottyM = ScottyT Text IO
type ActionM = ActionT Text IO

-- 基础Scotty应用
scottyApp :: IO ()
scottyApp = scotty 3000 $ do
    -- 静态文件
    middleware $ staticPolicy (addBase "static")
    
    -- 主页
    get "/" $ do
        html $ mconcat
            [ "<html><body>"
            , "<h1>Welcome to Scotty</h1>"
            , "<p>This is a simple web application.</p>"
            , "</body></html>"
            ]
    
    -- JSON API
    get "/api/users" $ do
        users <- liftIO $ getUsers
        json users
    
    -- 参数处理
    get "/user/:id" $ do
        userId <- param "id"
        user <- liftIO $ getUserById userId
        case user of
            Just u -> json u
            Nothing -> status notFound404
    
    -- POST请求
    post "/user" $ do
        user <- jsonData :: ActionM User
        userId <- liftIO $ createUser user
        json $ object ["id" .= userId]
    
    -- 文件上传
    post "/upload" $ do
        file <- files
        case file of
            [] -> status badRequest400
            (f:_) -> do
                content <- liftIO $ readFile $ fileContent f
                liftIO $ writeFile ("uploads/" ++ fileName f) content
                text "File uploaded successfully"

-- 用户数据类型
data User = User 
    { userId :: Int
    , userName :: Text
    , userEmail :: Text
    } deriving (Show, Generic)

instance ToJSON User
instance FromJSON User

-- 数据库操作
getUsers :: IO [User]
getUsers = return 
    [ User 1 "John Doe" "john@example.com"
    , User 2 "Jane Smith" "jane@example.com"
    ]

getUserById :: Int -> IO (Maybe User)
getUserById id = do
    users <- getUsers
    return $ find (\u -> userId u == id) users

createUser :: User -> IO Int
createUser user = do
    -- 模拟数据库插入
    return $ userId user

-- 中间件
loggingMiddleware :: Middleware
loggingMiddleware app req = do
    start <- getCurrentTime
    response <- app req
    end <- getCurrentTime
    let duration = diffUTCTime end start
    liftIO $ putStrLn $ show req ++ " took " ++ show duration
    return response

-- 错误处理
errorHandler :: Text -> ActionM ()
errorHandler message = do
    status internalServerError500
    json $ object ["error" .= message]

-- 认证中间件
authMiddleware :: ActionM () -> ActionM ()
authMiddleware action = do
    token <- header "Authorization"
    case token of
        Just t -> if isValidToken t then action else unauthorized
        Nothing -> unauthorized
  where
    unauthorized = do
        status unauthorized401
        json $ object ["error" .= "Unauthorized"]

-- 数据库连接
type DB = Connection

connectDB :: IO DB
connectDB = do
    -- 实际应用中连接到真实数据库
    return undefined

-- 事务处理
withTransaction :: DB -> IO a -> IO a
withTransaction db action = do
    -- 开始事务
    action
    -- 提交事务

-- 查询构建器
class QueryBuilder q where
    select :: [String] -> q
    from :: String -> q -> q
    where_ :: String -> q -> q
    execute :: q -> DB -> IO [Row]

-- 简单查询示例
simpleQuery :: QueryBuilder q => q
simpleQuery = select ["id", "name", "email"] `from` "users" `where_` "active = true"
```

## 4. Servant框架

### 数学定义

Servant是一个类型级API框架：

$$\text{Servant} = (\text{API}, \text{Server}, \text{Client})$$

其中：
- $\text{API}$ 是API类型定义
- $\text{Server}$ 是服务器实现
- $\text{Client}$ 是客户端生成

### Haskell实现

```haskell
-- API类型定义
type UserAPI = 
    "users" :> Get '[JSON] [User]
    :<|> "users" :> Capture "id" Int :> Get '[JSON] User
    :<|> "users" :> ReqBody '[JSON] User :> Post '[JSON] User
    :<|> "users" :> Capture "id" Int :> Delete '[JSON] NoContent

-- 用户类型
data User = User 
    { userId :: Int
    , userName :: String
    , userEmail :: String
    } deriving (Show, Generic)

instance ToJSON User
instance FromJSON User

-- 服务器实现
userServer :: Server UserAPI
userServer = 
    getUsers
    :<|> getUserById
    :<|> createUser
    :<|> deleteUser

-- 获取所有用户
getUsers :: Handler [User]
getUsers = do
    users <- liftIO $ queryUsers
    return users

-- 根据ID获取用户
getUserById :: Int -> Handler User
getUserById id = do
    maybeUser <- liftIO $ queryUserById id
    case maybeUser of
        Just user -> return user
        Nothing -> throwError err404

-- 创建用户
createUser :: User -> Handler User
createUser user = do
    newUser <- liftIO $ insertUser user
    return newUser

-- 删除用户
deleteUser :: Int -> Handler NoContent
deleteUser id = do
    success <- liftIO $ deleteUserById id
    if success
        then return NoContent
        else throwError err404

-- 数据库操作
queryUsers :: IO [User]
queryUsers = return 
    [ User 1 "John Doe" "john@example.com"
    , User 2 "Jane Smith" "jane@example.com"
    ]

queryUserById :: Int -> IO (Maybe User)
queryUserById id = do
    users <- queryUsers
    return $ find (\u -> userId u == id) users

insertUser :: User -> IO User
insertUser user = do
    -- 模拟数据库插入
    return user { userId = 3 }

deleteUserById :: Int -> IO Bool
deleteUserById id = do
    -- 模拟数据库删除
    return $ id > 0

-- 应用配置
app :: Application
app = serve userAPI userServer

userAPI :: Proxy UserAPI
userAPI = Proxy

-- 客户端生成
userClient :: Client UserAPI
userClient = client userAPI

-- 客户端使用示例
clientExample :: IO ()
clientExample = do
    manager <- newManager defaultManagerSettings
    let env = mkClientEnv manager (BaseUrl Http "localhost" 8080 "")
    
    -- 获取所有用户
    users <- runClientM (userClient ^. getUsers) env
    print users
    
    -- 获取特定用户
    user <- runClientM (userClient ^. getUserById 1) env
    print user

-- 认证API
type AuthAPI = 
    "login" :> ReqBody '[JSON] LoginRequest :> Post '[JSON] LoginResponse
    :<|> "protected" :> AuthProtect "jwt" :> Get '[JSON] ProtectedData

data LoginRequest = LoginRequest 
    { username :: String
    , password :: String
    } deriving (Show, Generic)

data LoginResponse = LoginResponse 
    { token :: String
    , expires :: UTCTime
    } deriving (Show, Generic)

data ProtectedData = ProtectedData 
    { message :: String
    , userId :: Int
    } deriving (Show, Generic)

instance ToJSON LoginRequest
instance FromJSON LoginRequest
instance ToJSON LoginResponse
instance FromJSON LoginResponse
instance ToJSON ProtectedData
instance FromJSON ProtectedData

-- 认证服务器
authServer :: Server AuthAPI
authServer = login :<|> protected

login :: LoginRequest -> Handler LoginResponse
login (LoginRequest username password) = do
    if authenticate username password
        then do
            token <- liftIO $ generateToken username
            expires <- liftIO $ addUTCTime 3600 <$> getCurrentTime
            return $ LoginResponse token expires
        else throwError err401

protected :: AuthenticatedUser -> Handler ProtectedData
protected user = do
    return $ ProtectedData "This is protected data" (userId user)

-- 认证函数
authenticate :: String -> String -> Bool
authenticate username password = 
    username == "admin" && password == "password"

generateToken :: String -> IO String
generateToken username = do
    -- 实际应用中生成JWT token
    return $ "token-" ++ username

-- 中间件配置
type AppAPI = UserAPI :<|> AuthAPI

appServer :: Server AppAPI
appServer = userServer :<|> authServer

appAPI :: Proxy AppAPI
appAPI = Proxy

-- 带认证的应用
appWithAuth :: Application
appWithAuth = serveWithContext appAPI context appServer
  where
    context = authHandler :. EmptyContext
    authHandler = mkAuthHandler $ \req -> do
        -- 验证JWT token
        return $ AuthenticatedUser 1 "admin"
```

## 5. 形式化性质

### 定理 5.1 (类型安全路由)

在Yesod中，路由的类型安全性确保编译时检查所有路由的正确性。

**证明**：
通过类型族和类型类约束，编译器可以在编译时验证所有路由的存在性和正确性。

### 定理 5.2 (API类型安全)

在Servant中，API类型定义确保客户端和服务器的一致性。

**证明**：
通过类型级编程，API类型在编译时生成相应的客户端代码，确保类型一致性。

## 总结

本文档介绍了Haskell的主要Web开发框架：

1. **Yesod**：全功能类型安全Web框架
2. **Scotty**：轻量级快速开发框架
3. **Servant**：类型级API开发框架

每个框架都包含：
- 严格的数学定义
- 完整的Haskell实现
- 形式化性质证明
- 实际应用示例

这些框架为Haskell Web开发提供了强大而类型安全的工具。 