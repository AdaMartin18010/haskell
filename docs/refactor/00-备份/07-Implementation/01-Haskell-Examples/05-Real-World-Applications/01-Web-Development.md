# Web开发应用 (Web Development Applications)

## 概述

本文档展示了使用Haskell进行Web开发的完整解决方案，包括Web框架、数据库集成、API设计和最佳实践。

## 1. Web框架基础

### 概念定义

Web框架提供构建Web应用程序的基础设施，包括路由、中间件、模板引擎等。

### Haskell实现

```haskell
-- 基本Web应用类型
type WebApp = Request -> Response

-- 请求和响应类型
data Request = Request
  { method :: Method
  , path :: String
  , headers :: [(String, String)]
  , body :: String
  }

data Response = Response
  { status :: Int
  , headers :: [(String, String)]
  , body :: String
  }

data Method = GET | POST | PUT | DELETE | PATCH

-- 基本路由系统
type Route = (Method, String, WebApp)

-- 路由匹配
matchRoute :: Request -> [Route] -> Maybe WebApp
matchRoute req routes = 
  find (\(method, path, _) -> 
    method == requestMethod req && 
    matchPath path (requestPath req)) routes
  >>= Just . (\(_, _, handler) -> handler)

-- 路径匹配
matchPath :: String -> String -> Bool
matchPath pattern path = 
  let patternParts = splitOn "/" pattern
      pathParts = splitOn "/" path
  in length patternParts == length pathParts &&
     all matchPart (zip patternParts pathParts)

matchPart :: (String, String) -> Bool
matchPart (pattern, path) = 
  pattern == path || 
  head pattern == ':' ||  -- 参数匹配
  pattern == "*"          -- 通配符
```

## 2. Yesod框架应用

### 概念定义

Yesod是Haskell的主要Web框架，提供类型安全的Web开发。

### Haskell实现

```haskell
-- Yesod应用基础
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}

import Yesod
import Yesod.Static
import Data.Text (Text)

-- 应用基础类型
data App = App
  { appStatic :: Static
  , appDatabase :: ConnectionPool
  }

-- 路由定义
mkYesodData "App" [parseRoutes|
/ HomeR GET
/user/#Int UserR GET
/users UsersR GET POST
/api/users ApiUsersR GET POST
/static StaticR Static appStatic
|]

-- Yesod实例
instance Yesod App where
  approot = ApprootStatic "http://localhost:3000"
  
  defaultLayout widget = do
    pc <- widgetToPageContent widget
    withUrlRenderer [hamlet|
      $doctype 5
      <html>
        <head>
          <title>#{pageTitle pc}
          <meta charset=utf-8>
          <link rel=stylesheet href=@{StaticR css_main_css}>
        <body>
          <nav>
            <a href=@{HomeR}>Home
            <a href=@{UsersR}>Users
          ^{pageBody pc}
    |]

-- 处理器定义
getHomeR :: Handler Html
getHomeR = defaultLayout [whamlet|
  <h1>Welcome to Haskell Web App
  <p>This is a sample web application built with Yesod.
|]

getUserR :: Int -> Handler Html
getUserR userId = do
  user <- getUserById userId
  case user of
    Just u -> defaultLayout [whamlet|
      <h1>User Profile
      <p>Name: #{userName u}
      <p>Email: #{userEmail u}
    |]
    Nothing -> notFound

getUsersR :: Handler Html
getUsersR = do
  users <- getAllUsers
  defaultLayout [whamlet|
    <h1>Users
    <ul>
      $forall user <- users
        <li>
          <a href=@{UserR $ userId user}>#{userName user}
  |]

postUsersR :: Handler Value
postUsersR = do
  userData <- requireJsonBody :: Handler UserData
  userId <- createUser userData
  returnJson $ object ["id" .= userId, "message" .= ("User created" :: Text)]

-- API处理器
getApiUsersR :: Handler Value
getApiUsersR = do
  users <- getAllUsers
  returnJson users

postApiUsersR :: Handler Value
postApiUsersR = do
  userData <- requireJsonBody :: Handler UserData
  userId <- createUser userData
  returnJson $ object ["id" .= userId]
```

## 3. 数据库集成

### 概念定义

数据库集成提供数据持久化能力，支持关系型和非关系型数据库。

### Haskell实现

```haskell
-- 数据库模型
import Database.Persist
import Database.Persist.Sqlite
import Database.Persist.TH

-- 实体定义
share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
User
  name Text
  email Text Unique
  age Int Maybe
  createdAt UTCTime default=now()
  deriving Show

Post
  title Text
  content Textarea
  authorId UserId
  published Bool default=false
  createdAt UTCTime default=now()
  deriving Show
|]

-- 数据库操作
getUserById :: Int -> Handler (Maybe User)
getUserById userId = runDB $ get $ UserKey $ SqlBackendKey $ fromIntegral userId

getAllUsers :: Handler [Entity User]
getAllUsers = runDB $ selectList [] [Asc UserName]

createUser :: UserData -> Handler (Key User)
createUser userData = runDB $ insert $ User
  { userName = userDataName userData
  , userEmail = userDataEmail userData
  , userAge = userDataAge userData
  , userCreatedAt = utcNow
  }

-- 查询构建器
getUsersByAge :: Int -> Handler [Entity User]
getUsersByAge minAge = runDB $ selectList [UserAge >=. Just minAge] []

getUserPosts :: UserId -> Handler [Entity Post]
getUserPosts userId = runDB $ selectList [PostAuthorId ==. userId] [Desc PostCreatedAt]

-- 事务处理
createUserWithPosts :: UserData -> [PostData] -> Handler (Key User)
createUserWithPosts userData postsData = runDB $ do
  userId <- insert $ User
    { userName = userDataName userData
    , userEmail = userDataEmail userData
    , userAge = userDataAge userData
    , userCreatedAt = utcNow
    }
  
  forM_ postsData $ \postData -> insert $ Post
    { postTitle = postDataTitle postData
    , postContent = postDataContent postData
    , postAuthorId = userId
    , postPublished = postDataPublished postData
    , postCreatedAt = utcNow
    }
  
  return userId
```

## 4. API设计

### 概念定义

RESTful API设计提供标准化的数据交换接口。

### Haskell实现

```haskell
-- API类型定义
data UserData = UserData
  { userDataName :: Text
  , userDataEmail :: Text
  , userDataAge :: Maybe Int
  } deriving (Show, Generic)

data PostData = PostData
  { postDataTitle :: Text
  , postDataContent :: Textarea
  , postDataPublished :: Bool
  } deriving (Show, Generic)

-- JSON实例
instance ToJSON UserData
instance FromJSON UserData
instance ToJSON PostData
instance FromJSON PostData

-- API路由
mkYesodData "ApiApp" [parseRoutes|
/api/v1/users UsersApiR GET POST
/api/v1/users/#Int UserApiR GET PUT DELETE
/api/v1/users/#Int/posts UserPostsApiR GET POST
/api/v1/posts PostsApiR GET POST
/api/v1/posts/#Int PostApiR GET PUT DELETE
|]

-- API处理器
getUsersApiR :: Handler Value
getUsersApiR = do
  page <- lookupGetParam "page" >>= maybe (return 1) readMay
  limit <- lookupGetParam "limit" >>= maybe (return 10) readMay
  users <- getUsersPaginated page limit
  total <- getUsersCount
  returnJson $ object
    [ "data" .= users
    , "pagination" .= object
        [ "page" .= page
        , "limit" .= limit
        , "total" .= total
        , "pages" .= ((total - 1) `div` limit + 1)
        ]
    ]

postUsersApiR :: Handler Value
postUsersApiR = do
  userData <- requireJsonBody :: Handler UserData
  -- 验证数据
  case validateUserData userData of
    Left errors -> sendResponseStatus status400 $ object ["errors" .= errors]
    Right _ -> do
      userId <- createUser userData
      sendResponseStatus status201 $ object
        [ "id" .= userId
        , "message" .= ("User created successfully" :: Text)
        ]

getUserApiR :: Int -> Handler Value
getUserApiR userId = do
  user <- getUserById userId
  case user of
    Just u -> returnJson u
    Nothing -> sendResponseStatus status404 $ object
      ["error" .= ("User not found" :: Text)]

putUserApiR :: Int -> Handler Value
putUserApiR userId = do
  userData <- requireJsonBody :: Handler UserData
  case validateUserData userData of
    Left errors -> sendResponseStatus status400 $ object ["errors" .= errors]
    Right _ -> do
      success <- updateUser userId userData
      if success
        then returnJson $ object ["message" .= ("User updated successfully" :: Text)]
        else sendResponseStatus status404 $ object ["error" .= ("User not found" :: Text)]

-- 数据验证
validateUserData :: UserData -> Either [Text] ()
validateUserData userData = do
  when (Text.null $ userDataName userData) $
    Left ["Name cannot be empty"]
  when (Text.null $ userDataEmail userData) $
    Left ["Email cannot be empty"]
  when (not $ isValidEmail $ userDataEmail userData) $
    Left ["Invalid email format"]
  when (maybe False (< 0) $ userDataAge userData) $
    Left ["Age cannot be negative"]
  return ()

isValidEmail :: Text -> Bool
isValidEmail email = 
  let emailRegex = "^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\\.[a-zA-Z]{2,}$"
  in email =~ emailRegex
```

## 5. 中间件和认证

### 概念定义

中间件提供请求处理管道，认证确保API安全性。

### Haskell实现

```haskell
-- 认证中间件
import Data.JWT
import Web.JWT

-- JWT认证
data AuthUser = AuthUser
  { authUserId :: Int
  , authUserName :: Text
  , authUserEmail :: Text
  }

-- 认证中间件
authMiddleware :: Handler AuthUser -> Handler a -> Handler a
authMiddleware authHandler protectedHandler = do
  token <- lookupHeader "Authorization"
  case token of
    Just authHeader -> do
      case parseToken authHeader of
        Just user -> protectedHandler
        Nothing -> sendResponseStatus status401 $ object
          ["error" .= ("Invalid token" :: Text)]
    Nothing -> sendResponseStatus status401 $ object
      ["error" .= ("Missing authorization header" :: Text)]

-- 解析JWT令牌
parseToken :: Text -> Maybe AuthUser
parseToken authHeader = do
  let token = Text.drop 7 authHeader  -- 移除 "Bearer "
  case decodeAndVerifySignature secret token of
    Right claims -> do
      userId <- claims .: "user_id"
      userName <- claims .: "user_name"
      userEmail <- claims .: "user_email"
      return $ AuthUser userId userName userEmail
    Left _ -> Nothing

-- 登录处理器
postLoginR :: Handler Value
postLoginR = do
  loginData <- requireJsonBody :: Handler LoginData
  case authenticateUser loginData of
    Just user -> do
      token <- generateToken user
      returnJson $ object
        [ "token" .= token
        , "user" .= user
        ]
    Nothing -> sendResponseStatus status401 $ object
      ["error" .= ("Invalid credentials" :: Text)]

-- 生成JWT令牌
generateToken :: AuthUser -> Handler Text
generateToken user = do
  now <- liftIO getCurrentTime
  let claims = ClaimsMap $ Map.fromList
        [ ("user_id", Number $ fromIntegral $ authUserId user)
        , ("user_name", String $ authUserName user)
        , ("user_email", String $ authUserEmail user)
        , ("iat", Number $ fromIntegral $ floor $ utcTimeToPOSIXSeconds now)
        , ("exp", Number $ fromIntegral $ floor $ utcTimeToPOSIXSeconds now + 3600)
        ]
  return $ encodeSigned secret mempty claims

-- 日志中间件
logMiddleware :: Handler a -> Handler a
logMiddleware handler = do
  req <- waiRequest
  startTime <- liftIO getCurrentTime
  result <- handler
  endTime <- liftIO getCurrentTime
  let duration = diffUTCTime endTime startTime
  liftIO $ putStrLn $ show (requestMethod req) ++ " " ++ 
                      show (rawPathInfo req) ++ " " ++ 
                      show duration
  return result
```

## 6. 前端集成

### 概念定义

前端集成提供动态用户界面，支持现代Web开发技术。

### Haskell实现

```haskell
-- 模板引擎
getDashboardR :: Handler Html
getDashboardR = do
  user <- requireAuth
  posts <- getUserPosts $ entityKey user
  stats <- getUserStats $ entityKey user
  defaultLayout [whamlet|
    <div .dashboard>
      <h1>Dashboard
      <div .stats>
        <div .stat>
          <h3>Posts
          <p>#{length posts}
        <div .stat>
          <h3>Views
          <p>#{statsViews stats}
      <div .recent-posts>
        <h2>Recent Posts
        $forall post <- take 5 posts
          <div .post-preview>
            <h3>#{postTitle $ entityVal post}
            <p>#{Text.take 100 $ unTextarea $ postContent $ entityVal post}
            <a href=@{PostR $ entityKey post}>Read more
  |]

-- JavaScript集成
getAppJs :: Handler TypedContent
getAppJs = do
  addHeader "Content-Type" "application/javascript"
  return $ TypedContent "application/javascript" $ 
    toContent [julius|
      // 用户交互
      $(document).ready(function() {
        // AJAX表单提交
        $('.ajax-form').on('submit', function(e) {
          e.preventDefault();
          var form = $(this);
          var data = form.serialize();
          
          $.ajax({
            url: form.attr('action'),
            method: 'POST',
            data: data,
            success: function(response) {
              showNotification('Success!', 'success');
              form[0].reset();
            },
            error: function(xhr) {
              showNotification('Error: ' + xhr.responseText, 'error');
            }
          });
        });
        
        // 实时搜索
        $('#search-input').on('input', function() {
          var query = $(this).val();
          if (query.length > 2) {
            $.get('/api/search?q=' + encodeURIComponent(query), function(data) {
              updateSearchResults(data);
            });
          }
        });
      });
      
      function showNotification(message, type) {
        var notification = $('<div class="notification ' + type + '">' + message + '</div>');
        $('body').append(notification);
        setTimeout(function() {
          notification.fadeOut();
        }, 3000);
      }
    |]

-- CSS样式
getAppCss :: Handler TypedContent
getAppCss = do
  addHeader "Content-Type" "text/css"
  return $ TypedContent "text/css" $ 
    toContent [lucius|
      .dashboard {
        max-width: 1200px;
        margin: 0 auto;
        padding: 20px;
      }
      
      .stats {
        display: flex;
        gap: 20px;
        margin-bottom: 30px;
      }
      
      .stat {
        background: #f5f5f5;
        padding: 20px;
        border-radius: 8px;
        flex: 1;
      }
      
      .post-preview {
        border: 1px solid #ddd;
        padding: 15px;
        margin-bottom: 15px;
        border-radius: 5px;
      }
      
      .notification {
        position: fixed;
        top: 20px;
        right: 20px;
        padding: 15px;
        border-radius: 5px;
        color: white;
        z-index: 1000;
      }
      
      .notification.success {
        background: #4caf50;
      }
      
      .notification.error {
        background: #f44336;
      }
    |]
```

## 7. 部署和性能优化

### 概念定义

部署配置和性能优化确保生产环境的稳定性和效率。

### Haskell实现

```haskell
-- 生产配置
instance Yesod App where
  approot = ApprootStatic "https://myapp.com"
  
  -- 生产环境设置
  shouldLogIO _ _ = return True
  logLevel = LevelWarn
  
  -- 安全设置
  maximumContentLength _ _ = Just $ 10 * 1024 * 1024  -- 10MB
  
  -- 会话设置
  makeSessionBackend _ = Just <$> defaultClientSessionBackend
    120  -- 2小时过期
    "config/client_session_key.aes"

-- 性能监控
import System.Monitoring

-- 性能指标收集
performanceMiddleware :: Handler a -> Handler a
performanceMiddleware handler = do
  startTime <- liftIO getCurrentTime
  startMemory <- liftIO getMemoryUsage
  result <- handler
  endTime <- liftIO getCurrentTime
  endMemory <- liftIO getMemoryUsage
  
  let duration = diffUTCTime endTime startTime
      memoryDelta = endMemory - startMemory
  
  liftIO $ recordMetrics duration memoryDelta
  return result

-- 缓存系统
import Data.Cache

-- 内存缓存
userCache :: Cache Int User
userCache = newCache 1000  -- 1000个条目

-- 缓存中间件
cachedUser :: Int -> Handler (Maybe User)
cachedUser userId = do
  cached <- liftIO $ lookupCache userCache userId
  case cached of
    Just user -> return $ Just user
    Nothing -> do
      user <- getUserById userId
      case user of
        Just u -> liftIO $ insertCache userCache userId u
        Nothing -> return Nothing
      return user

-- 数据库连接池
import Database.Persist.Sqlite
import Control.Monad.Logger

-- 连接池配置
mkYesodData "App" [parseRoutes|
/ HomeR GET
|]

instance Yesod App where
  connectionPool = runStdoutLoggingT $ createSqlitePool "app.db" 10

-- 应用启动
main :: IO ()
main = do
  -- 初始化数据库
  runStdoutLoggingT $ withSqlitePool "app.db" 10 $ \pool -> do
    runSqlPool (runMigration migrateAll) pool
    
    -- 启动应用
    warp 3000 $ App
      { appStatic = static "static"
      , appDatabase = pool
      }
```

## 总结

本文档展示了使用Haskell进行Web开发的完整解决方案：

1. **Web框架**：使用Yesod提供类型安全的Web开发
2. **数据库集成**：通过Persistent进行数据持久化
3. **API设计**：RESTful API设计和实现
4. **认证中间件**：JWT认证和授权
5. **前端集成**：模板引擎和JavaScript集成
6. **部署优化**：生产环境配置和性能监控

Haskell的强类型系统和函数式特性为构建安全、可靠的Web应用提供了坚实基础。

---

**相关链接**：

- [函数式编程基础](../01-Basic-Examples/01-Functional-Programming-Basics.md)
- [类型类与单子](../02-Advanced-Features/01-Type-Classes-and-Monads.md)
- [排序算法](../03-Algorithm-Implementation/01-Sorting-Algorithms.md)
- [定理证明](../04-Formal-Proofs/01-Theorem-Proving-Examples.md)
