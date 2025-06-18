# 模块系统 (Module System)

## 概述

Haskell的模块系统是组织和管理代码的核心机制，提供了命名空间隔离、代码重用和接口抽象等功能。本文档系统性介绍Haskell模块系统的理论基础、数学模型和实际应用。

## 目录

1. [基本概念](#基本概念)
2. [模块定义](#模块定义)
3. [导出导入](#导出导入)
4. [命名空间](#命名空间)
5. [Haskell实现](#haskell实现)
6. [最佳实践](#最佳实践)

## 基本概念

### 定义 4.1: 模块 (Module)

模块是Haskell代码的基本组织单元，包含类型、函数、类等定义。

### 定义 4.2: 模块系统 (Module System)

模块系统是管理模块间关系和依赖的机制。

### 模块的数学定义

模块可以表示为：
$$M = (T, F, C, E)$$

其中：

- $T$ 是类型定义集合
- $F$ 是函数定义集合
- $C$ 是类定义集合
- $E$ 是导出列表

## 模块定义

### 基本模块语法

```haskell
-- 模块声明
module ModuleName where
  -- 模块内容

-- 带导出的模块
module ModuleName 
  ( export1
  , export2
  , export3
  ) where
  -- 模块内容

-- 带导入的模块
module ModuleName 
  ( export1
  , export2
  ) where
  
import OtherModule
import qualified OtherModule as OM
import OtherModule hiding (hiddenFunction)
```

### 模块层次结构

```haskell
-- 层次模块
module Data.List 
  ( head
  , tail
  , map
  , filter
  ) where

-- 子模块
module Data.List.Utils where
  import Data.List
  
-- 主模块
module Main where
  import Data.List
  import Data.List.Utils
```

## 导出导入

### 导出语法

```haskell
-- 导出所有
module ModuleName (..) where

-- 选择性导出
module ModuleName 
  ( Type1(..)        -- 导出类型及其所有构造函数
  , Type2(Con1, Con2) -- 导出类型及指定构造函数
  , function1         -- 导出函数
  , function2
  , Class1(..)        -- 导出类及其所有方法
  ) where

-- 重新导出
module ModuleName 
  ( module OtherModule
  , additionalExport
  ) where
  
import OtherModule
```

### 导入语法

```haskell
-- 基本导入
import Data.List

-- 限定导入
import qualified Data.List as List

-- 选择性导入
import Data.List (head, tail, map)

-- 隐藏导入
import Data.List hiding (head, tail)

-- 模式导入
import Data.Maybe (Maybe(..))

-- 实例导入
import Data.List (foldr)
```

## 命名空间

### 命名空间管理

```haskell
-- 避免命名冲突
module MyModule where
  import qualified Data.List as L
  import qualified Data.Map as M
  
  -- 使用限定名称
  myFunction = L.map (*2) [1,2,3]
  myMap = M.fromList [("a", 1), ("b", 2)]

-- 重命名导入
module AnotherModule where
  import Data.List (map as listMap)
  import Data.Map (map as mapMap)
  
  -- 使用重命名后的函数
  result1 = listMap (*2) [1,2,3]
  result2 = mapMap (\k v -> v * 2) myMap
```

### 模块别名

```haskell
-- 创建模块别名
module MyApp.Data.Processing as Processing where
  -- 处理相关函数

-- 使用别名
module MyApp.Main where
  import MyApp.Data.Processing as Processing
  
  main = Processing.processData input
```

## Haskell实现

### 综合示例

```haskell
-- 数学运算模块
module Math.Operations 
  ( add
  , subtract
  , multiply
  , divide
  , MathError(..)
  ) where

-- 错误类型
data MathError = DivisionByZero | InvalidInput

-- 基本运算
add :: Num a => a -> a -> a
add = (+)

subtract :: Num a => a -> a -> a
subtract = (-)

multiply :: Num a => a -> a -> a
multiply = (*)

divide :: (Fractional a, Eq a) => a -> a -> Either MathError a
divide _ 0 = Left DivisionByZero
divide x y = Right (x / y)

-- 高级运算模块
module Math.Advanced 
  ( power
  , sqrt
  , log
  , MathError(..)
  ) where

import Math.Operations (MathError(..))

-- 高级运算
power :: (Num a, Integral b) => a -> b -> a
power = (^)

sqrt :: (Floating a) => a -> a
sqrt = Prelude.sqrt

log :: (Floating a) => a -> a
log = Prelude.log

-- 统计模块
module Math.Statistics 
  ( mean
  , variance
  , standardDeviation
  ) where

import Math.Operations (add, divide)
import Math.Advanced (power, sqrt)

-- 统计函数
mean :: (Fractional a) => [a] -> Maybe a
mean [] = Nothing
mean xs = Just (sum xs / fromIntegral (length xs))

variance :: (Fractional a) => [a] -> Maybe a
variance xs = do
  m <- mean xs
  let squaredDiffs = map (\x -> power (x - m) 2) xs
  mean squaredDiffs

standardDeviation :: (Floating a) => [a] -> Maybe a
standardDeviation xs = do
  v <- variance xs
  return (sqrt v)

-- 主模块
module Main where

import Math.Operations (add, subtract, multiply, divide, MathError(..))
import Math.Advanced (power, sqrt)
import Math.Statistics (mean, variance, standardDeviation)

-- 主函数
main :: IO ()
main = do
  putStrLn "Math Operations Demo"
  
  -- 基本运算
  putStrLn $ "5 + 3 = " ++ show (add 5 3)
  putStrLn $ "5 - 3 = " ++ show (subtract 5 3)
  putStrLn $ "5 * 3 = " ++ show (multiply 5 3)
  
  case divide 10 2 of
    Left err -> putStrLn $ "Error: " ++ show err
    Right result -> putStrLn $ "10 / 2 = " ++ show result
  
  -- 高级运算
  putStrLn $ "2^3 = " ++ show (power 2 3)
  putStrLn $ "sqrt 16 = " ++ show (sqrt 16)
  
  -- 统计运算
  let dataSet = [1, 2, 3, 4, 5]
  putStrLn $ "Data: " ++ show dataSet
  
  case mean dataSet of
    Nothing -> putStrLn "Cannot calculate mean of empty list"
    Just m -> putStrLn $ "Mean: " ++ show m
  
  case variance dataSet of
    Nothing -> putStrLn "Cannot calculate variance"
    Just v -> putStrLn $ "Variance: " ++ show v
  
  case standardDeviation dataSet of
    Nothing -> putStrLn "Cannot calculate standard deviation"
    Just sd -> putStrLn $ "Standard Deviation: " ++ show sd
```

### 实际应用示例

```haskell
-- 数据库模块
module Database.Connection 
  ( Connection
  , connect
  , disconnect
  , executeQuery
  , DatabaseError(..)
  ) where

import Control.Exception (Exception)

-- 数据库错误
data DatabaseError = ConnectionFailed | QueryFailed | InvalidQuery

-- 连接类型
data Connection = Connection String

-- 数据库操作
connect :: String -> IO (Either DatabaseError Connection)
connect url = return (Right (Connection url))

disconnect :: Connection -> IO ()
disconnect _ = putStrLn "Disconnected"

executeQuery :: Connection -> String -> IO (Either DatabaseError String)
executeQuery _ query = return (Right ("Result of: " ++ query))

-- 用户模块
module User.Model 
  ( User(..)
  , createUser
  , updateUser
  , deleteUser
  ) where

-- 用户类型
data User = User
  { userId :: Int
  , userName :: String
  , userEmail :: String
  }

-- 用户操作
createUser :: String -> String -> User
createUser name email = User 0 name email

updateUser :: User -> String -> String -> User
updateUser user name email = user { userName = name, userEmail = email }

deleteUser :: User -> User
deleteUser user = user { userId = -1 }

-- 用户服务模块
module User.Service 
  ( UserService(..)
  , createUserService
  , saveUser
  , findUser
  ) where

import Database.Connection (Connection, executeQuery, DatabaseError)
import User.Model (User(..), createUser, updateUser)

-- 用户服务
data UserService = UserService Connection

-- 服务操作
createUserService :: Connection -> UserService
createUserService conn = UserService conn

saveUser :: UserService -> User -> IO (Either DatabaseError Bool)
saveUser (UserService conn) user = do
  let query = "INSERT INTO users VALUES (" ++ show (userId user) ++ ", '" ++ userName user ++ "', '" ++ userEmail user ++ "')"
  result <- executeQuery conn query
  case result of
    Left err -> return (Left err)
    Right _ -> return (Right True)

findUser :: UserService -> Int -> IO (Either DatabaseError (Maybe User))
findUser (UserService conn) id = do
  let query = "SELECT * FROM users WHERE id = " ++ show id
  result <- executeQuery conn query
  case result of
    Left err -> return (Left err)
    Right _ -> return (Right (Just (User id "John" "john@example.com")))

-- 应用主模块
module Application.Main where

import Database.Connection (connect, disconnect, DatabaseError)
import User.Model (createUser)
import User.Service (createUserService, saveUser, findUser)

-- 应用主函数
appMain :: IO ()
appMain = do
  putStrLn "Starting Application"
  
  -- 连接数据库
  connResult <- connect "postgresql://localhost/mydb"
  case connResult of
    Left err -> putStrLn $ "Database connection failed: " ++ show err
    Right conn -> do
      putStrLn "Connected to database"
      
      -- 创建用户服务
      let userService = createUserService conn
      
      -- 创建用户
      let newUser = createUser "Alice" "alice@example.com"
      
      -- 保存用户
      saveResult <- saveUser userService newUser
      case saveResult of
        Left err -> putStrLn $ "Failed to save user: " ++ show err
        Right _ -> putStrLn "User saved successfully"
      
      -- 查找用户
      findResult <- findUser userService 1
      case findResult of
        Left err -> putStrLn $ "Failed to find user: " ++ show err
        Right maybeUser -> case maybeUser of
          Nothing -> putStrLn "User not found"
          Just user -> putStrLn $ "Found user: " ++ userName user
      
      -- 断开连接
      disconnect conn
      putStrLn "Application finished"
```

## 最佳实践

1. **模块命名**: 使用层次化的模块命名约定。
2. **导出控制**: 只导出必要的接口，隐藏实现细节。
3. **导入管理**: 使用限定导入避免命名冲突。
4. **模块组织**: 按功能或层次组织模块。
5. **文档化**: 为每个模块提供清晰的文档。

## 相关链接

- [包管理](./02-Package-Management.md)
- [项目结构](./03-Project-Structure.md)
- [依赖管理](./04-Dependency-Management.md)

---

**作者**: 形式化知识体系重构项目  
**最后更新**: 2024年12月  
**版本**: 1.0
