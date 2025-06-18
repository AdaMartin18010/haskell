# 包管理 (Package Management)

## 概述

Haskell的包管理系统是管理项目依赖、版本控制和构建配置的核心工具。本文档系统性介绍Haskell包管理的理论基础、数学模型和实际应用，涵盖Cabal、Stack等主要工具。

## 目录

1. [基本概念](#基本概念)
2. [包定义](#包定义)
3. [依赖管理](#依赖管理)
4. [版本控制](#版本控制)
5. [Haskell实现](#haskell实现)
6. [最佳实践](#最佳实践)

## 基本概念

### 定义 4.2.1: 包 (Package)

包是Haskell代码的发布单元，包含模块、依赖关系和元数据。

### 定义 4.2.2: 包管理 (Package Management)

包管理是管理包的创建、发布、安装和依赖解析的过程。

### 包的数学定义

包可以表示为：
$$P = (N, V, D, M, C)$$

其中：

- $N$ 是包名
- $V$ 是版本号
- $D$ 是依赖集合
- $M$ 是模块集合
- $C$ 是配置信息

## 包定义

### Cabal文件结构

```haskell
-- my-package.cabal
name:                my-package
version:             1.0.0.0
synopsis:            A sample Haskell package
description:         This is a sample package for demonstration
license:             MIT
author:              Your Name
maintainer:          your.email@example.com
category:            Development
build-depends:       base >= 4.7 && < 5
                    , containers
                    , text
                    , aeson
exposed-modules:     MyPackage.Core
                    , MyPackage.Utils
other-modules:       MyPackage.Internal
default-language:    Haskell2010
```

### 包配置

```haskell
-- 库配置
library
  exposed-modules:     MyPackage.Core
                      , MyPackage.Utils
  build-depends:       base >= 4.7 && < 5
                      , containers
                      , text
  hs-source-dirs:      src
  default-language:    Haskell2010

-- 可执行文件配置
executable my-package-exe
  main-is:             Main.hs
  build-depends:       base >= 4.7 && < 5
                      , my-package
  hs-source-dirs:      app
  default-language:    Haskell2010

-- 测试配置
test-suite my-package-test
  type:                exitcode-stdio-1.0
  main-is:             Spec.hs
  build-depends:       base >= 4.7 && < 5
                      , my-package
                      , hspec
  hs-source-dirs:      test
  default-language:    Haskell2010
```

## 依赖管理

### 依赖解析

```haskell
-- 依赖图
data DependencyGraph = DependencyGraph
  { nodes :: Map PackageName PackageInfo
  , edges :: Map PackageName [PackageName]
  }

-- 包信息
data PackageInfo = PackageInfo
  { packageName :: PackageName
  , packageVersion :: Version
  , dependencies :: [Dependency]
  , modules :: [ModuleName]
  }

-- 依赖
data Dependency = Dependency
  { depName :: PackageName
  , versionConstraint :: VersionConstraint
  }

-- 版本约束
data VersionConstraint = 
    AnyVersion
  | ThisVersion Version
  | LaterVersion Version
  | EarlierVersion Version
  | UnionVersion VersionConstraint VersionConstraint
  | IntersectVersion VersionConstraint VersionConstraint

-- 依赖解析器
resolveDependencies :: [PackageInfo] -> Either String DependencyGraph
resolveDependencies packages = do
  let graph = buildDependencyGraph packages
  validateDependencies graph
  return graph

-- 构建依赖图
buildDependencyGraph :: [PackageInfo] -> DependencyGraph
buildDependencyGraph packages = DependencyGraph
  { nodes = Map.fromList [(packageName pkg, pkg) | pkg <- packages]
  , edges = Map.fromList [(packageName pkg, map depName (dependencies pkg)) | pkg <- packages]
  }

-- 验证依赖
validateDependencies :: DependencyGraph -> Either String ()
validateDependencies graph = do
  -- 检查循环依赖
  when (hasCycles graph) $ Left "Circular dependencies detected"
  -- 检查版本冲突
  when (hasVersionConflicts graph) $ Left "Version conflicts detected"
  return ()
```

### 版本约束

```haskell
-- 版本号
data Version = Version
  { major :: Int
  , minor :: Int
  , patch :: Int
  , build :: [String]
  }

-- 版本比较
instance Ord Version where
  compare (Version m1 n1 p1 _) (Version m2 n2 p2 _) =
    compare (m1, n1, p1) (m2, n2, p2)

-- 版本约束检查
satisfiesConstraint :: Version -> VersionConstraint -> Bool
satisfiesConstraint version constraint = case constraint of
  AnyVersion -> True
  ThisVersion v -> version == v
  LaterVersion v -> version > v
  EarlierVersion v -> version < v
  UnionVersion c1 c2 -> satisfiesConstraint version c1 || satisfiesConstraint version c2
  IntersectVersion c1 c2 -> satisfiesConstraint version c1 && satisfiesConstraint version c2

-- 解析版本约束
parseVersionConstraint :: String -> Either String VersionConstraint
parseVersionConstraint str = case words str of
  [">=", version] -> LaterVersion <$> parseVersion version
  ["<=", version] -> EarlierVersion <$> parseVersion version
  ["==", version] -> ThisVersion <$> parseVersion version
  [">", version] -> LaterVersion <$> parseVersion version
  ["<", version] -> EarlierVersion <$> parseVersion version
  _ -> Left $ "Invalid version constraint: " ++ str
```

## 版本控制

### 语义化版本

```haskell
-- 语义化版本
data SemanticVersion = SemanticVersion
  { major :: Int
  , minor :: Int
  , patch :: Int
  , preRelease :: Maybe String
  , buildMetadata :: Maybe String
  }

-- 版本兼容性
isCompatible :: SemanticVersion -> SemanticVersion -> Bool
isCompatible v1 v2 = major v1 == major v2

-- 版本升级类型
data VersionUpgrade = 
    MajorUpgrade
  | MinorUpgrade
  | PatchUpgrade
  | PreReleaseUpgrade

-- 确定升级类型
upgradeType :: SemanticVersion -> SemanticVersion -> VersionUpgrade
upgradeType old new
  | major new > major old = MajorUpgrade
  | minor new > minor old = MinorUpgrade
  | patch new > patch old = PatchUpgrade
  | otherwise = PreReleaseUpgrade
```

### 版本策略

```haskell
-- 版本策略
data VersionStrategy = 
    ExactVersion
  | LatestVersion
  | CompatibleVersion
  | PinnedVersion Version

-- 版本选择器
selectVersion :: VersionStrategy -> [Version] -> Maybe Version
selectVersion strategy versions = case strategy of
  ExactVersion -> listToMaybe versions
  LatestVersion -> listToMaybe (reverse (sort versions))
  CompatibleVersion -> findCompatibleVersion versions
  PinnedVersion v -> if v `elem` versions then Just v else Nothing

-- 查找兼容版本
findCompatibleVersion :: [Version] -> Maybe Version
findCompatibleVersion [] = Nothing
findCompatibleVersion (v:vs) = 
  let compatible = filter (\x -> major x == major v) (v:vs)
  in listToMaybe (reverse (sort compatible))
```

## Haskell实现

### 综合示例

```haskell
-- 包管理模块
module PackageManagement where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.List (sort, find)

-- 包名类型
type PackageName = String
type ModuleName = String

-- 包信息
data PackageInfo = PackageInfo
  { packageName :: PackageName
  , packageVersion :: Version
  , dependencies :: [Dependency]
  , modules :: [ModuleName]
  , description :: String
  , license :: String
  } deriving (Show, Eq)

-- 版本
data Version = Version
  { major :: Int
  , minor :: Int
  , patch :: Int
  } deriving (Show, Eq, Ord)

-- 依赖
data Dependency = Dependency
  { depName :: PackageName
  , versionConstraint :: VersionConstraint
  } deriving (Show, Eq)

-- 版本约束
data VersionConstraint = 
    AnyVersion
  | ThisVersion Version
  | LaterVersion Version
  | EarlierVersion Version
  | UnionVersion VersionConstraint VersionConstraint
  | IntersectVersion VersionConstraint VersionConstraint
  deriving (Show, Eq)

-- 包管理器
data PackageManager = PackageManager
  { installedPackages :: Map PackageName PackageInfo
  , packageRepository :: Map PackageName [PackageInfo]
  }

-- 创建包管理器
createPackageManager :: PackageManager
createPackageManager = PackageManager
  { installedPackages = Map.empty
  , packageRepository = Map.empty
  }

-- 安装包
installPackage :: PackageManager -> PackageInfo -> Either String PackageManager
installPackage manager package = do
  -- 检查依赖
  deps <- resolveDependencies manager (dependencies package)
  -- 安装依赖
  manager' <- installDependencies manager deps
  -- 安装包
  let newInstalled = Map.insert (packageName package) package (installedPackages manager')
  return manager' { installedPackages = newInstalled }

-- 解析依赖
resolveDependencies :: PackageManager -> [Dependency] -> Either String [PackageInfo]
resolveDependencies manager deps = do
  resolved <- mapM (resolveDependency manager) deps
  return resolved

-- 解析单个依赖
resolveDependency :: PackageManager -> Dependency -> Either String PackageInfo
resolveDependency manager dep = do
  let candidates = fromMaybe [] (Map.lookup (depName dep) (packageRepository manager))
  let compatible = filter (\pkg -> satisfiesConstraint (packageVersion pkg) (versionConstraint dep)) candidates
  case compatible of
    [] -> Left $ "No compatible version found for " ++ depName dep
    (pkg:_) -> return pkg

-- 检查版本约束
satisfiesConstraint :: Version -> VersionConstraint -> Bool
satisfiesConstraint version constraint = case constraint of
  AnyVersion -> True
  ThisVersion v -> version == v
  LaterVersion v -> version > v
  EarlierVersion v -> version < v
  UnionVersion c1 c2 -> satisfiesConstraint version c1 || satisfiesConstraint version c2
  IntersectVersion c1 c2 -> satisfiesConstraint version c1 && satisfiesConstraint version c2

-- 安装依赖
installDependencies :: PackageManager -> [PackageInfo] -> Either String PackageManager
installDependencies manager [] = return manager
installDependencies manager (pkg:pkgs) = do
  manager' <- installPackage manager pkg
  installDependencies manager' pkgs

-- 卸载包
uninstallPackage :: PackageManager -> PackageName -> PackageManager
uninstallPackage manager name = manager
  { installedPackages = Map.delete name (installedPackages manager)
  }

-- 列出已安装包
listInstalledPackages :: PackageManager -> [PackageInfo]
listInstalledPackages manager = Map.elems (installedPackages manager)

-- 查找包
findPackage :: PackageManager -> PackageName -> Maybe PackageInfo
findPackage manager name = Map.lookup name (installedPackages manager)

-- 更新包
updatePackage :: PackageManager -> PackageName -> Version -> Either String PackageManager
updatePackage manager name newVersion = do
  case findPackage manager name of
    Nothing -> Left $ "Package " ++ name ++ " not found"
    Just oldPackage -> do
      let updatedPackage = oldPackage { packageVersion = newVersion }
      installPackage manager updatedPackage
```

### 实际应用示例

```haskell
-- 示例包定义
samplePackage :: PackageInfo
samplePackage = PackageInfo
  { packageName = "my-awesome-package"
  , packageVersion = Version 1 0 0
  , dependencies = 
      [ Dependency "base" (LaterVersion (Version 4 7 0))
      , Dependency "containers" AnyVersion
      , Dependency "text" (LaterVersion (Version 1 0 0))
      ]
  , modules = ["MyAwesomePackage.Core", "MyAwesomePackage.Utils"]
  , description = "An awesome Haskell package"
  , license = "MIT"
  }

-- 示例仓库
sampleRepository :: Map PackageName [PackageInfo]
sampleRepository = Map.fromList
  [ ("base", [PackageInfo "base" (Version 4 16 0) [] [] "Haskell base library" "BSD3"])
  , ("containers", [PackageInfo "containers" (Version 0 6 5) [Dependency "base" AnyVersion] [] "Containers library" "BSD3"])
  , ("text", [PackageInfo "text" (Version 1 2 4) [Dependency "base" AnyVersion] [] "Text library" "BSD3"])
  ]

-- 包管理示例
packageManagementExample :: IO ()
packageManagementExample = do
  putStrLn "Package Management Demo"
  
  -- 创建包管理器
  let manager = createPackageManager { packageRepository = sampleRepository }
  
  -- 安装包
  case installPackage manager samplePackage of
    Left err -> putStrLn $ "Installation failed: " ++ err
    Right manager' -> do
      putStrLn "Package installed successfully"
      
      -- 列出已安装包
      let installed = listInstalledPackages manager'
      putStrLn $ "Installed packages: " ++ show (map packageName installed)
      
      -- 查找包
      case findPackage manager' "my-awesome-package" of
        Nothing -> putStrLn "Package not found"
        Just pkg -> putStrLn $ "Found package: " ++ packageName pkg ++ " v" ++ show (packageVersion pkg)
      
      -- 更新包
      let updatedManager = manager' { packageRepository = Map.insert "my-awesome-package" 
          [samplePackage { packageVersion = Version 1 1 0 }] (packageRepository manager') }
      
      case updatePackage updatedManager "my-awesome-package" (Version 1 1 0) of
        Left err -> putStrLn $ "Update failed: " ++ err
        Right _ -> putStrLn "Package updated successfully"
```

### 构建配置示例

```haskell
-- 构建配置
data BuildConfig = BuildConfig
  { buildType :: BuildType
  , compiler :: String
  , optimization :: OptimizationLevel
  , flags :: [String]
  }

data BuildType = 
    Library
  | Executable
  | TestSuite
  | Benchmark

data OptimizationLevel = 
    Debug
  | Release
  | Profile

-- 构建器
data Builder = Builder
  { buildConfig :: BuildConfig
  , sourceFiles :: [FilePath]
  , dependencies :: [PackageName]
  }

-- 构建项目
buildProject :: Builder -> IO (Either String ())
buildProject builder = do
  putStrLn $ "Building with " ++ show (buildType (buildConfig builder))
  putStrLn $ "Compiler: " ++ compiler (buildConfig builder)
  putStrLn $ "Optimization: " ++ show (optimization (buildConfig builder))
  putStrLn $ "Flags: " ++ show (flags (buildConfig builder))
  putStrLn $ "Source files: " ++ show (sourceFiles builder)
  putStrLn $ "Dependencies: " ++ show (dependencies builder)
  return (Right ())

-- 示例构建配置
sampleBuildConfig :: BuildConfig
sampleBuildConfig = BuildConfig
  { buildType = Library
  , compiler = "ghc-9.2.7"
  , optimization = Release
  , flags = ["-Wall", "-Werror"]
  }

sampleBuilder :: Builder
sampleBuilder = Builder
  { buildConfig = sampleBuildConfig
  , sourceFiles = ["src/Main.hs", "src/Utils.hs"]
  , dependencies = ["base", "containers", "text"]
  }
```

## 最佳实践

1. **版本管理**: 使用语义化版本控制。
2. **依赖约束**: 明确指定版本约束，避免过于宽松的约束。
3. **包组织**: 合理组织模块结构，避免循环依赖。
4. **测试**: 为包提供完整的测试套件。
5. **文档**: 提供清晰的包文档和使用示例。

## 相关链接

- [模块系统](./01-Module-System.md)
- [项目结构](./03-Project-Structure.md)
- [依赖管理](./04-Dependency-Management.md)

---

**作者**: 形式化知识体系重构项目  
**最后更新**: 2024年12月  
**版本**: 1.0
