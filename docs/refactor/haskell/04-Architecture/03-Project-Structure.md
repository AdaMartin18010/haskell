# 项目结构 (Project Structure)

## 概述

Haskell项目结构是组织代码、配置文件和资源的标准方式，确保项目的可维护性、可扩展性和团队协作效率。本文档系统性介绍Haskell项目结构的理论基础、数学模型和实际应用。

## 目录

1. [基本概念](#基本概念)
2. [目录组织](#目录组织)
3. [文件布局](#文件布局)
4. [架构模式](#架构模式)
5. [Haskell实现](#haskell实现)
6. [最佳实践](#最佳实践)

## 基本概念

### 定义 4.3.1: 项目结构 (Project Structure)

项目结构是项目中文件和目录的组织方式，定义了代码、配置和资源的布局。

### 定义 4.3.2: 架构模式 (Architecture Pattern)

架构模式是组织代码和模块的标准方式，提供可重用的设计解决方案。

### 项目结构的数学定义

项目结构可以表示为：
$$S = (D, F, R, C)$$

其中：

- $D$ 是目录集合
- $F$ 是文件集合
- $R$ 是关系集合（依赖、包含等）
- $C$ 是约束集合

## 目录组织

### 标准目录结构

```haskell
-- 标准Haskell项目结构
data ProjectStructure = ProjectStructure
  { rootDir :: FilePath
  , sourceDir :: FilePath
  , testDir :: FilePath
  , docsDir :: FilePath
  , configDir :: FilePath
  , buildDir :: FilePath
  }

-- 目录类型
data DirectoryType = 
    SourceDirectory
  | TestDirectory
  | DocumentationDirectory
  | ConfigurationDirectory
  | BuildDirectory
  | ResourceDirectory

-- 目录信息
data DirectoryInfo = DirectoryInfo
  { dirPath :: FilePath
  , dirType :: DirectoryType
  , dirPurpose :: String
  , dirContents :: [FilePath]
  }

-- 创建标准项目结构
createStandardStructure :: FilePath -> ProjectStructure
createStandardStructure root = ProjectStructure
  { rootDir = root
  , sourceDir = root </> "src"
  , testDir = root </> "test"
  , docsDir = root </> "docs"
  , configDir = root </> "config"
  , buildDir = root </> "dist"
  }
```

### 层次化目录结构

```haskell
-- 层次化目录
data HierarchicalStructure = HierarchicalStructure
  { topLevel :: [DirectoryInfo]
  , subDirectories :: Map FilePath [DirectoryInfo]
  , depth :: Int
  }

-- 目录层次
data DirectoryHierarchy = DirectoryHierarchy
  { name :: String
  , children :: [DirectoryHierarchy]
  , files :: [FilePath]
  }

-- 构建目录层次
buildHierarchy :: [FilePath] -> DirectoryHierarchy
buildHierarchy paths = DirectoryHierarchy
  { name = "root"
  , children = groupByDirectory paths
  , files = filter isFile paths
  }

-- 按目录分组
groupByDirectory :: [FilePath] -> [DirectoryHierarchy]
groupByDirectory paths = 
  let grouped = groupBy (takeDirectory) paths
  in map (\group -> DirectoryHierarchy
    { name = takeDirectory (head group)
    , children = groupByDirectory (filter isSubDirectory group)
    , files = filter isFile group
    }) grouped
```

## 文件布局

### 文件组织

```haskell
-- 文件类型
data FileType = 
    SourceFile
  | TestFile
  | ConfigurationFile
  | DocumentationFile
  | BuildFile
  | ResourceFile

-- 文件信息
data FileInfo = FileInfo
  { filePath :: FilePath
  , fileType :: FileType
  , fileSize :: Integer
  , fileModified :: UTCTime
  , fileDependencies :: [FilePath]
  }

-- 文件组织器
data FileOrganizer = FileOrganizer
  { sourceFiles :: [FileInfo]
  , testFiles :: [FileInfo]
  , configFiles :: [FileInfo]
  , docFiles :: [FileInfo]
  }

-- 组织文件
organizeFiles :: [FilePath] -> FileOrganizer
organizeFiles paths = FileOrganizer
  { sourceFiles = filterByType paths SourceFile
  , testFiles = filterByType paths TestFile
  , configFiles = filterByType paths ConfigurationFile
  , docFiles = filterByType paths DocumentationFile
  }

-- 按类型过滤文件
filterByType :: [FilePath] -> FileType -> [FileInfo]
filterByType paths fileType = 
  map (\path -> FileInfo path fileType 0 (read "2024-01-01 00:00:00 UTC") [])
      (filter (\path -> getFileType path == fileType) paths)

-- 获取文件类型
getFileType :: FilePath -> FileType
getFileType path
  | ".hs" `isSuffixOf` path = SourceFile
  | "Test" `isInfixOf` path || "Spec" `isInfixOf` path = TestFile
  | ".cabal" `isSuffixOf` path || ".yaml" `isSuffixOf` path = ConfigurationFile
  | ".md" `isSuffixOf` path || ".txt" `isSuffixOf` path = DocumentationFile
  | otherwise = ResourceFile
```

### 模块组织

```haskell
-- 模块结构
data ModuleStructure = ModuleStructure
  { moduleName :: String
  , modulePath :: FilePath
  , moduleDependencies :: [String]
  , moduleExports :: [String]
  , moduleImports :: [String]
  }

-- 模块组织器
data ModuleOrganizer = ModuleOrganizer
  { coreModules :: [ModuleStructure]
  , utilityModules :: [ModuleStructure]
  , interfaceModules :: [ModuleStructure]
  , internalModules :: [ModuleStructure]
  }

-- 组织模块
organizeModules :: [ModuleStructure] -> ModuleOrganizer
organizeModules modules = ModuleOrganizer
  { coreModules = filter (\m -> "Core" `isInfixOf` moduleName m) modules
  , utilityModules = filter (\m -> "Utils" `isInfixOf` moduleName m) modules
  , interfaceModules = filter (\m -> "Interface" `isInfixOf` moduleName m) modules
  , internalModules = filter (\m -> "Internal" `isInfixOf` moduleName m) modules
  }
```

## 架构模式

### 分层架构

```haskell
-- 分层架构
data LayeredArchitecture = LayeredArchitecture
  { presentationLayer :: [ModuleStructure]
  , businessLayer :: [ModuleStructure]
  , dataLayer :: [ModuleStructure]
  , infrastructureLayer :: [ModuleStructure]
  }

-- 层依赖关系
data LayerDependency = LayerDependency
  { fromLayer :: String
  , toLayer :: String
  , dependencyType :: DependencyType
  }

data DependencyType = 
    DirectDependency
  | InterfaceDependency
  | DataDependency

-- 构建分层架构
buildLayeredArchitecture :: [ModuleStructure] -> LayeredArchitecture
buildLayeredArchitecture modules = LayeredArchitecture
  { presentationLayer = filter (\m -> "UI" `isInfixOf` moduleName m || "Controller" `isInfixOf` moduleName m) modules
  , businessLayer = filter (\m -> "Service" `isInfixOf` moduleName m || "Business" `isInfixOf` moduleName m) modules
  , dataLayer = filter (\m -> "Repository" `isInfixOf` moduleName m || "Data" `isInfixOf` moduleName m) modules
  , infrastructureLayer = filter (\m -> "Config" `isInfixOf` moduleName m || "Infra" `isInfixOf` moduleName m) modules
  }

-- 验证层依赖
validateLayerDependencies :: LayeredArchitecture -> [LayerDependency] -> Bool
validateLayerDependencies arch deps = 
  all (\dep -> isValidDependency arch dep) deps

-- 检查依赖有效性
isValidDependency :: LayeredArchitecture -> LayerDependency -> Bool
isValidDependency arch dep = case (fromLayer dep, toLayer dep) of
  ("presentation", "business") -> True
  ("presentation", "data") -> False
  ("business", "data") -> True
  ("business", "infrastructure") -> True
  ("data", "infrastructure") -> True
  _ -> False
```

### 模块化架构

```haskell
-- 模块化架构
data ModularArchitecture = ModularArchitecture
  { modules :: Map String ModuleStructure
  , moduleGraph :: Map String [String]
  , moduleInterfaces :: Map String [String]
  }

-- 模块接口
data ModuleInterface = ModuleInterface
  { interfaceName :: String
  , interfaceMethods :: [String]
  , interfaceTypes :: [String]
  }

-- 构建模块化架构
buildModularArchitecture :: [ModuleStructure] -> ModularArchitecture
buildModularArchitecture modules = ModularArchitecture
  { modules = Map.fromList [(moduleName m, m) | m <- modules]
  , moduleGraph = buildModuleGraph modules
  , moduleInterfaces = buildModuleInterfaces modules
  }

-- 构建模块图
buildModuleGraph :: [ModuleStructure] -> Map String [String]
buildModuleGraph modules = Map.fromList
  [(moduleName m, moduleDependencies m) | m <- modules]

-- 构建模块接口
buildModuleInterfaces :: [ModuleStructure] -> Map String [String]
buildModuleInterfaces modules = Map.fromList
  [(moduleName m, moduleExports m) | m <- modules]
```

## Haskell实现

### 综合示例

```haskell
-- 项目结构管理模块
module ProjectStructure where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Time (UTCTime)
import System.FilePath ((</>), takeDirectory, takeFileName)

-- 项目结构类型
data ProjectStructure = ProjectStructure
  { rootDir :: FilePath
  , sourceDir :: FilePath
  , testDir :: FilePath
  , docsDir :: FilePath
  , configDir :: FilePath
  , buildDir :: FilePath
  } deriving (Show, Eq)

-- 文件类型
data FileType = 
    SourceFile
  | TestFile
  | ConfigurationFile
  | DocumentationFile
  | BuildFile
  | ResourceFile
  deriving (Show, Eq)

-- 文件信息
data FileInfo = FileInfo
  { filePath :: FilePath
  , fileType :: FileType
  , fileSize :: Integer
  , fileModified :: UTCTime
  , fileDependencies :: [FilePath]
  } deriving (Show, Eq)

-- 模块结构
data ModuleStructure = ModuleStructure
  { moduleName :: String
  , modulePath :: FilePath
  , moduleDependencies :: [String]
  , moduleExports :: [String]
  , moduleImports :: [String]
  } deriving (Show, Eq)

-- 项目分析器
data ProjectAnalyzer = ProjectAnalyzer
  { projectStructure :: ProjectStructure
  , files :: [FileInfo]
  , modules :: [ModuleStructure]
  }

-- 创建标准项目结构
createStandardStructure :: FilePath -> ProjectStructure
createStandardStructure root = ProjectStructure
  { rootDir = root
  , sourceDir = root </> "src"
  , testDir = root </> "test"
  , docsDir = root </> "docs"
  , configDir = root </> "config"
  , buildDir = root </> "dist"
  }

-- 分析项目
analyzeProject :: ProjectStructure -> IO ProjectAnalyzer
analyzeProject structure = do
  files <- scanFiles structure
  modules <- analyzeModules files
  return ProjectAnalyzer
    { projectStructure = structure
    , files = files
    , modules = modules
    }

-- 扫描文件
scanFiles :: ProjectStructure -> IO [FileInfo]
scanFiles structure = do
  sourceFiles <- scanDirectory (sourceDir structure) SourceFile
  testFiles <- scanDirectory (testDir structure) TestFile
  configFiles <- scanDirectory (configDir structure) ConfigurationFile
  docFiles <- scanDirectory (docsDir structure) DocumentationFile
  return (sourceFiles ++ testFiles ++ configFiles ++ docFiles)

-- 扫描目录
scanDirectory :: FilePath -> FileType -> IO [FileInfo]
scanDirectory dir fileType = do
  -- 简化实现，实际会扫描文件系统
  return [FileInfo (dir </> "example.hs") fileType 1024 (read "2024-01-01 00:00:00 UTC") []]

-- 分析模块
analyzeModules :: [FileInfo] -> IO [ModuleStructure]
analyzeModules files = do
  let sourceFiles = filter (\f -> fileType f == SourceFile) files
  mapM analyzeModule sourceFiles

-- 分析单个模块
analyzeModule :: FileInfo -> IO ModuleStructure
analyzeModule file = do
  let moduleName = takeModuleName (filePath file)
  return ModuleStructure
    { moduleName = moduleName
    , modulePath = filePath file
    , moduleDependencies = []
    , moduleExports = []
    , moduleImports = []
    }

-- 提取模块名
takeModuleName :: FilePath -> String
takeModuleName path = 
  let fileName = takeFileName path
  in if ".hs" `isSuffixOf` fileName 
     then take (length fileName - 3) fileName 
     else fileName

-- 验证项目结构
validateProjectStructure :: ProjectStructure -> [String]
validateProjectStructure structure = 
  concat [validateDirectory (sourceDir structure) "Source"
         , validateDirectory (testDir structure) "Test"
         , validateDirectory (docsDir structure) "Documentation"
         , validateDirectory (configDir structure) "Configuration"]

-- 验证目录
validateDirectory :: FilePath -> String -> [String]
validateDirectory dir name = 
  -- 简化实现，实际会检查目录是否存在
  []

-- 生成项目报告
generateProjectReport :: ProjectAnalyzer -> String
generateProjectReport analyzer = 
  "Project Structure Report\n" ++
  "=======================\n" ++
  "Root Directory: " ++ rootDir (projectStructure analyzer) ++ "\n" ++
  "Source Files: " ++ show (length (filter (\f -> fileType f == SourceFile) (files analyzer))) ++ "\n" ++
  "Test Files: " ++ show (length (filter (\f -> fileType f == TestFile) (files analyzer))) ++ "\n" ++
  "Modules: " ++ show (length (modules analyzer)) ++ "\n" ++
  "Module Names: " ++ show (map moduleName (modules analyzer)) ++ "\n"
```

### 实际应用示例

```haskell
-- 示例项目结构
sampleProjectStructure :: ProjectStructure
sampleProjectStructure = createStandardStructure "/path/to/my-project"

-- 示例文件
sampleFiles :: [FileInfo]
sampleFiles = 
  [ FileInfo "src/Main.hs" SourceFile 1024 (read "2024-01-01 00:00:00 UTC") []
  , FileInfo "src/Utils.hs" SourceFile 2048 (read "2024-01-01 00:00:00 UTC") []
  , FileInfo "test/MainSpec.hs" TestFile 512 (read "2024-01-01 00:00:00 UTC") []
  , FileInfo "my-project.cabal" ConfigurationFile 256 (read "2024-01-01 00:00:00 UTC") []
  , FileInfo "README.md" DocumentationFile 1024 (read "2024-01-01 00:00:00 UTC") []
  ]

-- 示例模块
sampleModules :: [ModuleStructure]
sampleModules = 
  [ ModuleStructure "Main" "src/Main.hs" ["Utils"] ["main"] ["System.IO"]
  , ModuleStructure "Utils" "src/Utils.hs" [] ["helperFunction"] ["Data.List"]
  ]

-- 项目结构示例
projectStructureExample :: IO ()
projectStructureExample = do
  putStrLn "Project Structure Demo"
  
  -- 创建项目结构
  let structure = sampleProjectStructure
  
  -- 分析项目
  analyzer <- analyzeProject structure
  
  -- 生成报告
  let report = generateProjectReport analyzer
  putStrLn report
  
  -- 验证结构
  let issues = validateProjectStructure structure
  if null issues
    then putStrLn "Project structure is valid"
    else putStrLn $ "Issues found: " ++ show issues
  
  -- 显示模块信息
  putStrLn "\nModule Information:"
  mapM_ (\module' -> putStrLn $ "  " ++ moduleName module' ++ " -> " ++ modulePath module') (modules analyzer)
```

### 架构模式示例

```haskell
-- 分层架构示例
layeredArchitectureExample :: IO ()
layeredArchitectureExample = do
  putStrLn "Layered Architecture Demo"
  
  -- 定义层
  let presentationModules = 
        [ ModuleStructure "UI.Controller" "src/UI/Controller.hs" ["Business.Service"] [] []
        , ModuleStructure "UI.View" "src/UI/View.hs" ["UI.Controller"] [] []
        ]
  
  let businessModules = 
        [ ModuleStructure "Business.Service" "src/Business/Service.hs" ["Data.Repository"] [] []
        , ModuleStructure "Business.Logic" "src/Business/Logic.hs" ["Business.Service"] [] []
        ]
  
  let dataModules = 
        [ ModuleStructure "Data.Repository" "src/Data/Repository.hs" ["Infrastructure.Database"] [] []
        , ModuleStructure "Data.Model" "src/Data/Model.hs" [] [] []
        ]
  
  let infrastructureModules = 
        [ ModuleStructure "Infrastructure.Database" "src/Infrastructure/Database.hs" [] [] []
        , ModuleStructure "Infrastructure.Config" "src/Infrastructure/Config.hs" [] [] []
        ]
  
  let allModules = presentationModules ++ businessModules ++ dataModules ++ infrastructureModules
  
  -- 构建分层架构
  let layeredArch = LayeredArchitecture
        { presentationLayer = presentationModules
        , businessLayer = businessModules
        , dataLayer = dataModules
        , infrastructureLayer = infrastructureModules
        }
  
  -- 定义依赖关系
  let dependencies = 
        [ LayerDependency "presentation" "business" DirectDependency
        , LayerDependency "business" "data" DirectDependency
        , LayerDependency "data" "infrastructure" DirectDependency
        ]
  
  -- 验证依赖
  let isValid = validateLayerDependencies layeredArch dependencies
  putStrLn $ "Architecture is valid: " ++ show isValid
  
  -- 显示层信息
  putStrLn "\nLayer Information:"
  putStrLn $ "Presentation Layer: " ++ show (map moduleName (presentationLayer layeredArch))
  putStrLn $ "Business Layer: " ++ show (map moduleName (businessLayer layeredArch))
  putStrLn $ "Data Layer: " ++ show (map moduleName (dataLayer layeredArch))
  putStrLn $ "Infrastructure Layer: " ++ show (map moduleName (infrastructureLayer layeredArch))
```

## 最佳实践

1. **目录命名**: 使用清晰、一致的目录命名约定。
2. **模块组织**: 按功能和层次组织模块。
3. **依赖管理**: 明确管理模块间的依赖关系。
4. **文档结构**: 为项目提供完整的文档结构。
5. **配置分离**: 将配置与代码分离。

## 相关链接

- [模块系统](./01-Module-System.md)
- [包管理](./02-Package-Management.md)
- [依赖管理](./04-Dependency-Management.md)

---

**作者**: 形式化知识体系重构项目  
**最后更新**: 2024年12月  
**版本**: 1.0
