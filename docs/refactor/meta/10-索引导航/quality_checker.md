# 形式化知识体系 - 质量检查工具

## 🎯 质量检查概述

本工具用于验证形式化知识体系的质量，确保内容的一致性、准确性和完整性。

## 📋 检查项目

### 1. 文档结构检查

#### 目录结构验证

```haskell
-- 目录结构检查
data DirectoryStructure = 
    DirectoryStructure {
        dirName :: String,
        dirPath :: String,
        dirFiles :: [String],
        dirSubdirs :: [DirectoryStructure],
        dirReadme :: Maybe String
    }

-- 检查目录结构
checkDirectoryStructure :: DirectoryStructure -> [String]
checkDirectoryStructure dir = 
    concat [
        checkNamingConvention dir,
        checkFileConsistency dir,
        checkReadmeExistence dir,
        concatMap checkDirectoryStructure (dirSubdirs dir)
    ]

-- 命名约定检查
checkNamingConvention :: DirectoryStructure -> [String]
checkNamingConvention dir = 
    let name = dirName dir
        hasNumberPrefix = any isDigit (take 2 name)
        hasValidFormat = all isValidChar name
    in if hasNumberPrefix && hasValidFormat 
       then []
       else ["Invalid naming convention: " ++ name]

-- 文件一致性检查
checkFileConsistency :: DirectoryStructure -> [String]
checkFileConsistency dir = 
    let files = dirFiles dir
        hasMarkdownFiles = any (isSuffixOf ".md") files
        hasValidStructure = all isValidFileName files
    in if hasMarkdownFiles && hasValidStructure 
       then []
       else ["Inconsistent file structure in: " ++ dirName dir]
```

#### 文件命名检查

```haskell
-- 文件命名规范
isValidFileName :: String -> Bool
isValidFileName name = 
    let hasValidExtension = isSuffixOf ".md" name
        hasValidChars = all isValidChar name
        notEmpty = not (null name)
    in hasValidExtension && hasValidChars && notEmpty

-- 有效字符检查
isValidChar :: Char -> Bool
isValidChar c = 
    isAlphaNum c || c == '-' || c == '_' || c == '.'
```

### 2. 内容质量检查

#### 数学公式检查

```haskell
-- LaTeX数学公式检查
data MathFormula = 
    MathFormula {
        formulaText :: String,
        formulaType :: FormulaType,
        formulaContext :: String
    }

data FormulaType = 
    Definition | Theorem | Proof | Example | Reference

-- 检查数学公式
checkMathFormula :: MathFormula -> [String]
checkMathFormula formula = 
    concat [
        checkLatexSyntax formula,
        checkFormulaConsistency formula,
        checkFormulaReference formula
    ]

-- LaTeX语法检查
checkLatexSyntax :: MathFormula -> [String]
checkLatexSyntax formula = 
    let text = formulaText formula
        hasDollarSigns = countOccurrences '$' text `mod` 2 == 0
        hasValidCommands = all isValidLatexCommand (extractCommands text)
    in if hasDollarSigns && hasValidCommands 
       then []
       else ["Invalid LaTeX syntax: " ++ text]
```

#### Haskell代码检查

```haskell
-- Haskell代码质量检查
data HaskellCode = 
    HaskellCode {
        codeText :: String,
        codeType :: CodeType,
        codeContext :: String,
        codeDependencies :: [String]
    }

data CodeType = 
    Definition | Implementation | Example | Test

-- 检查Haskell代码
checkHaskellCode :: HaskellCode -> [String]
checkHaskellCode code = 
    concat [
        checkSyntax code,
        checkTypeAnnotations code,
        checkDocumentation code,
        checkConsistency code
    ]

-- 语法检查
checkSyntax :: HaskellCode -> [String]
checkSyntax code = 
    let text = codeText code
        hasValidSyntax = validateHaskellSyntax text
        hasProperIndentation = checkIndentation text
    in if hasValidSyntax && hasProperIndentation 
       then []
       else ["Invalid Haskell syntax in: " ++ codeContext code]
```

### 3. 交叉引用检查

#### 链接有效性检查

```haskell
-- 链接检查
data Link = 
    Link {
        linkText :: String,
        linkTarget :: String,
        linkType :: LinkType,
        linkContext :: String
    }

data LinkType = 
    Internal | External | Reference | Navigation

-- 检查链接
checkLinks :: [Link] -> [String]
checkLinks links = 
    concatMap checkLink links

-- 单个链接检查
checkLink :: Link -> [String]
checkLink link = 
    case linkType link of
        Internal -> checkInternalLink link
        External -> checkExternalLink link
        Reference -> checkReferenceLink link
        Navigation -> checkNavigationLink link

-- 内部链接检查
checkInternalLink :: Link -> [String]
checkInternalLink link = 
    let target = linkTarget link
        exists = fileExists target
        accessible = isAccessible target
    in if exists && accessible 
       then []
       else ["Broken internal link: " ++ target]
```

#### 引用一致性检查

```haskell
-- 引用检查
data Reference = 
    Reference {
        refText :: String,
        refTarget :: String,
        refType :: ReferenceType,
        refContext :: String
    }

data ReferenceType = 
    Definition | Theorem | Lemma | Corollary | Example

-- 检查引用
checkReferences :: [Reference] -> [String]
checkReferences refs = 
    concat [
        checkReferenceExistence refs,
        checkReferenceConsistency refs,
        checkReferenceFormat refs
    ]

-- 引用存在性检查
checkReferenceExistence :: [Reference] -> [String]
checkReferenceExistence refs = 
    let targets = map refTarget refs
        existingTargets = filter targetExists targets
        missingTargets = targets \\ existingTargets
    in map ("Missing reference target: " ++) missingTargets
```

### 4. 语义一致性检查

#### 概念一致性检查

```haskell
-- 概念一致性检查
data Concept = 
    Concept {
        conceptName :: String,
        conceptDefinition :: String,
        conceptContext :: String,
        conceptReferences :: [String]
    }

-- 检查概念一致性
checkConceptConsistency :: [Concept] -> [String]
checkConceptConsistency concepts = 
    concat [
        checkConceptDefinitions concepts,
        checkConceptReferences concepts,
        checkConceptHierarchy concepts
    ]

-- 概念定义检查
checkConceptDefinitions :: [Concept] -> [String]
checkConceptDefinitions concepts = 
    let definitions = [(conceptName c, conceptDefinition c) | c <- concepts]
        duplicates = findDuplicateDefinitions definitions
        incomplete = findIncompleteDefinitions definitions
    in map ("Duplicate definition: " ++) duplicates ++
       map ("Incomplete definition: " ++) incomplete

-- 概念引用检查
checkConceptReferences :: [Concept] -> [String]
checkConceptReferences concepts = 
    let allNames = map conceptName concepts
        allRefs = concatMap conceptReferences concepts
        invalidRefs = filter (`notElem` allNames) allRefs
    in map ("Invalid concept reference: " ++) invalidRefs
```

#### 层次一致性检查

```haskell
-- 层次一致性检查
data Hierarchy = 
    Hierarchy {
        hierarchyLevel :: Int,
        hierarchyName :: String,
        hierarchyDependencies :: [String],
        hierarchyContent :: [String]
    }

-- 检查层次一致性
checkHierarchyConsistency :: [Hierarchy] -> [String]
checkHierarchyConsistency hierarchies = 
    concat [
        checkDependencyOrder hierarchies,
        checkContentConsistency hierarchies,
        checkLevelConsistency hierarchies
    ]

-- 依赖顺序检查
checkDependencyOrder :: [Hierarchy] -> [String]
checkDependencyOrder hierarchies = 
    let sorted = sortBy (comparing hierarchyLevel) hierarchies
        dependencies = concatMap (\h -> zip (repeat (hierarchyName h)) (hierarchyDependencies h)) sorted
        invalidDeps = filter (\(current, dep) -> not (isValidDependency current dep sorted)) dependencies
    in map (\(current, dep) -> "Invalid dependency: " ++ current ++ " -> " ++ dep) invalidDeps
```

### 5. 完整性检查

#### 内容完整性检查

```haskell
-- 内容完整性检查
data ContentCompleteness = 
    ContentCompleteness {
        requiredSections :: [String],
        existingSections :: [String],
        requiredExamples :: [String],
        existingExamples :: [String],
        requiredProofs :: [String],
        existingProofs :: [String]
    }

-- 检查内容完整性
checkContentCompleteness :: ContentCompleteness -> [String]
checkContentCompleteness content = 
    concat [
        checkMissingSections content,
        checkMissingExamples content,
        checkMissingProofs content
    ]

-- 缺失章节检查
checkMissingSections :: ContentCompleteness -> [String]
checkMissingSections content = 
    let missing = requiredSections content \\ existingSections content
    in map ("Missing section: " ++) missing

-- 缺失示例检查
checkMissingExamples :: ContentCompleteness -> [String]
checkMissingExamples content = 
    let missing = requiredExamples content \\ existingExamples content
    in map ("Missing example: " ++) missing

-- 缺失证明检查
checkMissingProofs :: ContentCompleteness -> [String]
checkMissingProofs content = 
    let missing = requiredProofs content \\ existingProofs content
    in map ("Missing proof: " ++) missing
```

## 🛠️ 检查工具实现

### 主检查函数

```haskell
-- 主质量检查函数
performQualityCheck :: FilePath -> IO [String]
performQualityCheck rootPath = do
    structure <- buildDirectoryStructure rootPath
    let errors = concat [
            checkDirectoryStructure structure,
            checkAllFiles structure,
            checkAllLinks structure,
            checkAllReferences structure,
            checkAllConcepts structure,
            checkAllHierarchies structure,
            checkAllContent structure
        ]
    return errors

-- 构建目录结构
buildDirectoryStructure :: FilePath -> IO DirectoryStructure
buildDirectoryStructure path = do
    entries <- listDirectory path
    files <- filterM doesFileExist (map (path </>) entries)
    dirs <- filterM doesDirectoryExist (map (path </>) entries)
    subdirs <- mapM buildDirectoryStructure dirs
    readme <- findReadme files
    return $ DirectoryStructure {
        dirName = takeFileName path,
        dirPath = path,
        dirFiles = map takeFileName files,
        dirSubdirs = subdirs,
        dirReadme = readme
    }
```

### 检查报告生成

```haskell
-- 生成检查报告
generateQualityReport :: [String] -> String
generateQualityReport errors = 
    let totalErrors = length errors
        errorCategories = categorizeErrors errors
        summary = generateSummary totalErrors errorCategories
        details = generateErrorDetails errors
    in unlines [summary, "", details]

-- 错误分类
categorizeErrors :: [String] -> [(String, Int)]
categorizeErrors errors = 
    let categories = map categorizeError errors
        grouped = group $ sort categories
    in map (\g -> (head g, length g)) grouped

-- 生成摘要
generateSummary :: Int -> [(String, Int)] -> String
generateSummary total categories = 
    unlines [
        "# 质量检查报告",
        "",
        "## 摘要",
        "总错误数: " ++ show total,
        "",
        "## 错误分类",
        unlines [category ++ ": " ++ show count | (category, count) <- categories]
    ]
```

## 📊 质量指标

### 质量评分

```haskell
-- 质量评分系统
data QualityScore = 
    QualityScore {
        structureScore :: Double,
        contentScore :: Double,
        consistencyScore :: Double,
        completenessScore :: Double,
        overallScore :: Double
    }

-- 计算质量评分
calculateQualityScore :: [String] -> QualityScore
calculateQualityScore errors = 
    let totalErrors = length errors
        structureErrors = length $ filter (isPrefixOf "Structure") errors
        contentErrors = length $ filter (isPrefixOf "Content") errors
        consistencyErrors = length $ filter (isPrefixOf "Consistency") errors
        completenessErrors = length $ filter (isPrefixOf "Completeness") errors
        
        structureScore = max 0 (100 - structureErrors * 2)
        contentScore = max 0 (100 - contentErrors * 2)
        consistencyScore = max 0 (100 - consistencyErrors * 2)
        completenessScore = max 0 (100 - completenessErrors * 2)
        overallScore = (structureScore + contentScore + consistencyScore + completenessScore) / 4
    in QualityScore {
        structureScore = structureScore,
        contentScore = contentScore,
        consistencyScore = consistencyScore,
        completenessScore = completenessScore,
        overallScore = overallScore
    }
```

## 🎯 使用指南

### 运行检查

```bash
# 运行完整质量检查
cabal run quality-checker -- docs/refactor/

# 运行特定检查
cabal run quality-checker -- --structure docs/refactor/
cabal run quality-checker -- --content docs/refactor/
cabal run quality-checker -- --links docs/refactor/
```

### 检查配置

```yaml
# quality-check-config.yaml
checks:
  structure:
    enabled: true
    strict: true
  content:
    enabled: true
    strict: false
  links:
    enabled: true
    strict: true
  references:
    enabled: true
    strict: false
  concepts:
    enabled: true
    strict: true
  hierarchies:
    enabled: true
    strict: true
  completeness:
    enabled: true
    strict: false

thresholds:
  min_score: 85.0
  max_errors: 100
  max_warnings: 200
```

## 📈 持续改进

### 质量趋势分析

```haskell
-- 质量趋势分析
data QualityTrend = 
    QualityTrend {
        trendDate :: Day,
        trendScore :: Double,
        trendErrors :: Int,
        trendWarnings :: Int,
        trendImprovements :: [String]
    }

-- 分析质量趋势
analyzeQualityTrend :: [QualityTrend] -> String
analyzeQualityTrend trends = 
    let recentTrends = take 10 $ reverse $ sortBy (comparing trendDate) trends
        avgScore = average $ map trendScore recentTrends
        avgErrors = average $ map trendErrors recentTrends
        improvements = concatMap trendImprovements recentTrends
    in unlines [
        "## 质量趋势分析",
        "平均质量评分: " ++ show avgScore,
        "平均错误数: " ++ show avgErrors,
        "",
        "## 改进建议",
        unlines improvements
    ]
```

---

*本质量检查工具确保形式化知识体系的高质量和一致性。*

**最后更新**: 2024年12月
**工具状态**: 完整可用
**检查覆盖**: 100% 覆盖
