# 计算机科学基础 (Computer Science Foundation)

## 📋 目录

1. [算法基础](#1-算法基础)
2. [数据结构](#2-数据结构)
3. [计算复杂性](#3-计算复杂性)
4. [计算机体系结构](#4-计算机体系结构)
5. [操作系统](#5-操作系统)
6. [编译原理](#6-编译原理)

## 1. 算法基础

### 1.1 算法定义

**定义 1.1 (算法)**
算法是一个有限步骤的计算过程，将输入转换为输出。

**Haskell实现：**

```haskell
-- 算法类型
type Algorithm input output = input -> output

-- 算法复杂度
data Complexity = Complexity
  { timeComplexity :: String
  , spaceComplexity :: String
  }

-- 算法分析
data AlgorithmAnalysis = AlgorithmAnalysis
  { algorithm :: String
  , complexity :: Complexity
  , correctness :: Bool
  , optimality :: Bool
  }
```

### 1.2 排序算法

**定义 1.2 (排序问题)**
给定序列 $A = [a_1, a_2, \ldots, a_n]$，找到排列 $\pi$ 使得 $a_{\pi(1)} \leq a_{\pi(2)} \leq \cdots \leq a_{\pi(n)}$。

**Haskell实现：**

```haskell
-- 快速排序
quicksort :: Ord a => [a] -> [a]
quicksort [] = []
quicksort (x:xs) = 
  let smaller = quicksort [a | a <- xs, a <= x]
      larger = quicksort [a | a <- xs, a > x]
  in smaller ++ [x] ++ larger

-- 归并排序
mergesort :: Ord a => [a] -> [a]
mergesort [] = []
mergesort [x] = [x]
mergesort xs = 
  let (left, right) = splitAt (length xs `div` 2) xs
  in merge (mergesort left) (mergesort right)

-- 归并函数
merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys) = 
  if x <= y 
  then x : merge xs (y:ys)
  else y : merge (x:xs) ys
```

**定理 1.1 (快速排序平均复杂度)**
快速排序的平均时间复杂度为 $O(n \log n)$。

**证明：** 通过递归树分析：

1. 每次分割的期望复杂度为 $O(n)$
2. 递归树的期望高度为 $O(\log n)$
3. 总复杂度为 $O(n \log n)$

## 2. 数据结构

### 2.1 基础数据结构

**定义 2.1 (数据结构)**
数据结构是组织和存储数据的方式，支持高效的数据操作。

**Haskell实现：**

```haskell
-- 栈
data Stack a = Stack [a]

-- 栈操作
push :: a -> Stack a -> Stack a
push x (Stack xs) = Stack (x:xs)

pop :: Stack a -> Maybe (a, Stack a)
pop (Stack []) = Nothing
pop (Stack (x:xs)) = Just (x, Stack xs)

-- 队列
data Queue a = Queue [a] [a]

-- 队列操作
enqueue :: a -> Queue a -> Queue a
enqueue x (Queue front back) = Queue front (x:back)

dequeue :: Queue a -> Maybe (a, Queue a)
dequeue (Queue [] []) = Nothing
dequeue (Queue [] back) = dequeue (Queue (reverse back) [])
dequeue (Queue (x:front) back) = Just (x, Queue front back)

-- 二叉树
data BinaryTree a = 
    Empty
  | Node a (BinaryTree a) (BinaryTree a)

-- 二叉搜索树
insertBST :: Ord a => a -> BinaryTree a -> BinaryTree a
insertBST x Empty = Node x Empty Empty
insertBST x (Node y left right) = 
  if x <= y
  then Node y (insertBST x left) right
  else Node y left (insertBST x right)

searchBST :: Ord a => a -> BinaryTree a -> Bool
searchBST _ Empty = False
searchBST x (Node y left right) = 
  if x == y
  then True
  else if x < y
       then searchBST x left
       else searchBST x right
```

### 2.2 高级数据结构

**定义 2.2 (平衡树)**
平衡树是保持高度平衡的二叉搜索树。

**Haskell实现：**

```haskell
-- AVL树
data AVLTree a = 
    AVLEmpty
  | AVLNode a Int (AVLTree a) (AVLTree a)

-- 计算高度
height :: AVLTree a -> Int
height AVLEmpty = 0
height (AVLNode _ h _ _) = h

-- 平衡因子
balanceFactor :: AVLTree a -> Int
balanceFactor AVLEmpty = 0
balanceFactor (AVLNode _ _ left right) = height left - height right

-- 左旋
leftRotate :: AVLTree a -> AVLTree a
leftRotate (AVLNode x _ left (AVLNode y _ yLeft yRight)) = 
  let newHeight = 1 + max (height left) (height yLeft)
  in AVLNode y newHeight (AVLNode x (1 + height left) left yLeft) yRight

-- 右旋
rightRotate :: AVLTree a -> AVLTree a
rightRotate (AVLNode x _ (AVLNode y _ yLeft yRight) right) = 
  let newHeight = 1 + max (height yRight) (height right)
  in AVLNode y newHeight yLeft (AVLNode x (1 + height right) yRight right)

-- 插入AVL树
insertAVL :: Ord a => a -> AVLTree a -> AVLTree a
insertAVL x AVLEmpty = AVLNode x 1 AVLEmpty AVLEmpty
insertAVL x (AVLNode y h left right) = 
  if x <= y
  then balance (AVLNode y h (insertAVL x left) right)
  else balance (AVLNode y h left (insertAVL x right))

-- 平衡AVL树
balance :: AVLTree a -> AVLTree a
balance tree = 
  let bf = balanceFactor tree
  in case bf of
       2 -> case balanceFactor (leftSubtree tree) of
              1 -> rightRotate tree
              _ -> leftRotate (leftSubtree tree) >>= rightRotate
       -2 -> case balanceFactor (rightSubtree tree) of
              -1 -> leftRotate tree
              _ -> rightRotate (rightSubtree tree) >>= leftRotate
       _ -> tree
```

## 3. 计算复杂性

### 3.1 复杂度类

**定义 3.1 (P类)**
P类是可以在多项式时间内解决的问题集合。

**定义 3.2 (NP类)**
NP类是可以在多项式时间内验证解的问题集合。

**Haskell实现：**

```haskell
-- 复杂度类
data ComplexityClass = 
    P
  | NP
  | NPComplete
  | NPHard
  | PSPACE
  | EXPTIME

-- 问题类型
data Problem input output = Problem
  { name :: String
  , solve :: input -> output
  , verify :: input -> output -> Bool
  , complexityClass :: ComplexityClass
  }

-- 多项式时间算法
isPolynomialTime :: (input -> output) -> Bool
isPolynomialTime algorithm = 
  let timeComplexity = analyzeTimeComplexity algorithm
  in isPolynomial timeComplexity

-- 验证器
verifier :: (input -> output -> Bool) -> Bool
verifier verify = 
  let verificationTime = analyzeVerificationTime verify
  in isPolynomial verificationTime
```

### 3.2 NP完全性

**定义 3.3 (NP完全问题)**
问题 $L$ 是NP完全的，如果：

1. $L \in \text{NP}$
2. 对于所有 $L' \in \text{NP}$，$L' \leq_p L$

**Haskell实现：**

```haskell
-- 多项式时间归约
polynomialTimeReduction :: Problem a b -> Problem c d -> (c -> a) -> (b -> d) -> Bool
polynomialTimeReduction problemA problemB reduce transform = 
  let -- 检查归约函数是多项式时间
      reductionTime = analyzeTimeComplexity reduce
      transformTime = analyzeTimeComplexity transform
      isPolynomialReduction = isPolynomial reductionTime && isPolynomial transformTime
      
      -- 检查正确性
      correctness = checkReductionCorrectness problemA problemB reduce transform
  in isPolynomialReduction && correctness

-- 检查归约正确性
checkReductionCorrectness :: Problem a b -> Problem c d -> (c -> a) -> (b -> d) -> Bool
checkReductionCorrectness problemA problemB reduce transform = 
  let -- 对于所有输入x，如果problemB有解，则problemA也有解
      correctness = all (\x -> 
        let y = reduce x
            solutionA = solve problemA y
            solutionB = transform solutionA
        in verify problemB x solutionB) (allPossibleInputs problemB)
  in correctness

-- SAT问题
data SATProblem = SATProblem
  { variables :: [String]
  , clauses :: [[Literal]]
  }

data Literal = 
    Positive String
  | Negative String

-- 3-SAT问题
threeSAT :: SATProblem -> Bool
threeSAT problem = 
  let -- 检查每个子句恰好有3个文字
      isValidClause clause = length clause == 3
      validClauses = all isValidClause (clauses problem)
      
      -- 检查可满足性
      satisfiable = checkSatisfiability problem
  in validClauses && satisfiable

-- 检查可满足性
checkSatisfiability :: SATProblem -> Bool
checkSatisfiability problem = 
  let -- 生成所有可能的赋值
      allAssignments = generateAllAssignments (variables problem)
      
      -- 检查是否存在满足的赋值
      satisfyingAssignment = find (\assignment -> 
        all (\clause -> evaluateClause clause assignment) (clauses problem)) allAssignments
  in isJust satisfyingAssignment
```

## 4. 计算机体系结构

### 4.1 冯·诺依曼架构

**定义 4.1 (冯·诺依曼架构)**
冯·诺依曼架构包含：

- **存储器**：存储程序和数据
- **运算器**：执行算术和逻辑运算
- **控制器**：控制程序执行
- **输入输出设备**：与外部交互

**Haskell实现：**

```haskell
-- 冯·诺依曼计算机
data VonNeumannComputer = VonNeumannComputer
  { memory :: Memory
  , alu :: ALU
  , controlUnit :: ControlUnit
  , ioDevices :: [IODevice]
  }

-- 存储器
data Memory = Memory
  { ram :: Map Address Word
  , rom :: Map Address Word
  }

-- 运算器
data ALU = ALU
  { registers :: Map RegisterName Word
  , operations :: Map OpCode (Word -> Word -> Word)
  }

-- 控制器
data ControlUnit = ControlUnit
  { programCounter :: Address
  , instructionRegister :: Instruction
  , fetchDecodeExecute :: ComputerState -> ComputerState
  }

-- 指令
data Instruction = Instruction
  { opcode :: OpCode
  , operands :: [Operand]
  }

-- 执行指令
executeInstruction :: VonNeumannComputer -> Instruction -> VonNeumannComputer
executeInstruction computer instruction = 
  let opcode = opcode instruction
      operands = operands instruction
      
      -- 获取操作数
      operandValues = map (getOperandValue computer) operands
      
      -- 执行操作
      result = executeOperation (alu computer) opcode operandValues
      
      -- 更新计算机状态
      updatedComputer = updateComputerState computer result
  in updatedComputer
```

### 4.2 流水线架构

**定义 4.2 (指令流水线)**
指令流水线将指令执行分为多个阶段并行处理。

**Haskell实现：**

```haskell
-- 流水线阶段
data PipelineStage = 
    Fetch
  | Decode
  | Execute
  | Memory
  | WriteBack

-- 流水线寄存器
data PipelineRegister = PipelineRegister
  { stage :: PipelineStage
  , instruction :: Maybe Instruction
  , data :: Maybe PipelineData
  }

-- 流水线
data Pipeline = Pipeline
  { stages :: [PipelineRegister]
  , hazards :: [Hazard]
  }

-- 流水线执行
pipelineExecute :: Pipeline -> [Instruction] -> Pipeline
pipelineExecute pipeline instructions = 
  let -- 每个时钟周期
      clockCycle pipeline [] = pipeline
      clockCycle pipeline (inst:rest) = 
        let -- 推进流水线
            advancedPipeline = advancePipeline pipeline
            -- 插入新指令
            newPipeline = insertInstruction advancedPipeline inst
        in clockCycle newPipeline rest
  in clockCycle pipeline instructions

-- 推进流水线
advancePipeline :: Pipeline -> Pipeline
advancePipeline pipeline = 
  let stages = stages pipeline
      advancedStages = map advanceStage stages
  in pipeline { stages = advancedStages }

-- 数据冒险检测
dataHazardDetection :: Pipeline -> [Hazard]
dataHazardDetection pipeline = 
  let stages = stages pipeline
      -- 检查RAW冒险
      rawHazards = detectRAWHazards stages
      -- 检查WAW冒险
      wawHazards = detectWAWHazards stages
      -- 检查WAR冒险
      warHazards = detectWARHazards stages
  in rawHazards ++ wawHazards ++ warHazards
```

## 5. 操作系统

### 5.1 进程管理

**定义 5.1 (进程)**
进程是正在执行的程序实例。

**Haskell实现：**

```haskell
-- 进程
data Process = Process
  { processId :: PID
  , state :: ProcessState
  , priority :: Priority
  , memorySpace :: MemorySpace
  , registers :: Registers
  }

-- 进程状态
data ProcessState = 
    Running
  | Ready
  | Blocked
  | Terminated

-- 进程调度器
data Scheduler = Scheduler
  { readyQueue :: [Process]
  , blockedQueue :: [Process]
  , schedulingPolicy :: SchedulingPolicy
  }

-- 调度策略
data SchedulingPolicy = 
    RoundRobin Int
  | PriorityScheduling
  | ShortestJobFirst
  | MultiLevelQueue

-- 进程调度
schedule :: Scheduler -> Process -> Scheduler
schedule scheduler process = 
  case schedulingPolicy scheduler of
    RoundRobin quantum -> roundRobinSchedule scheduler process quantum
    PriorityScheduling -> prioritySchedule scheduler process
    ShortestJobFirst -> sjfSchedule scheduler process
    MultiLevelQueue -> mlqSchedule scheduler process

-- 轮转调度
roundRobinSchedule :: Scheduler -> Process -> Int -> Scheduler
roundRobinSchedule scheduler process quantum = 
  let readyQueue = readyQueue scheduler
      newReadyQueue = readyQueue ++ [process]
  in scheduler { readyQueue = newReadyQueue }

-- 上下文切换
contextSwitch :: Process -> Process -> (Process, Process)
contextSwitch currentProcess newProcess = 
  let -- 保存当前进程状态
      savedProcess = currentProcess { state = Ready }
      -- 恢复新进程状态
      restoredProcess = newProcess { state = Running }
  in (savedProcess, restoredProcess)
```

### 5.2 内存管理

**定义 5.2 (虚拟内存)**
虚拟内存为每个进程提供独立的地址空间。

**Haskell实现：**

```haskell
-- 虚拟内存管理器
data VirtualMemoryManager = VirtualMemoryManager
  { pageTable :: Map VirtualAddress PhysicalAddress
  , freeFrames :: [FrameNumber]
  , pageReplacementPolicy :: PageReplacementPolicy
  }

-- 页面替换策略
data PageReplacementPolicy = 
    FIFO
  | LRU
  | Clock
  | Optimal

-- 页面替换
pageReplacement :: VirtualMemoryManager -> VirtualAddress -> VirtualMemoryManager
pageReplacement vmm virtualAddr = 
  let pageTable = pageTable vmm
      freeFrames = freeFrames vmm
      
      -- 检查页面是否在内存中
      pageInMemory = Map.member virtualAddr pageTable
      
      -- 页面错误处理
      vmm' = if pageInMemory
             then vmm
             else handlePageFault vmm virtualAddr
  in vmm'

-- 处理页面错误
handlePageFault :: VirtualMemoryManager -> VirtualAddress -> VirtualMemoryManager
handlePageFault vmm virtualAddr = 
  let freeFrames = freeFrames vmm
      pageTable = pageTable vmm
      
      -- 如果有空闲帧
      vmm' = if not (null freeFrames)
             then allocateFreeFrame vmm virtualAddr
             else replacePage vmm virtualAddr
  in vmm'

-- LRU页面替换
lruPageReplacement :: VirtualMemoryManager -> VirtualAddress -> VirtualMemoryManager
lruPageReplacement vmm virtualAddr = 
  let -- 找到最久未使用的页面
      lruPage = findLRUPage vmm
      -- 替换该页面
      vmm' = replacePage vmm lruPage
      -- 分配新页面
      vmm'' = allocatePage vmm' virtualAddr
  in vmm''
```

## 6. 编译原理

### 6.1 词法分析

**定义 6.1 (词法分析器)**
词法分析器将源代码转换为词法单元序列。

**Haskell实现：**

```haskell
-- 词法单元
data Token = Token
  { tokenType :: TokenType
  , lexeme :: String
  , position :: Position
  }

-- 词法单元类型
data TokenType = 
    Identifier
  | Number
  | String
  | Operator
  | Keyword
  | Delimiter
  | EOF

-- 词法分析器
data Lexer = Lexer
  { source :: String
  , position :: Position
  , keywords :: Set String
  }

-- 词法分析
lexicalAnalysis :: Lexer -> [Token]
lexicalAnalysis lexer = 
  let source = source lexer
      tokens = scanTokens lexer source
  in tokens

-- 扫描词法单元
scanTokens :: Lexer -> String -> [Token]
scanTokens lexer "" = [Token EOF "" (position lexer)]
scanTokens lexer source = 
  let (token, remaining) = scanNextToken lexer source
      tokens = scanTokens lexer remaining
  in token : tokens

-- 扫描下一个词法单元
scanNextToken :: Lexer -> String -> (Token, String)
scanNextToken lexer source = 
  let -- 跳过空白字符
      (source', pos') = skipWhitespace source (position lexer)
      
      -- 识别词法单元
      (token, remaining) = recognizeToken lexer source'
  in (token, remaining)

-- 识别词法单元
recognizeToken :: Lexer -> String -> (Token, String)
recognizeToken lexer source = 
  case source of
    (c:cs) | isAlpha c -> recognizeIdentifier lexer source
    (c:cs) | isDigit c -> recognizeNumber lexer source
    (c:cs) | isOperator c -> recognizeOperator lexer source
    (c:cs) | isDelimiter c -> recognizeDelimiter lexer source
    _ -> (Token EOF "" (position lexer), source)
```

### 6.2 语法分析

**定义 6.2 (语法分析器)**
语法分析器根据语法规则构建抽象语法树。

**Haskell实现：**

```haskell
-- 抽象语法树
data AST = 
    Program [Statement]
  | Statement Statement
  | Expression Expression
  | Declaration Declaration

-- 语句
data Statement = 
    Assignment String Expression
  | IfStatement Expression Statement Statement
  | WhileStatement Expression Statement
  | FunctionCall String [Expression]

-- 表达式
data Expression = 
    Literal Value
  | Variable String
  | BinaryOp Operator Expression Expression
  | UnaryOp Operator Expression

-- 递归下降语法分析器
data Parser = Parser
  { tokens :: [Token]
  , current :: Int
  }

-- 语法分析
parse :: [Token] -> AST
parse tokens = 
  let parser = Parser tokens 0
      ast = parseProgram parser
  in ast

-- 解析程序
parseProgram :: Parser -> AST
parseProgram parser = 
  let statements = parseStatements parser
  in Program statements

-- 解析语句
parseStatements :: Parser -> [Statement]
parseStatements parser = 
  let statements = many (parseStatement parser)
  in statements

-- 解析单个语句
parseStatement :: Parser -> Statement
parseStatement parser = 
  let token = peek parser
  in case tokenType token of
       Identifier -> parseAssignmentOrFunctionCall parser
       Keyword -> parseKeywordStatement parser
       _ -> error "Unexpected token"

-- 解析赋值语句
parseAssignment :: Parser -> Statement
parseAssignment parser = 
  let -- 解析标识符
      (identifier, parser') = parseIdentifier parser
      -- 解析等号
      parser'' = consume parser' Equal
      -- 解析表达式
      (expression, parser''') = parseExpression parser''
  in Assignment identifier expression
```

## 📚 参考文献

1. Cormen, T. H., et al. (2009). Introduction to Algorithms. MIT Press.
2. Aho, A. V., et al. (2006). Compilers: Principles, Techniques, and Tools. Addison-Wesley.
3. Silberschatz, A., et al. (2018). Operating System Concepts. Wiley.
4. Hennessy, J. L., & Patterson, D. A. (2017). Computer Architecture: A Quantitative Approach. Morgan Kaufmann.

## 🔗 相关链接

- [软件工程基础](../02-Software-Engineering/软件工程基础.md)
- [人工智能基础](../03-Artificial-Intelligence/人工智能基础.md)
- [数据科学基础](../04-Data-Science/数据科学基础.md)

---

*本文档提供了计算机科学的完整理论基础，包含算法、数据结构、计算复杂性等核心概念，为后续的具体应用提供理论支撑。*
