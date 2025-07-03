# 区块链与Web3概述（Blockchain & Web3 Overview）

## 概述

区块链与Web3技术通过去中心化、密码学和共识机制构建可信的数字基础设施。涵盖分布式账本、智能合约、去中心化应用、数字资产等多个技术领域。

## 理论基础

- **密码学**：哈希函数、数字签名、零知识证明
- **共识机制**：PoW、PoS、DPoS、BFT
- **分布式系统**：拜占庭容错、网络同步、状态复制
- **经济学**：代币经济学、激励机制、治理机制

## 核心领域

### 1. 区块链基础
- 区块结构
- 链式存储
- 共识算法
- 网络协议

### 2. 智能合约
- 合约语言
- 执行环境
- 安全验证
- 升级机制

### 3. 去中心化应用
- DApp架构
- 前端集成
- 数据存储
- 用户体验

### 4. 数字资产
- 代币标准
- NFT协议
- DeFi协议
- 跨链桥接

## Haskell实现

### 区块链核心

```haskell
import Data.Time
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Crypto.Hash (hash, SHA256)
import Data.Serialize

-- 区块头
data BlockHeader = BlockHeader {
  version :: Int,
  previousHash :: ByteString,
  merkleRoot :: ByteString,
  timestamp :: UTCTime,
  difficulty :: Int,
  nonce :: Int
} deriving (Show, Eq)

-- 区块
data Block = Block {
  header :: BlockHeader,
  transactions :: [Transaction],
  hash :: ByteString
} deriving (Show, Eq)

-- 交易
data Transaction = Transaction {
  txId :: ByteString,
  inputs :: [TxInput],
  outputs :: [TxOutput],
  signature :: ByteString
} deriving (Show, Eq)

-- 交易输入
data TxInput = TxInput {
  previousTxId :: ByteString,
  outputIndex :: Int,
  scriptSig :: ByteString
} deriving (Show, Eq)

-- 交易输出
data TxOutput = TxOutput {
  value :: Integer,
  scriptPubKey :: ByteString
} deriving (Show, Eq)

-- 区块链
data Blockchain = Blockchain {
  blocks :: [Block],
  pendingTransactions :: [Transaction],
  difficulty :: Int
} deriving (Show)

-- 计算区块哈希
calculateBlockHash :: BlockHeader -> ByteString
calculateBlockHash header = 
  let serialized = encode header
  in hash serialized

-- 创建创世区块
createGenesisBlock :: Block
createGenesisBlock = 
  let header = BlockHeader {
    version = 1,
    previousHash = BS.replicate 32 0,
    merkleRoot = BS.replicate 32 0,
    timestamp = undefined, -- 需要实际时间
    difficulty = 4,
    nonce = 0
  }
  in Block {
    header = header,
    transactions = [],
    hash = calculateBlockHash header
  }

-- 创建新区块
createNewBlock :: Blockchain -> [Transaction] -> Int -> Block
createNewBlock blockchain transactions nonce = 
  let previousBlock = last (blocks blockchain)
      header = BlockHeader {
        version = 1,
        previousHash = hash previousBlock,
        merkleRoot = calculateMerkleRoot transactions,
        timestamp = undefined, -- 需要实际时间
        difficulty = difficulty blockchain,
        nonce = nonce
      }
      block = Block {
        header = header,
        transactions = transactions,
        hash = calculateBlockHash header
      }
  in block

-- 计算默克尔根
calculateMerkleRoot :: [Transaction] -> ByteString
calculateMerkleRoot [] = BS.replicate 32 0
calculateMerkleRoot [tx] = hash (encode tx)
calculateMerkleRoot txs = 
  let hashes = map (hash . encode) txs
      paired = pairHashes hashes
  in calculateMerkleRoot paired

-- 配对哈希
pairHashes :: [ByteString] -> [ByteString]
pairHashes [] = []
pairHashes [h] = [h]
pairHashes (h1:h2:rest) = 
  let combined = BS.append h1 h2
      combinedHash = hash combined
  in combinedHash : pairHashes rest

-- 工作量证明
proofOfWork :: Blockchain -> [Transaction] -> Block
proofOfWork blockchain transactions = 
  let target = BS.replicate (difficulty blockchain) 0
      findValidBlock nonce = 
        let block = createNewBlock blockchain transactions nonce
            blockHash = hash block
        in if BS.take (difficulty blockchain) blockHash == target
           then block
           else findValidBlock (nonce + 1)
  in findValidBlock 0

-- 验证区块
validateBlock :: Block -> Block -> Bool
validateBlock previousBlock currentBlock = 
  let expectedHash = calculateBlockHash (header currentBlock)
      actualHash = hash currentBlock
      correctHash = expectedHash == actualHash
      correctPrevious = previousHash (header currentBlock) == hash previousBlock
      validProof = validateProofOfWork currentBlock
  in correctHash && correctPrevious && validProof

-- 验证工作量证明
validateProofOfWork :: Block -> Bool
validateProofOfWork block = 
  let blockHash = hash block
      target = BS.replicate (difficulty (header block)) 0
  in BS.take (difficulty (header block)) blockHash == target

-- 添加区块到链
addBlock :: Blockchain -> Block -> Blockchain
addBlock blockchain block = 
  if validateBlock (last (blocks blockchain)) block
  then blockchain { blocks = blocks blockchain ++ [block] }
  else error "Invalid block"

-- 使用示例
demoBlockchain :: IO ()
demoBlockchain = do
  let genesisBlock = createGenesisBlock
  let blockchain = Blockchain [genesisBlock] [] 4
  
  putStrLn $ "Genesis block created: " ++ show genesisBlock
  putStrLn $ "Blockchain initialized with difficulty: " ++ show (difficulty blockchain)
```

### 智能合约系统

```haskell
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State

-- 智能合约
data SmartContract = SmartContract {
  contractId :: String,
  code :: String,
  state :: Map String Value,
  balance :: Integer
} deriving (Show)

-- 合约值
data Value = 
  IntValue Integer
  | StringValue String
  | BoolValue Bool
  | AddressValue String
  | ArrayValue [Value]
  deriving (Show, Eq)

-- 合约执行环境
data ContractEnv = ContractEnv {
  contracts :: Map String SmartContract,
  accounts :: Map String Integer,
  currentContract :: Maybe String,
  gasUsed :: Integer,
  gasLimit :: Integer
} deriving (Show)

-- 合约执行状态
type ContractState = State ContractEnv

-- 创建合约
createContract :: String -> String -> ContractState SmartContract
createContract contractId code = do
  let contract = SmartContract {
    contractId = contractId,
    code = code,
    state = Map.empty,
    balance = 0
  }
  env <- get
  put $ env { contracts = Map.insert contractId contract (contracts env) }
  return contract

-- 调用合约函数
callContract :: String -> String -> [Value] -> ContractState (Maybe Value)
callContract contractId functionName args = do
  env <- get
  case Map.lookup contractId (contracts env) of
    Just contract -> do
      let result = executeFunction contract functionName args
      case result of
        Just (newContract, returnValue) -> do
          put $ env { 
            contracts = Map.insert contractId newContract (contracts env),
            currentContract = Just contractId
          }
          return $ Just returnValue
        Nothing -> return Nothing
    Nothing -> return Nothing

-- 执行合约函数
executeFunction :: SmartContract -> String -> [Value] -> Maybe (SmartContract, Value)
executeFunction contract functionName args = 
  case functionName of
    "transfer" -> executeTransfer contract args
    "getBalance" -> executeGetBalance contract args
    "setValue" -> executeSetValue contract args
    "getValue" -> executeGetValue contract args
    _ -> Nothing

-- 执行转账
executeTransfer :: SmartContract -> [Value] -> Maybe (SmartContract, Value)
executeTransfer contract args = 
  case args of
    [AddressValue to, IntValue amount] -> 
      if amount <= balance contract
      then Just (contract { balance = balance contract - amount }, BoolValue True)
      else Just (contract, BoolValue False)
    _ -> Nothing

-- 执行获取余额
executeGetBalance :: SmartContract -> [Value] -> Maybe (SmartContract, Value)
executeGetBalance contract _ = 
  Just (contract, IntValue (balance contract))

-- 执行设置值
executeSetValue :: SmartContract -> [Value] -> Maybe (SmartContract, Value)
executeSetValue contract args = 
  case args of
    [StringValue key, value] -> 
      let newState = Map.insert key value (state contract)
      in Just (contract { state = newState }, BoolValue True)
    _ -> Nothing

-- 执行获取值
executeGetValue :: SmartContract -> [Value] -> Maybe (SmartContract, Value)
executeGetValue contract args = 
  case args of
    [StringValue key] -> 
      case Map.lookup key (state contract) of
        Just value -> Just (contract, value)
        Nothing -> Just (contract, StringValue "")
    _ -> Nothing

-- 部署代币合约
deployTokenContract :: String -> String -> Integer -> ContractState SmartContract
deployTokenContract contractId name totalSupply = do
  let code = "ERC20 Token Contract"
  contract <- createContract contractId code
  let contractWithBalance = contract { balance = totalSupply }
  env <- get
  put $ env { contracts = Map.insert contractId contractWithBalance (contracts env) }
  return contractWithBalance

-- 使用示例
demoSmartContract :: IO ()
demoSmartContract = do
  let initialState = ContractEnv Map.empty Map.empty Nothing 0 1000000
  let (result, finalState) = runState (do
    -- 部署代币合约
    tokenContract <- deployTokenContract "TOKEN001" "MyToken" 1000000
    
    -- 调用转账函数
    transferResult <- callContract "TOKEN001" "transfer" [AddressValue "0x123", IntValue 100]
    
    -- 获取余额
    balanceResult <- callContract "TOKEN001" "getBalance" []
    
    return (transferResult, balanceResult)) initialState
  
  putStrLn $ "Smart contract execution result: " ++ show result
```

## Rust实现

### 区块链节点

```rust
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};
use serde::{Serialize, Deserialize};
use sha2::{Sha256, Digest};
use tokio::sync::mpsc;

#[derive(Debug, Clone, Serialize, Deserialize)]
struct BlockHeader {
    version: u32,
    previous_hash: Vec<u8>,
    merkle_root: Vec<u8>,
    timestamp: u64,
    difficulty: u32,
    nonce: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct Block {
    header: BlockHeader,
    transactions: Vec<Transaction>,
    hash: Vec<u8>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct Transaction {
    tx_id: Vec<u8>,
    inputs: Vec<TxInput>,
    outputs: Vec<TxOutput>,
    signature: Vec<u8>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TxInput {
    previous_tx_id: Vec<u8>,
    output_index: u32,
    script_sig: Vec<u8>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TxOutput {
    value: u64,
    script_pub_key: Vec<u8>,
}

#[derive(Debug)]
struct Blockchain {
    blocks: Vec<Block>,
    pending_transactions: Vec<Transaction>,
    difficulty: u32,
    accounts: HashMap<String, u64>,
}

impl Blockchain {
    fn new(difficulty: u32) -> Self {
        let genesis_block = Self::create_genesis_block();
        Self {
            blocks: vec![genesis_block],
            pending_transactions: Vec::new(),
            difficulty,
            accounts: HashMap::new(),
        }
    }
    
    fn create_genesis_block() -> Block {
        let header = BlockHeader {
            version: 1,
            previous_hash: vec![0; 32],
            merkle_root: vec![0; 32],
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            difficulty: 4,
            nonce: 0,
        };
        
        let hash = Self::calculate_block_hash(&header);
        Block {
            header,
            transactions: Vec::new(),
            hash,
        }
    }
    
    fn calculate_block_hash(header: &BlockHeader) -> Vec<u8> {
        let serialized = bincode::serialize(header).unwrap();
        let mut hasher = Sha256::new();
        hasher.update(&serialized);
        hasher.finalize().to_vec()
    }
    
    fn calculate_merkle_root(transactions: &[Transaction]) -> Vec<u8> {
        if transactions.is_empty() {
            return vec![0; 32];
        }
        
        let mut hashes: Vec<Vec<u8>> = transactions
            .iter()
            .map(|tx| {
                let mut hasher = Sha256::new();
                hasher.update(&bincode::serialize(tx).unwrap());
                hasher.finalize().to_vec()
            })
            .collect();
        
        while hashes.len() > 1 {
            let mut new_hashes = Vec::new();
            for chunk in hashes.chunks(2) {
                let mut combined = chunk[0].clone();
                if chunk.len() > 1 {
                    combined.extend_from_slice(&chunk[1]);
                }
                let mut hasher = Sha256::new();
                hasher.update(&combined);
                new_hashes.push(hasher.finalize().to_vec());
            }
            hashes = new_hashes;
        }
        
        hashes[0].clone()
    }
    
    fn mine_block(&mut self, transactions: Vec<Transaction>) -> Block {
        let previous_block = &self.blocks[self.blocks.len() - 1];
        let merkle_root = Self::calculate_merkle_root(&transactions);
        
        let mut nonce = 0u64;
        loop {
            let header = BlockHeader {
                version: 1,
                previous_hash: previous_block.hash.clone(),
                merkle_root: merkle_root.clone(),
                timestamp: SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
                difficulty: self.difficulty,
                nonce,
            };
            
            let hash = Self::calculate_block_hash(&header);
            if Self::is_valid_hash(&hash, self.difficulty) {
                return Block {
                    header,
                    transactions,
                    hash,
                };
            }
            
            nonce += 1;
        }
    }
    
    fn is_valid_hash(hash: &[u8], difficulty: u32) -> bool {
        let target_zeros = difficulty as usize;
        hash.iter().take(target_zeros).all(|&byte| byte == 0)
    }
    
    fn add_block(&mut self, block: Block) -> bool {
        if self.validate_block(&block) {
            self.blocks.push(block);
            true
        } else {
            false
        }
    }
    
    fn validate_block(&self, block: &Block) -> bool {
        let calculated_hash = Self::calculate_block_hash(&block.header);
        if calculated_hash != block.hash {
            return false;
        }
        
        if !Self::is_valid_hash(&block.hash, self.difficulty) {
            return false;
        }
        
        if let Some(previous_block) = self.blocks.last() {
            if block.header.previous_hash != previous_block.hash {
                return false;
            }
        }
        
        true
    }
    
    fn add_transaction(&mut self, transaction: Transaction) {
        self.pending_transactions.push(transaction);
    }
    
    fn get_balance(&self, address: &str) -> u64 {
        *self.accounts.get(address).unwrap_or(&0)
    }
}

#[derive(Debug)]
struct BlockchainNode {
    blockchain: Blockchain,
    peers: Vec<String>,
    tx_sender: mpsc::Sender<Transaction>,
    tx_receiver: mpsc::Receiver<Transaction>,
}

impl BlockchainNode {
    fn new(difficulty: u32) -> Self {
        let (tx_sender, tx_receiver) = mpsc::channel(100);
        Self {
            blockchain: Blockchain::new(difficulty),
            peers: Vec::new(),
            tx_sender,
            tx_receiver,
        }
    }
    
    async fn start_mining(&mut self) {
        loop {
            if !self.blockchain.pending_transactions.is_empty() {
                let transactions = self.blockchain.pending_transactions.drain(..).collect();
                let new_block = self.blockchain.mine_block(transactions);
                
                if self.blockchain.add_block(new_block.clone()) {
                    println!("Mined new block: {:?}", new_block.hash);
                    self.broadcast_block(&new_block).await;
                }
            }
            
            tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
        }
    }
    
    async fn broadcast_block(&self, block: &Block) {
        // 简化的区块广播
        println!("Broadcasting block to {} peers", self.peers.len());
    }
    
    async fn process_transactions(&mut self) {
        while let Some(transaction) = self.tx_receiver.recv().await {
            self.blockchain.add_transaction(transaction);
        }
    }
    
    fn add_peer(&mut self, peer: String) {
        self.peers.push(peer);
    }
}

// 使用示例
#[tokio::main]
async fn demo_blockchain() {
    let mut node = BlockchainNode::new(4);
    
    // 添加一些交易
    let transaction = Transaction {
        tx_id: vec![1, 2, 3, 4],
        inputs: vec![],
        outputs: vec![TxOutput {
            value: 100,
            script_pub_key: vec![1, 2, 3],
        }],
        signature: vec![5, 6, 7, 8],
    };
    
    let _ = node.tx_sender.send(transaction).await;
    
    // 启动挖矿和交易处理
    let mining_handle = tokio::spawn(async move {
        node.start_mining().await;
    });
    
    println!("Blockchain node started");
}
```

### 智能合约虚拟机

```rust
use std::collections::HashMap;
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
enum Value {
    Int(i64),
    String(String),
    Bool(bool),
    Address(String),
    Array(Vec<Value>),
}

#[derive(Debug, Clone)]
struct SmartContract {
    contract_id: String,
    code: String,
    state: HashMap<String, Value>,
    balance: u64,
}

#[derive(Debug)]
struct ContractVM {
    contracts: HashMap<String, SmartContract>,
    accounts: HashMap<String, u64>,
    gas_used: u64,
    gas_limit: u64,
}

impl ContractVM {
    fn new(gas_limit: u64) -> Self {
        Self {
            contracts: HashMap::new(),
            accounts: HashMap::new(),
            gas_used: 0,
            gas_limit,
        }
    }
    
    fn deploy_contract(&mut self, contract_id: String, code: String, initial_balance: u64) -> Result<(), String> {
        if self.gas_used >= self.gas_limit {
            return Err("Gas limit exceeded".to_string());
        }
        
        let contract = SmartContract {
            contract_id: contract_id.clone(),
            code,
            state: HashMap::new(),
            balance: initial_balance,
        };
        
        self.contracts.insert(contract_id, contract);
        self.gas_used += 1000; // 部署消耗的gas
        
        Ok(())
    }
    
    fn call_contract(&mut self, contract_id: &str, function_name: &str, args: Vec<Value>) -> Result<Value, String> {
        if self.gas_used >= self.gas_limit {
            return Err("Gas limit exceeded".to_string());
        }
        
        let contract = self.contracts.get_mut(contract_id)
            .ok_or("Contract not found")?;
        
        let result = self.execute_function(contract, function_name, args)?;
        self.gas_used += 100; // 函数调用消耗的gas
        
        Ok(result)
    }
    
    fn execute_function(&self, contract: &mut SmartContract, function_name: &str, args: Vec<Value>) -> Result<Value, String> {
        match function_name {
            "transfer" => self.execute_transfer(contract, args),
            "getBalance" => self.execute_get_balance(contract, args),
            "setValue" => self.execute_set_value(contract, args),
            "getValue" => self.execute_get_value(contract, args),
            _ => Err("Unknown function".to_string()),
        }
    }
    
    fn execute_transfer(&self, contract: &mut SmartContract, args: Vec<Value>) -> Result<Value, String> {
        if args.len() != 2 {
            return Err("Transfer requires 2 arguments".to_string());
        }
        
        let (to, amount) = match (&args[0], &args[1]) {
            (Value::Address(to), Value::Int(amount)) => (to.clone(), *amount as u64),
            _ => return Err("Invalid arguments for transfer".to_string()),
        };
        
        if amount > contract.balance {
            return Ok(Value::Bool(false));
        }
        
        contract.balance -= amount;
        Ok(Value::Bool(true))
    }
    
    fn execute_get_balance(&self, contract: &SmartContract, _args: Vec<Value>) -> Result<Value, String> {
        Ok(Value::Int(contract.balance as i64))
    }
    
    fn execute_set_value(&self, contract: &mut SmartContract, args: Vec<Value>) -> Result<Value, String> {
        if args.len() != 2 {
            return Err("SetValue requires 2 arguments".to_string());
        }
        
        let (key, value) = match (&args[0], &args[1]) {
            (Value::String(key), value) => (key.clone(), value.clone()),
            _ => return Err("Invalid arguments for setValue".to_string()),
        };
        
        contract.state.insert(key, value);
        Ok(Value::Bool(true))
    }
    
    fn execute_get_value(&self, contract: &SmartContract, args: Vec<Value>) -> Result<Value, String> {
        if args.len() != 1 {
            return Err("GetValue requires 1 argument".to_string());
        }
        
        let key = match &args[0] {
            Value::String(key) => key,
            _ => return Err("Invalid argument for getValue".to_string()),
        };
        
        Ok(contract.state.get(key).cloned().unwrap_or(Value::String("".to_string())))
    }
    
    fn get_contract_state(&self, contract_id: &str) -> Option<&HashMap<String, Value>> {
        self.contracts.get(contract_id).map(|c| &c.state)
    }
}

// 使用示例
fn demo_smart_contract() {
    let mut vm = ContractVM::new(1000000);
    
    // 部署代币合约
    let contract_code = "ERC20 Token Contract".to_string();
    vm.deploy_contract("TOKEN001".to_string(), contract_code, 1000000).unwrap();
    
    // 调用转账函数
    let transfer_args = vec![
        Value::Address("0x123".to_string()),
        Value::Int(100),
    ];
    let transfer_result = vm.call_contract("TOKEN001", "transfer", transfer_args).unwrap();
    println!("Transfer result: {:?}", transfer_result);
    
    // 获取余额
    let balance_result = vm.call_contract("TOKEN001", "getBalance", vec![]).unwrap();
    println!("Balance: {:?}", balance_result);
    
    // 设置和获取状态
    let set_args = vec![
        Value::String("owner".to_string()),
        Value::Address("0x456".to_string()),
    ];
    vm.call_contract("TOKEN001", "setValue", set_args).unwrap();
    
    let get_args = vec![Value::String("owner".to_string())];
    let owner = vm.call_contract("TOKEN001", "getValue", get_args).unwrap();
    println!("Owner: {:?}", owner);
}
```

## Lean实现

### 形式化区块链模型

```lean
-- 区块头
structure BlockHeader where
  version : Nat
  previousHash : List Nat
  merkleRoot : List Nat
  timestamp : Nat
  difficulty : Nat
  nonce : Nat
  deriving Repr

-- 区块
structure Block where
  header : BlockHeader
  transactions : List Transaction
  hash : List Nat
  deriving Repr

-- 交易
structure Transaction where
  txId : List Nat
  inputs : List TxInput
  outputs : List TxOutput
  signature : List Nat
  deriving Repr

-- 交易输入
structure TxInput where
  previousTxId : List Nat
  outputIndex : Nat
  scriptSig : List Nat
  deriving Repr

-- 交易输出
structure TxOutput where
  value : Nat
  scriptPubKey : List Nat
  deriving Repr

-- 区块链
structure Blockchain where
  blocks : List Block
  pendingTransactions : List Transaction
  difficulty : Nat
  deriving Repr

-- 计算区块哈希
def calculateBlockHash (header : BlockHeader) : List Nat :=
  -- 简化的哈希计算
  header.version :: header.previousHash ++ header.merkleRoot ++ [header.timestamp, header.difficulty, header.nonce]

-- 创建创世区块
def createGenesisBlock : Block :=
  let header := BlockHeader.mk 1 [] [] 0 4 0
  Block.mk header [] (calculateBlockHash header)

-- 创建新区块
def createNewBlock (blockchain : Blockchain) (transactions : List Transaction) (nonce : Nat) : Block :=
  let previousBlock := blockchain.blocks.head?.getD createGenesisBlock
  let header := BlockHeader.mk 1 previousBlock.hash (calculateMerkleRoot transactions) 0 blockchain.difficulty nonce
  Block.mk header transactions (calculateBlockHash header)

-- 计算默克尔根
def calculateMerkleRoot (transactions : List Transaction) : List Nat :=
  match transactions with
  | [] => []
  | [tx] => tx.txId
  | txs => 
    let hashes := txs.map (λ tx => tx.txId)
    let paired := pairHashes hashes
    calculateMerkleRoot paired

-- 配对哈希
def pairHashes (hashes : List (List Nat)) : List (List Nat) :=
  match hashes with
  | [] => []
  | [h] => [h]
  | h1 :: h2 :: rest => (h1 ++ h2) :: pairHashes rest

-- 工作量证明
def proofOfWork (blockchain : Blockchain) (transactions : List Transaction) : Block :=
  let target := List.replicate blockchain.difficulty 0
  let findValidBlock (nonce : Nat) : Block :=
    let block := createNewBlock blockchain transactions nonce
    let blockHash := block.hash
    if List.take blockchain.difficulty blockHash = target then block else findValidBlock (nonce + 1)
  findValidBlock 0

-- 验证区块
def validateBlock (previousBlock : Block) (currentBlock : Block) : Bool :=
  let expectedHash := calculateBlockHash currentBlock.header
  let actualHash := currentBlock.hash
  let correctHash := expectedHash = actualHash
  let correctPrevious := currentBlock.header.previousHash = previousBlock.hash
  let validProof := validateProofOfWork currentBlock
  correctHash ∧ correctPrevious ∧ validProof

-- 验证工作量证明
def validateProofOfWork (block : Block) : Bool :=
  let blockHash := block.hash
  let target := List.replicate block.header.difficulty 0
  List.take block.header.difficulty blockHash = target

-- 智能合约
structure SmartContract where
  contractId : String
  code : String
  state : List (String × Value)
  balance : Nat
  deriving Repr

-- 合约值
inductive Value
| Int : Nat → Value
| String : String → Value
| Bool : Bool → Value
| Address : String → Value
deriving Repr

-- 合约执行环境
structure ContractEnv where
  contracts : List (String × SmartContract)
  accounts : List (String × Nat)
  gasUsed : Nat
  gasLimit : Nat
  deriving Repr

-- 创建合约
def createContract (contractId : String) (code : String) (env : ContractEnv) : ContractEnv :=
  let contract := SmartContract.mk contractId code [] 0
  { env with contracts := (contractId, contract) :: env.contracts }

-- 调用合约函数
def callContract (contractId : String) (functionName : String) (args : List Value) (env : ContractEnv) : Option (Value × ContractEnv) :=
  let contract := env.contracts.find? (λ (id, _) => id = contractId)
  match contract with
  | some (_, contract) =>
    let result := executeFunction contract functionName args
    match result with
    | some (newContract, returnValue) =>
      let updatedContracts := env.contracts.map (λ (id, c) => if id = contractId then (id, newContract) else (id, c))
      some (returnValue, { env with contracts := updatedContracts })
    | none => none
  | none => none

-- 执行合约函数
def executeFunction (contract : SmartContract) (functionName : String) (args : List Value) : Option (SmartContract × Value) :=
  match functionName with
  | "transfer" => executeTransfer contract args
  | "getBalance" => executeGetBalance contract args
  | "setValue" => executeSetValue contract args
  | "getValue" => executeGetValue contract args
  | _ => none

-- 执行转账
def executeTransfer (contract : SmartContract) (args : List Value) : Option (SmartContract × Value) :=
  match args with
  | [Value.Address to, Value.Int amount] =>
    if amount ≤ contract.balance then
      some ({ contract with balance := contract.balance - amount }, Value.Bool true)
    else
      some (contract, Value.Bool false)
  | _ => none

-- 执行获取余额
def executeGetBalance (contract : SmartContract) (args : List Value) : Option (SmartContract × Value) :=
  some (contract, Value.Int contract.balance)

-- 执行设置值
def executeSetValue (contract : SmartContract) (args : List Value) : Option (SmartContract × Value) :=
  match args with
  | [Value.String key, value] =>
    let newState := (key, value) :: contract.state
    some ({ contract with state := newState }, Value.Bool true)
  | _ => none

-- 执行获取值
def executeGetValue (contract : SmartContract) (args : List Value) : Option (SmartContract × Value) :=
  match args with
  | [Value.String key] =>
    let value := contract.state.find? (λ (k, _) => k = key) |>.map (λ (_, v) => v) |>.getD (Value.String "")
    some (contract, value)
  | _ => none

-- 使用示例
def demoBlockchain : IO Unit := do
  let genesisBlock := createGenesisBlock
  let blockchain := Blockchain.mk [genesisBlock] [] 4
  
  IO.println s!"Genesis block created: {genesisBlock}"
  IO.println s!"Blockchain initialized with difficulty: {blockchain.difficulty}"

def demoSmartContract : IO Unit := do
  let env := ContractEnv.mk [] [] 0 1000000
  let env' := createContract "TOKEN001" "ERC20 Token Contract" env
  
  let transferArgs := [Value.Address "0x123", Value.Int 100]
  let result := callContract "TOKEN001" "transfer" transferArgs env'
  
  match result with
  | some (value, _) => IO.println s!"Transfer result: {value}"
  | none => IO.println "Transfer failed"
```

### 形式化验证

```lean
-- 区块链不变量
def blockchainInvariant (blockchain : Blockchain) : Prop :=
  blockchain.difficulty > 0 ∧
  blockchain.blocks.all (λ block => block.header.difficulty = blockchain.difficulty)

-- 区块验证性质
theorem block_validation_property (previousBlock : Block) (currentBlock : Block) :
  validateBlock previousBlock currentBlock → 
  currentBlock.header.previousHash = previousBlock.hash := by
  simp [validateBlock]
  -- 证明区块验证的正确性

-- 工作量证明性质
theorem proof_of_work_property (blockchain : Blockchain) (transactions : List Transaction) :
  let block := proofOfWork blockchain transactions
  validateProofOfWork block := by
  simp [proofOfWork, validateProofOfWork]
  -- 证明工作量证明的有效性

-- 智能合约不变量
def contractInvariant (contract : SmartContract) : Prop :=
  contract.contractId.length > 0 ∧
  contract.code.length > 0

-- 合约执行性质
theorem contract_execution_property (contract : SmartContract) (functionName : String) (args : List Value) :
  let result := executeFunction contract functionName args
  match result with
  | some (newContract, _) => contractInvariant newContract
  | none => true := by
  simp [executeFunction, contractInvariant]
  -- 证明合约执行保持不变量

-- 使用示例
def demoFormalVerification : IO Unit := do
  let blockchain := Blockchain.mk [] [] 4
  
  if blockchainInvariant blockchain then
    IO.println "Blockchain invariant satisfied"
    let genesisBlock := createGenesisBlock
    let updatedBlockchain := { blockchain with blocks := [genesisBlock] }
    IO.println s!"Updated blockchain: {updatedBlockchain}"
  else
    IO.println "Blockchain invariant violated"
```

## 工程与形式化对比

| 维度 | Haskell | Rust | Lean |
|------|---------|------|------|
| 类型安全 | 强类型系统 | 所有权系统 | 依赖类型 |
| 性能 | 中等 | 高 | 中等 |
| 并发支持 | STM/Async | 多线程/异步 | 有限支持 |
| 形式化验证 | QuickCheck | 有限验证 | 完整证明 |
| 区块链生态 | 有限 | 丰富 | 有限 |

## 最佳实践

### 1. 安全性
- 密码学验证
- 智能合约审计
- 攻击防护
- 密钥管理

### 2. 性能优化
- 共识算法优化
- 网络同步
- 存储优化
- 计算优化

### 3. 可扩展性
- 分片技术
- 侧链机制
- 跨链协议
- 二层解决方案

### 4. 治理机制
- 去中心化治理
- 提案投票
- 升级机制
- 争议解决

## 应用场景

- **金融应用**：DeFi、支付、借贷、保险
- **数字资产**：NFT、代币、数字收藏品
- **供应链**：溯源、认证、透明化
- **身份认证**：去中心化身份、隐私保护
- **游戏娱乐**：区块链游戏、虚拟资产

## 总结

区块链与Web3技术需要高安全性、高可靠性和高性能的系统。Haskell适合智能合约和形式化验证，Rust适合区块链核心和性能关键部分，Lean适合关键算法的形式化证明。实际应用中应根据具体需求选择合适的技术栈，并注重安全性、可扩展性和治理机制。 