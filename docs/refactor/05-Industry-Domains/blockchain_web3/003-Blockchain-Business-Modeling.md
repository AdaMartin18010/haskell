# 区块链/Web3行业应用：业务建模分层详解

## 1. 总览

本节系统梳理区块链/Web3行业的核心业务建模，包括区块链核心概念、交易建模、智能合约建模、共识机制等，突出类型系统、形式化与工程实践的结合。

## 2. 区块链核心概念建模

### 2.1 概念结构

- 区块（Block）：区块头、交易集合、状态根、时间戳
- 区块头（Header）：父哈希、区块高度、状态根、交易根、摘要
- 交易（Transaction）：发送方、接收方、数值、手续费、签名

### 2.2 Rust代码示例

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Block {
    pub header: BlockHeader,
    pub transactions: Vec<Transaction>,
    pub state_root: Hash,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlockHeader {
    pub parent_hash: Hash,
    pub number: BlockNumber,
    pub state_root: Hash,
    pub transactions_root: Hash,
    pub timestamp: Timestamp,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Transaction {
    pub hash: TransactionHash,
    pub from: Address,
    pub to: Address,
    pub value: Amount,
    pub gas_limit: u64,
    pub gas_price: u64,
    pub nonce: u64,
    pub signature: Signature,
}
```

### 2.3 Haskell代码示例

```haskell
data Block = Block
  { blockHeader :: BlockHeader
  , blockTransactions :: [Transaction]
  , blockStateRoot :: Hash
  } deriving (Show, Eq)

data BlockHeader = BlockHeader
  { parentHash :: Hash
  , blockNumber :: BlockNumber
  , stateRoot :: Hash
  , transactionsRoot :: Hash
  , timestamp :: Timestamp
  } deriving (Show, Eq)

data Transaction = Transaction
  { txHash :: TransactionHash
  , txFrom :: Address
  , txTo :: Address
  , txValue :: Amount
  , txGasLimit :: Word64
  , txGasPrice :: Word64
  , txNonce :: Word64
  , txSignature :: Signature
  } deriving (Show, Eq)
```

## 3. 智能合约建模

### 3.1 概念结构

- 智能合约（SmartContract）：地址、代码、存储、余额
- 合约状态（ContractState）：键值存储、状态转换函数
- 合约事件（ContractEvent）：事件类型、参数、发出时间

### 3.2 Rust代码示例（Substrate）

```rust
#[pallet::config]
pub trait Config: frame_system::Config {
    type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;
    type Currency: Currency<Self::AccountId>;
}

#[pallet::storage]
#[pallet::getter(fn token_balance)]
pub type TokenBalance<T: Config> = StorageMap<
    _,
    Blake2_128Concat,
    T::AccountId,
    BalanceOf<T>,
    ValueQuery,
>;

#[pallet::event]
#[pallet::generate_deposit(pub(super) fn deposit_event)]
pub enum Event<T: Config> {
    Transfer(T::AccountId, T::AccountId, BalanceOf<T>),
    Approval(T::AccountId, T::AccountId, BalanceOf<T>),
}

#[pallet::call]
impl<T: Config> Pallet<T> {
    #[pallet::weight(10_000)]
    pub fn transfer(
        origin: OriginFor<T>,
        to: T::AccountId,
        amount: BalanceOf<T>,
    ) -> DispatchResult {
        let sender = ensure_signed(origin)?;
        Self::do_transfer(sender, to, amount)?;
        Ok(())
    }
}
```

### 3.3 Haskell代码示例（Plutus）

```haskell
-- 代币合约
data TokenContract = TokenContract
  { tokenName :: TokenName
  , tokenSymbol :: CurrencySymbol
  , tokenOwner :: PubKeyHash
  , tokenSupply :: Integer
  }

data TokenAction = Mint Integer | Burn Integer | Transfer PubKeyHash Integer

mkTokenValidator :: TokenContract -> TokenAction -> ScriptContext -> Bool
mkTokenValidator tc (Mint amount) ctx =
  traceIfFalse "Not signed by owner" (txSignedBy info (tokenOwner tc)) &&
  traceIfFalse "Invalid mint amount" (amount > 0)
  where
    info = scriptContextTxInfo ctx

mkTokenValidator tc (Transfer to amount) ctx =
  traceIfFalse "Not signed by sender" (txSignedBy info sender) &&
  traceIfFalse "Invalid transfer amount" (amount > 0 && amount <= senderBalance)
  where
    info = scriptContextTxInfo ctx
    sender = findSender info
    senderBalance = getBalance sender (tokenSymbol tc) info
```

## 4. 共识机制建模

### 4.1 概念结构

- 共识引擎（ConsensusEngine）：区块生成、验证规则、分叉选择
- 验证者（Validator）：权益、身份、投票权
- 共识状态（ConsensusState）：最终确认区块、待确认区块、投票记录

### 4.2 Rust代码示例（PoS共识）

```rust
pub trait ConsensusEngine {
    type Block;
    type Error;
    
    fn propose_block(&self) -> Result<Self::Block, Self::Error>;
    fn validate_block(&self, block: &Self::Block) -> Result<(), Self::Error>;
    fn finalize_block(&self, block: &Self::Block) -> Result<(), Self::Error>;
    fn determine_best_chain(&self) -> Result<ChainHead, Self::Error>;
}

pub struct ProofOfStake {
    validators: HashMap<ValidatorId, Validator>,
    state: ConsensusState,
    config: PosConfig,
}

impl ConsensusEngine for ProofOfStake {
    type Block = Block;
    type Error = ConsensusError;
    
    fn propose_block(&self) -> Result<Block, ConsensusError> {
        // 选择验证者
        let validator = self.select_validator()?;
        
        // 收集交易
        let transactions = self.collect_transactions();
        
        // 创建区块
        let parent = self.state.best_block_header();
        let header = BlockHeader {
            parent_hash: parent.hash(),
            number: parent.number + 1,
            state_root: self.compute_state_root(&transactions)?,
            transactions_root: self.compute_transactions_root(&transactions),
            timestamp: current_timestamp(),
        };
        
        // 签名区块
        let signature = validator.sign(&header)?;
        
        Ok(Block {
            header,
            transactions,
            signature,
        })
    }
}
```

### 4.3 Lean代码示例（共识正确性）

```lean
-- 共识安全性形式化
def consensus_safety (protocol : ConsensusProtocol) (nodes : list Node) : Prop :=
  ∀ (n₁ n₂ : Node) (b₁ b₂ : Block),
    n₁ ∈ nodes →
    n₂ ∈ nodes →
    finalized protocol n₁ b₁ →
    finalized protocol n₂ b₂ →
    (b₁ = b₂) ∨ (ancestor b₁ b₂) ∨ (ancestor b₂ b₁)

-- 活性定理
def consensus_liveness (protocol : ConsensusProtocol) (nodes : list Node) : Prop :=
  ∀ (t₁ : Time), ∃ (t₂ : Time) (b : Block),
    t₂ > t₁ →
    ∀ (n : Node), n ∈ honest_nodes nodes →
    finalized protocol n b
```

## 5. 去中心化应用建模

### 5.1 概念结构

- DApp（DecentralizedApp）：前端、智能合约、链下服务
- 状态通道（StateChannel）：链下状态、签名、争议解决
- 预言机（Oracle）：数据源、验证机制、数据格式

### 5.2 Rust代码示例（DApp后端）

```rust
pub struct DAppBackend {
    blockchain_client: BlockchainClient,
    contract_address: Address,
    state_cache: Cache<Key, Value>,
}

impl DAppBackend {
    pub async fn get_user_balance(&self, user: Address) -> Result<Balance, DAppError> {
        let call_data = encode_function_call("balanceOf", &[Token::Address(user)]);
        let result = self.blockchain_client.call(
            CallRequest {
                to: self.contract_address,
                data: call_data,
            }
        ).await?;
        
        Ok(decode_balance(result)?)
    }
    
    pub async fn submit_transaction(&self, tx: Transaction) -> Result<TxHash, DAppError> {
        // 签名交易
        let signed_tx = self.sign_transaction(tx)?;
        
        // 提交到区块链
        let tx_hash = self.blockchain_client.submit_transaction(signed_tx).await?;
        
        // 更新缓存
        self.update_state_cache(&tx).await?;
        
        Ok(tx_hash)
    }
}
```

## 6. 类型系统与形式化优势

- Haskell：代数数据类型表达区块链状态、纯函数式状态转换、智能合约DSL
- Rust：所有权系统保证资源安全、并发安全、零成本抽象
- Lean：共识协议正确性证明、智能合约安全性验证

## 7. 交叉引用与扩展阅读

- [区块链/Web3行业应用分层总览](./001-Blockchain-Overview.md)
- [Haskell、Rust、Lean理论与实践对比](./002-Blockchain-Haskell-Rust-Lean.md)
- [业务建模原始资料](../../model/industry_domains/blockchain_web3/README.md)
- [Rust深度解析](../../08-Programming-Languages/004-Rust-Deep-Dive.md)
- [Haskell深度解析](../../08-Programming-Languages/003-Haskell-Deep-Dive.md)
- [Lean深度解析](../../08-Programming-Languages/005-Lean-Deep-Dive.md)

---

> 本文档为区块链/Web3行业应用业务建模分层详解，后续将持续补充具体案例与形式化建模实践。
