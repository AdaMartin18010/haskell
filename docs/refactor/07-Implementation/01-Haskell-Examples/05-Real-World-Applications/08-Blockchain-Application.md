# 区块链应用 - Haskell实现

## 概述

本文档提供了一个完整的区块链应用的Haskell实现，包括基础区块链结构、挖矿算法、钱包功能等核心组件。

## 1. 基础数据结构

```haskell
{-# LANGUAGE GADTs, TypeFamilies, FlexibleContexts, DeriveGeneric #-}

module Blockchain.Core.DataStructures where

import Data.Time (UTCTime)
import Data.Text (Text)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Crypto.Hash (SHA256, hash)
import Data.Aeson (ToJSON, FromJSON)
import GHC.Generics (Generic)

-- 交易类型
data Transaction = Transaction
  { txId :: TransactionId
  , fromAddress :: Address
  , toAddress :: Address
  , amount :: Double
  , timestamp :: UTCTime
  , signature :: Signature
  } deriving (Show, Eq, Generic)

instance ToJSON Transaction
instance FromJSON Transaction

-- 交易ID (SHA256哈希)
newtype TransactionId = TransactionId { unTransactionId :: BS.ByteString }
  deriving (Show, Eq, Ord)

-- 地址 (公钥的哈希)
newtype Address = Address { unAddress :: BS.ByteString }
  deriving (Show, Eq, Ord)

-- 签名
newtype Signature = Signature { unSignature :: BS.ByteString }
  deriving (Show, Eq)

-- 区块头
data BlockHeader = BlockHeader
  { version :: Int
  , previousHash :: BlockHash
  , merkleRoot :: MerkleRoot
  , timestamp :: UTCTime
  , difficulty :: Int
  , nonce :: Int
  } deriving (Show, Eq, Generic)

instance ToJSON BlockHeader
instance FromJSON BlockHeader

-- 区块
data Block = Block
  { header :: BlockHeader
  , transactions :: [Transaction]
  } deriving (Show, Eq, Generic)

instance ToJSON Block
instance FromJSON Block

-- 区块哈希
newtype BlockHash = BlockHash { unBlockHash :: BS.ByteString }
  deriving (Show, Eq, Ord)

-- Merkle根
newtype MerkleRoot = MerkleRoot { unMerkleRoot :: BS.ByteString }
  deriving (Show, Eq)

-- 区块链
data Blockchain = Blockchain
  { blocks :: [Block]
  , pendingTransactions :: [Transaction]
  , difficulty :: Int
  } deriving (Show, Eq, Generic)

instance ToJSON Blockchain
instance FromJSON Blockchain

-- 钱包
data Wallet = Wallet
  { privateKey :: PrivateKey
  , publicKey :: PublicKey
  , address :: Address
  , balance :: Double
  } deriving (Show, Eq, Generic)

instance ToJSON Wallet
instance FromJSON Wallet

-- 私钥
newtype PrivateKey = PrivateKey { unPrivateKey :: BS.ByteString }
  deriving (Show, Eq)

-- 公钥
newtype PublicKey = PublicKey { unPublicKey :: BS.ByteString }
  deriving (Show, Eq)
```

## 2. 加密和哈希函数

```haskell
module Blockchain.Core.Crypto where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Crypto.Hash (SHA256, hash, hashWith)
import Blockchain.Core.DataStructures

-- SHA256哈希
sha256 :: BS.ByteString -> BS.ByteString
sha256 = hashWith SHA256

-- 计算交易ID
computeTransactionId :: Transaction -> TransactionId
computeTransactionId tx = TransactionId $ sha256 $ BSC.pack $ show tx

-- 计算区块哈希
computeBlockHash :: Block -> BlockHash
computeBlockHash block = BlockHash $ sha256 $ BSC.pack $ show (header block)

-- 计算Merkle根
computeMerkleRoot :: [Transaction] -> MerkleRoot
computeMerkleRoot [] = MerkleRoot $ sha256 $ BSC.pack "empty"
computeMerkleRoot [tx] = MerkleRoot $ sha256 $ BSC.pack $ show tx
computeMerkleRoot txs = 
  let hashes = map (sha256 . BSC.pack . show) txs
  in MerkleRoot $ computeMerkleRoot' hashes

computeMerkleRoot' :: [BS.ByteString] -> BS.ByteString
computeMerkleRoot' [] = BS.empty
computeMerkleRoot' [h] = h
computeMerkleRoot' hashes = 
  let paired = pairHashes hashes
  in computeMerkleRoot' paired

pairHashes :: [BS.ByteString] -> [BS.ByteString]
pairHashes [] = []
pairHashes [h] = [sha256 $ h `BS.append` h]
pairHashes (h1:h2:rest) = 
  let combined = sha256 $ h1 `BS.append` h2
  in combined : pairHashes rest

-- 验证工作量证明
verifyProofOfWork :: BlockHash -> Int -> Bool
verifyProofOfWork (BlockHash hash) difficulty = 
  let target = BS.replicate difficulty 0
      hashPrefix = BS.take difficulty hash
  in hashPrefix == target

-- 生成工作量证明
generateProofOfWork :: BlockHeader -> Int -> (BlockHeader, Int)
generateProofOfWork header difficulty = 
  let go nonce = 
        let newHeader = header { nonce = nonce }
            block = Block { header = newHeader, transactions = [] }
            hash = computeBlockHash block
        in if verifyProofOfWork hash difficulty then
             (newHeader, nonce)
           else
             go (nonce + 1)
  in go 0
```

## 3. 钱包功能

```haskell
module Blockchain.Core.Wallet where

import Blockchain.Core.DataStructures
import Blockchain.Core.Crypto
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Crypto.Random (getRandomBytes)
import Data.Time (getCurrentTime)

-- 创建新钱包
createWallet :: IO Wallet
createWallet = do
  -- 生成随机私钥
  privateKeyBytes <- getRandomBytes 32
  let privateKey = PrivateKey privateKeyBytes
  
  -- 从私钥生成公钥 (简化实现)
  let publicKey = PrivateKey $ sha256 privateKeyBytes
  
  -- 从公钥生成地址
  let address = Address $ sha256 $ unPrivateKey publicKey
  
  return Wallet
    { privateKey = privateKey
    , publicKey = publicKey
    , address = address
    , balance = 0.0
    }

-- 签名交易
signTransaction :: Wallet -> Transaction -> Transaction
signTransaction wallet tx = 
  let message = BSC.pack $ show tx
      signature = Signature $ sha256 $ message `BS.append` unPrivateKey (privateKey wallet)
  in tx { signature = signature }

-- 验证交易签名
verifyTransactionSignature :: Transaction -> Bool
verifyTransactionSignature tx = 
  let message = BSC.pack $ show tx { signature = Signature BS.empty }
      expectedSignature = sha256 $ message `BS.append` unPublicKey (publicKey (fromAddress tx))
  in unSignature (signature tx) == expectedSignature

-- 创建交易
createTransaction :: Wallet -> Address -> Double -> IO Transaction
createTransaction wallet toAddress amount = do
  currentTime <- getCurrentTime
  
  let tx = Transaction
        { txId = TransactionId BS.empty  -- 临时ID
        , fromAddress = address wallet
        , toAddress = toAddress
        , amount = amount
        , timestamp = currentTime
        , signature = Signature BS.empty  -- 临时签名
        }
      
      signedTx = signTransaction wallet tx
      finalTx = signedTx { txId = computeTransactionId signedTx }
  
  return finalTx
```

## 4. 区块链核心功能

```haskell
module Blockchain.Core.Blockchain where

import Blockchain.Core.DataStructures
import Blockchain.Core.Crypto
import Blockchain.Core.Wallet
import Data.Time (getCurrentTime)

-- 创建创世区块
createGenesisBlock :: Block
createGenesisBlock = 
  let header = BlockHeader
        { version = 1
        , previousHash = BlockHash $ BS.replicate 32 0
        , merkleRoot = MerkleRoot $ BS.replicate 32 0
        , timestamp = read "1970-01-01 00:00:00 UTC"
        , difficulty = 4
        , nonce = 0
        }
  in Block
    { header = header
    , transactions = []
    }

-- 创建新区块链
createBlockchain :: Int -> Blockchain
createBlockchain difficulty = Blockchain
  { blocks = [createGenesisBlock]
  , pendingTransactions = []
  , difficulty = difficulty
  }

-- 添加交易到待处理队列
addTransaction :: Blockchain -> Transaction -> Blockchain
addTransaction blockchain tx = 
  blockchain { pendingTransactions = pendingTransactions blockchain ++ [tx] }

-- 创建新区块
createNewBlock :: Blockchain -> Address -> Block
createNewBlock blockchain minerAddress = 
  let previousBlock = last (blocks blockchain)
      previousHash = computeBlockHash previousBlock
      merkleRoot = computeMerkleRoot (pendingTransactions blockchain)
      currentTime <- getCurrentTime
      
      header = BlockHeader
        { version = 1
        , previousHash = previousHash
        , merkleRoot = merkleRoot
        , timestamp = currentTime
        , difficulty = difficulty blockchain
        , nonce = 0
        }
      
      -- 添加挖矿奖励交易
      rewardTx = Transaction
        { txId = TransactionId BS.empty
        , fromAddress = Address BS.empty  -- 系统地址
        , toAddress = minerAddress
        , amount = 10.0  -- 挖矿奖励
        , timestamp = currentTime
        , signature = Signature BS.empty
        }
      
      allTransactions = pendingTransactions blockchain ++ [rewardTx]
      
  in Block
    { header = header
    , transactions = allTransactions
    }

-- 挖矿
mineBlock :: Blockchain -> Address -> IO (Block, Blockchain)
mineBlock blockchain minerAddress = do
  let newBlock = createNewBlock blockchain minerAddress
      (minedHeader, _) = generateProofOfWork (header newBlock) (difficulty blockchain)
      minedBlock = newBlock { header = minedHeader }
      
      updatedBlockchain = blockchain
        { blocks = blocks blockchain ++ [minedBlock]
        , pendingTransactions = []
        }
  
  return (minedBlock, updatedBlockchain)

-- 验证区块
validateBlock :: Block -> Block -> Bool
validateBlock currentBlock previousBlock = 
  let currentHash = computeBlockHash currentBlock
      previousHash = computeBlockHash previousBlock
      
      -- 验证前一个区块哈希
      hashValid = previousHash (header currentBlock) == previousHash
      
      -- 验证工作量证明
      proofValid = verifyProofOfWork currentHash (difficulty (header currentBlock))
      
      -- 验证Merkle根
      merkleValid = merkleRoot (header currentBlock) == computeMerkleRoot (transactions currentBlock)
      
      -- 验证交易
      transactionsValid = all verifyTransactionSignature (transactions currentBlock)
      
  in hashValid && proofValid && merkleValid && transactionsValid

-- 验证区块链
validateBlockchain :: Blockchain -> Bool
validateBlockchain blockchain = 
  let blocks' = blocks blockchain
  in case blocks' of
       [] -> True
       [_] -> True  -- 创世区块
       (b1:b2:rest) -> 
         let valid = validateBlock b2 b1
         in valid && validateBlockchain (blockchain { blocks = b2:rest })

-- 获取余额
getBalance :: Blockchain -> Address -> Double
getBalance blockchain address = 
  let allTransactions = concatMap transactions (blocks blockchain)
      incoming = sum [amount | tx <- allTransactions, toAddress tx == address]
      outgoing = sum [amount | tx <- allTransactions, fromAddress tx == address]
  in incoming - outgoing
```

## 5. 示例应用

```haskell
module Blockchain.Examples where

import Blockchain.Core.Blockchain
import Blockchain.Core.Wallet
import Data.Time (getCurrentTime)

-- 运行区块链示例
runBlockchainExample :: IO ()
runBlockchainExample = do
  putStrLn "=== 区块链示例 ==="
  
  -- 创建区块链
  let blockchain = createBlockchain 4
  putStrLn "创建区块链"
  
  -- 创建钱包
  wallet1 <- createWallet
  wallet2 <- createWallet
  putStrLn $ "钱包1地址: " ++ show (address wallet1)
  putStrLn $ "钱包2地址: " ++ show (address wallet2)
  
  -- 创建交易
  tx1 <- createTransaction wallet1 (address wallet2) 5.0
  putStrLn $ "创建交易: " ++ show (amount tx1) ++ " 从 " ++ show (fromAddress tx1) ++ " 到 " ++ show (toAddress tx1)
  
  -- 添加交易到区块链
  let blockchainWithTx = addTransaction blockchain tx1
  putStrLn "交易已添加到待处理队列"
  
  -- 挖矿
  (minedBlock, updatedBlockchain) <- mineBlock blockchainWithTx (address wallet1)
  putStrLn $ "挖矿完成，新区块哈希: " ++ show (computeBlockHash minedBlock)
  
  -- 验证区块链
  let isValid = validateBlockchain updatedBlockchain
  putStrLn $ "区块链验证: " ++ show isValid
  
  -- 检查余额
  let balance1 = getBalance updatedBlockchain (address wallet1)
  let balance2 = getBalance updatedBlockchain (address wallet2)
  putStrLn $ "钱包1余额: " ++ show balance1
  putStrLn $ "钱包2余额: " ++ show balance2

main :: IO ()
main = runBlockchainExample
```

## 总结

这个区块链应用提供了：

1. **基础数据结构**：交易、区块、区块链、钱包等
2. **加密功能**：SHA256哈希、数字签名等
3. **钱包功能**：创建钱包、签名交易、验证签名
4. **区块链核心**：创建区块、挖矿、验证、余额查询
5. **示例应用**：完整的区块链操作演示

所有实现都遵循函数式编程范式，充分利用Haskell的类型系统确保类型安全。 