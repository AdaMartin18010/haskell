# Haskell标准库 - 核心库与工具

## 📚 概述

Haskell标准库提供了丰富的预定义函数、数据类型和工具，是Haskell编程的基础。从Prelude预定义库到各种专业库，标准库涵盖了从基础操作到高级功能的各个方面。

## 🏗️ 目录结构

- [Prelude预定义库](#prelude预定义库)
- [数据结构库](#数据结构库)
- [文本处理库](#文本处理库)
- [IO系统](#io系统)
- [数值计算库](#数值计算库)
- [容器库](#容器库)

## 🔧 Prelude预定义库

### 基本函数

Prelude是Haskell的默认导入库，提供了最常用的函数和类型。

```haskell
-- 基本数值函数
add :: Num a => a -> a -> a
add = (+)

subtract :: Num a => a -> a -> a
subtract = (-)

multiply :: Num a => a -> a -> a
multiply = (*)

divide :: Fractional a => a -> a -> a
divide = (/)

-- 比较函数
equal :: Eq a => a -> a -> Bool
equal = (==)

notEqual :: Eq a => a -> a -> Bool
notEqual = (/=)

lessThan :: Ord a => a -> a -> Bool
lessThan = (<)

greaterThan :: Ord a => a -> a -> Bool
greaterThan = (>)

-- 逻辑函数
and' :: Bool -> Bool -> Bool
and' = (&&)

or' :: Bool -> Bool -> Bool
or' = (||)

not' :: Bool -> Bool
not' = not
```

### 列表函数

```haskell
-- 列表构造
emptyList :: [a]
emptyList = []

singleton :: a -> [a]
singleton x = [x]

cons :: a -> [a] -> [a]
cons = (:)

-- 列表操作
head' :: [a] -> a
head' (x:_) = x
head' [] = error "Empty list"

tail' :: [a] -> [a]
tail' (_:xs) = xs
tail' [] = error "Empty list"

last' :: [a] -> a
last' [x] = x
last' (_:xs) = last' xs
last' [] = error "Empty list"

init' :: [a] -> [a]
init' [_] = []
init' (x:xs) = x : init' xs
init' [] = error "Empty list"

-- 列表长度
length' :: [a] -> Int
length' [] = 0
length' (_:xs) = 1 + length' xs

-- 列表连接
append :: [a] -> [a] -> [a]
append [] ys = ys
append (x:xs) ys = x : append xs ys

concat' :: [[a]] -> [a]
concat' [] = []
concat' (xs:xss) = xs ++ concat' xss
```

### 高阶函数

```haskell
-- map函数
map' :: (a -> b) -> [a] -> [b]
map' _ [] = []
map' f (x:xs) = f x : map' f xs

-- filter函数
filter' :: (a -> Bool) -> [a] -> [a]
filter' _ [] = []
filter' p (x:xs)
  | p x = x : filter' p xs
  | otherwise = filter' p xs

-- foldr函数
foldr' :: (a -> b -> b) -> b -> [a] -> b
foldr' _ z [] = z
foldr' f z (x:xs) = f x (foldr' f z xs)

-- foldl函数
foldl' :: (b -> a -> b) -> b -> [a] -> b
foldl' _ z [] = z
foldl' f z (x:xs) = foldl' f (f z x) xs

-- 函数组合
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

-- 部分应用
partial :: (a -> b -> c) -> a -> b -> c
partial f x y = f x y
```

## 📦 数据结构库

### Data.List

```haskell
import Data.List

-- 排序函数
sortList :: Ord a => [a] -> [a]
sortList = sort

sortByList :: (a -> a -> Ordering) -> [a] -> [a]
sortByList = sortBy

-- 去重函数
nubList :: Eq a => [a] -> [a]
nubList = nub

nubByList :: (a -> a -> Bool) -> [a] -> [a]
nubByList = nubBy

-- 查找函数
findList :: (a -> Bool) -> [a] -> Maybe a
findList = find

findIndexList :: (a -> Bool) -> [a] -> Maybe Int
findIndexList = findIndex

-- 分割函数
splitAtList :: Int -> [a] -> ([a], [a])
splitAtList = splitAt

takeWhileList :: (a -> Bool) -> [a] -> [a]
takeWhileList = takeWhile

dropWhileList :: (a -> Bool) -> [a] -> [a]
dropWhileList = dropWhile

-- 分组函数
groupList :: Eq a => [a] -> [[a]]
groupList = group

groupByList :: (a -> a -> Bool) -> [a] -> [[a]]
groupByList = groupBy
```

### Data.Maybe

```haskell
import Data.Maybe

-- Maybe构造函数
just :: a -> Maybe a
just = Just

nothing :: Maybe a
nothing = Nothing

-- Maybe操作函数
fromJust :: Maybe a -> a
fromJust (Just x) = x
fromJust Nothing = error "fromJust: Nothing"

fromMaybe :: a -> Maybe a -> a
fromMaybe _ (Just x) = x
fromMaybe defaultVal Nothing = defaultVal

maybe :: b -> (a -> b) -> Maybe a -> b
maybe defaultVal f (Just x) = f x
maybe defaultVal _ Nothing = defaultVal

-- Maybe转换函数
listToMaybe :: [a] -> Maybe a
listToMaybe [] = Nothing
listToMaybe (x:_) = Just x

maybeToList :: Maybe a -> [a]
maybeToList (Just x) = [x]
maybeToList Nothing = []

-- Maybe组合函数
catMaybes :: [Maybe a] -> [a]
catMaybes [] = []
catMaybes (Just x:xs) = x : catMaybes xs
catMaybes (Nothing:xs) = catMaybes xs

mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe _ [] = []
mapMaybe f (x:xs) = case f x of
  Just y -> y : mapMaybe f xs
  Nothing -> mapMaybe f xs
```

### Data.Either

```haskell
import Data.Either

-- Either构造函数
left :: a -> Either a b
left = Left

right :: b -> Either a b
right = Right

-- Either操作函数
isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft (Right _) = False

isRight :: Either a b -> Bool
isRight (Left _) = False
isRight (Right _) = True

fromLeft :: a -> Either a b -> a
fromLeft _ (Left x) = x
fromLeft defaultVal (Right _) = defaultVal

fromRight :: b -> Either a b -> b
fromRight _ (Left _) = defaultVal
fromRight defaultVal (Right x) = x

-- Either转换函数
lefts :: [Either a b] -> [a]
lefts [] = []
lefts (Left x:xs) = x : lefts xs
lefts (Right _:xs) = lefts xs

rights :: [Either a b] -> [b]
rights [] = []
rights (Left _:xs) = rights xs
rights (Right x:xs) = x : rights xs

partitionEithers :: [Either a b] -> ([a], [b])
partitionEithers = foldr (either left right) ([], [])
  where
    left a (ls, rs) = (a:ls, rs)
    right b (ls, rs) = (ls, b:rs)
```

## 📝 文本处理库

### Data.Text

```haskell
import qualified Data.Text as T
import Data.Text (Text)

-- 文本构造
emptyText :: Text
emptyText = T.empty

singletonText :: Char -> Text
singletonText = T.singleton

packText :: String -> Text
packText = T.pack

unpackText :: Text -> String
unpackText = T.unpack

-- 文本操作
appendText :: Text -> Text -> Text
appendText = T.append

consText :: Char -> Text -> Text
consText = T.cons

snocText :: Text -> Char -> Text
snocText = T.snoc

headText :: Text -> Char
headText = T.head

tailText :: Text -> Text
tailText = T.tail

lastText :: Text -> Char
lastText = T.last

initText :: Text -> Text
initText = T.init

-- 文本长度
lengthText :: Text -> Int
lengthText = T.length

nullText :: Text -> Bool
nullText = T.null

-- 文本分割
splitText :: Char -> Text -> [Text]
splitText = T.split

splitOnText :: Text -> Text -> [Text]
splitOnText = T.splitOn

wordsText :: Text -> [Text]
wordsText = T.words

linesText :: Text -> [Text]
linesText = T.lines

-- 文本转换
toUpperText :: Text -> Text
toUpperText = T.toUpper

toLowerText :: Text -> Text
toLowerText = T.toLower

stripText :: Text -> Text
stripText = T.strip

stripStartText :: Text -> Text
stripStartText = T.stripStart

stripEndText :: Text -> Text
stripEndText = T.stripEnd
```

### Data.Text.Lazy

```haskell
import qualified Data.Text.Lazy as TL
import Data.Text.Lazy (Text)

-- 惰性文本操作
emptyLazyText :: Text
emptyLazyText = TL.empty

singletonLazyText :: Char -> Text
singletonLazyText = TL.singleton

packLazyText :: String -> Text
packLazyText = TL.pack

unpackLazyText :: Text -> String
unpackLazyText = TL.unpack

-- 惰性文本处理
appendLazyText :: Text -> Text -> Text
appendLazyText = TL.append

consLazyText :: Char -> Text -> Text
consLazyText = TL.cons

snocLazyText :: Text -> Char -> Text
snocLazyText = TL.snoc

-- 惰性文本转换
toUpperLazyText :: Text -> Text
toUpperLazyText = TL.toUpper

toLowerLazyText :: Text -> Text
toLowerLazyText = TL.toLower

stripLazyText :: Text -> Text
stripLazyText = TL.strip

-- 惰性文本分割
splitLazyText :: Char -> Text -> [Text]
splitLazyText = TL.split

splitOnLazyText :: Text -> Text -> [Text]
splitOnLazyText = TL.splitOn

wordsLazyText :: Text -> [Text]
wordsLazyText = TL.words

linesLazyText :: Text -> [Text]
linesLazyText = TL.lines
```

## 🔄 IO系统

### System.IO

```haskell
import System.IO

-- 文件操作
readFileIO :: FilePath -> IO String
readFileIO = readFile

writeFileIO :: FilePath -> String -> IO ()
writeFileIO = writeFile

appendFileIO :: FilePath -> String -> IO ()
appendFileIO = appendFile

-- 句柄操作
openFileIO :: FilePath -> IOMode -> IO Handle
openFileIO = openFile

hGetContentsIO :: Handle -> IO String
hGetContentsIO = hGetContents

hPutStrIO :: Handle -> String -> IO ()
hPutStrIO = hPutStr

hPutStrLnIO :: Handle -> String -> IO ()
hPutStrLnIO = hPutStrLn

hGetLineIO :: Handle -> IO String
hGetLineIO = hGetLine

hCloseIO :: Handle -> IO ()
hCloseIO = hClose

-- 标准输入输出
getLineIO :: IO String
getLineIO = getLine

putStrIO :: String -> IO ()
putStrIO = putStr

putStrLnIO :: String -> IO ()
putStrLnIO = putStrLn

printIO :: Show a => a -> IO ()
printIO = print

-- 缓冲操作
hSetBufferingIO :: Handle -> BufferMode -> IO ()
hSetBufferingIO = hSetBuffering

hFlushIO :: Handle -> IO ()
hFlushIO = hFlush
```

### Control.Monad.IO.Class

```haskell
import Control.Monad.IO.Class

-- IO单子类
class MonadIO m where
  liftIO :: IO a -> m a

-- IO操作提升
liftReadFile :: MonadIO m => FilePath -> m String
liftReadFile = liftIO . readFile

liftWriteFile :: MonadIO m => FilePath -> String -> m ()
liftWriteFile path = liftIO . writeFile path

liftPutStrLn :: MonadIO m => String -> m ()
liftPutStrLn = liftIO . putStrLn

liftGetLine :: MonadIO m => m String
liftGetLine = liftIO getLine

-- IO组合
withFileIO :: FilePath -> IOMode -> (Handle -> IO a) -> IO a
withFileIO path mode = withFile path mode

bracketIO :: IO a -> (a -> IO b) -> (a -> IO c) -> IO c
bracketIO = bracket
```

## 🔢 数值计算库

### Data.Int

```haskell
import Data.Int

-- 固定精度整数
int8 :: Int8
int8 = 127

int16 :: Int16
int16 = 32767

int32 :: Int32
int32 = 2147483647

int64 :: Int64
int64 = 9223372036854775807

-- 整数操作
addInt8 :: Int8 -> Int8 -> Int8
addInt8 = (+)

subtractInt8 :: Int8 -> Int8 -> Int8
subtractInt8 = (-)

multiplyInt8 :: Int8 -> Int8 -> Int8
multiplyInt8 = (*)

-- 整数转换
fromIntegralInt :: Integral a => a -> Int
fromIntegralInt = fromIntegral

toIntegralInt :: Int -> Integer
toIntegralInt = toInteger
```

### Data.Word

```haskell
import Data.Word

-- 无符号整数
word8 :: Word8
word8 = 255

word16 :: Word16
word16 = 65535

word32 :: Word32
word32 = 4294967295

word64 :: Word64
word64 = 18446744073709551615

-- 无符号整数操作
addWord8 :: Word8 -> Word8 -> Word8
addWord8 = (+)

subtractWord8 :: Word8 -> Word8 -> Word8
subtractWord8 = (-)

multiplyWord8 :: Word8 -> Word8 -> Word8
multiplyWord8 = (*)

-- 无符号整数转换
fromIntegralWord :: Integral a => a -> Word
fromIntegralWord = fromIntegral

toIntegralWord :: Word -> Integer
toIntegralWord = toInteger
```

## 📦 容器库

### Data.Map

```haskell
import qualified Data.Map as Map
import Data.Map (Map)

-- Map构造
emptyMap :: Map k v
emptyMap = Map.empty

singletonMap :: k -> v -> Map k v
singletonMap = Map.singleton

fromListMap :: Ord k => [(k, v)] -> Map k v
fromListMap = Map.fromList

toListMap :: Map k v -> [(k, v)]
toListMap = Map.toList

-- Map操作
insertMap :: Ord k => k -> v -> Map k v -> Map k v
insertMap = Map.insert

deleteMap :: Ord k => k -> Map k v -> Map k v
deleteMap = Map.delete

lookupMap :: Ord k => k -> Map k v -> Maybe v
lookupMap = Map.lookup

memberMap :: Ord k => k -> Map k v -> Bool
memberMap = Map.member

-- Map转换
mapMap :: (a -> b) -> Map k a -> Map k b
mapMap = Map.map

mapWithKeyMap :: (k -> a -> b) -> Map k a -> Map k b
mapWithKeyMap = Map.mapWithKey

filterMap :: (a -> Bool) -> Map k a -> Map k a
filterMap = Map.filter

filterWithKeyMap :: (k -> a -> Bool) -> Map k a -> Map k a
filterWithKeyMap = Map.filterWithKey
```

### Data.Set

```haskell
import qualified Data.Set as Set
import Data.Set (Set)

-- Set构造
emptySet :: Set a
emptySet = Set.empty

singletonSet :: a -> Set a
singletonSet = Set.singleton

fromListSet :: Ord a => [a] -> Set a
fromListSet = Set.fromList

toListSet :: Set a -> [a]
toListSet = Set.toList

-- Set操作
insertSet :: Ord a => a -> Set a -> Set a
insertSet = Set.insert

deleteSet :: Ord a => a -> Set a -> Set a
deleteSet = Set.delete

memberSet :: Ord a => a -> Set a -> Bool
memberSet = Set.member

-- Set运算
unionSet :: Ord a => Set a -> Set a -> Set a
unionSet = Set.union

intersectionSet :: Ord a => Set a -> Set a -> Set a
intersectionSet = Set.intersection

differenceSet :: Ord a => Set a -> Set a -> Set a
differenceSet = Set.difference

-- Set转换
mapSet :: Ord b => (a -> b) -> Set a -> Set b
mapSet = Set.map

filterSet :: (a -> Bool) -> Set a -> Set a
filterSet = Set.filter
```

## 🔗 相关链接

- [语言特性](01-Language-Features.md) - 基础语言特性
- [高级特性](02-Advanced-Features.md) - 高级类型系统
- [开发工具](04-Development-Tools.md) - 编译器和工具链

## 📚 参考文献

1. Peyton Jones, S. (2003). *The Haskell 98 Language and Libraries: The Revised Report*
2. Marlow, S. (2010). *Haskell 2010 Language Report*
3. O'Sullivan, B. (2009). *Real World Haskell*

---

**最后更新**: 2024年12月  
**版本**: 1.0  
**状态**: 完成
