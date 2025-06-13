{-# LANGUAGE GADTs, TypeFamilies, FlexibleInstances, MultiParamTypeClasses #-}

-- 集合论基础 Haskell 实现
-- Set Theory Foundation Haskell Implementation

module SetTheory where

import Data.List (nub, subsequences)
import Data.Maybe (fromJust)

-- ============================================================================
-- 基本类型定义
-- ============================================================================

-- 集合的基本类型
data Set a = 
    EmptySet                    -- 空集
  | Singleton a                 -- 单元素集
  | Union (Set a) (Set a)       -- 并集
  | Intersection (Set a) (Set a) -- 交集
  | Difference (Set a) (Set a)  -- 差集
  | PowerSet (Set a)            -- 幂集
  | CartesianProduct (Set a) (Set b) -- 笛卡尔积
  | Comprehension (Set a) (a -> Bool) -- 分离公理
  deriving (Show, Eq)

-- 存在性类型
data ExistenceType = 
    Independent    -- 独立存在
  | Dependent      -- 依赖存在
  | Constructed    -- 构造存在
  | Fictional      -- 虚构存在
  deriving (Show, Eq)

-- 序数类型
data Ordinal = 
    Zero                    -- 0
  | Successor Ordinal       -- α + 1
  | Limit [Ordinal]         -- 极限序数
  deriving (Show, Eq)

-- 基数类型
data Cardinal = 
    FiniteCardinal Integer    -- 有限基数
  | Aleph Ordinal            -- 阿列夫数
  deriving (Show, Eq)

-- 关系类型
data Relation a b = Relation {
    domain :: Set a,
    codomain :: Set b,
    pairs :: Set (a, b)
} deriving (Show, Eq)

-- 函数类型
data Function a b = Function {
    domain :: Set a,
    codomain :: Set b,
    mapping :: a -> b
} deriving (Show)

-- ============================================================================
-- 集合成员关系
-- ============================================================================

-- 集合成员关系类
class SetMembership a where
    -- 成员关系
    member :: a -> Set a -> Bool
    
    -- 子集关系
    subset :: Set a -> Set a -> Bool
    
    -- 真子集关系
    properSubset :: Set a -> Set a -> Bool
    
    -- 相等关系
    setEqual :: Set a -> Set a -> Bool

-- 集合成员关系实例
instance (Eq a) => SetMembership a where
    member x = \case
        EmptySet -> False
        Singleton y -> x == y
        Union s1 s2 -> member x s1 || member x s2
        Intersection s1 s2 -> member x s1 && member x s2
        Difference s1 s2 -> member x s1 && not (member x s2)
        PowerSet s -> all (\subset -> subset `isSubsetOf` s) (powerSetElements x)
        CartesianProduct s1 s2 -> case x of
            (a, b) -> member a s1 && member b s2
        Comprehension s p -> member x s && p x
    
    subset s1 s2 = all (\x -> member x s2) (setElements s1)
    
    properSubset s1 s2 = subset s1 s2 && not (setEqual s1 s2)
    
    setEqual s1 s2 = subset s1 s2 && subset s2 s1

-- 辅助函数
isSubsetOf :: (Eq a) => Set a -> Set a -> Bool
isSubsetOf = subset

-- 获取集合的所有元素
setElements :: Set a -> [a]
setElements = \case
    EmptySet -> []
    Singleton x -> [x]
    Union s1 s2 -> nub (setElements s1 ++ setElements s2)
    Intersection s1 s2 -> nub [x | x <- setElements s1, member x s2]
    Difference s1 s2 -> nub [x | x <- setElements s1, not (member x s2)]
    PowerSet s -> powerSetElements s
    CartesianProduct s1 s2 -> nub [(a, b) | a <- setElements s1, b <- setElements s2]
    Comprehension s p -> nub [x | x <- setElements s, p x]

-- 幂集元素
powerSetElements :: Set a -> [Set a]
powerSetElements s = 
    let elements = setElements s
    in map (buildSetFromList elements) (subsequences elements)

-- 从列表构建集合
buildSetFromList :: [a] -> [a] -> Set a
buildSetFromList allElements selectedElements = 
    Comprehension (buildSetFromList allElements allElements) (\x -> x `elem` selectedElements)

-- ============================================================================
-- ZFC公理系统
-- ============================================================================

-- ZFC公理系统类
class ZFCAxioms a where
    -- 外延公理：两个集合相等当且仅当它们包含相同的元素
    extensionality :: Set a -> Set a -> Bool
    
    -- 空集公理：存在一个不包含任何元素的集合
    emptySetAxiom :: Set a
    
    -- 配对公理：对于任意两个集合，存在一个包含它们的集合
    pairing :: a -> a -> Set a
    
    -- 并集公理：对于任意集合族，存在一个包含所有成员元素的集合
    union :: Set (Set a) -> Set a
    
    -- 幂集公理：对于任意集合，存在一个包含其所有子集的集合
    powerSet :: Set a -> Set (Set a)
    
    -- 分离公理：对于任意集合和性质，存在一个包含满足该性质的所有元素的子集
    separation :: (a -> Bool) -> Set a -> Set a
    
    -- 替换公理：对于任意函数和集合，存在一个包含函数值域的集合
    replacement :: (a -> b) -> Set a -> Set b
    
    -- 无穷公理：存在一个包含空集且对每个元素都包含其后继的集合
    infinity :: Set a
    
    -- 选择公理：对于任意非空集合族，存在一个选择函数
    choice :: Set (Set a) -> (Set a -> a)

-- ZFC公理实例
instance (Eq a) => ZFCAxioms a where
    -- 外延公理
    extensionality s1 s2 = setEqual s1 s2
    
    -- 空集公理
    emptySetAxiom = EmptySet
    
    -- 配对公理
    pairing x y = Union (Singleton x) (Singleton y)
    
    -- 并集公理
    union setOfSets = 
        let allElements = concatMap setElements (setElements setOfSets)
        in buildSetFromList allElements allElements
    
    -- 幂集公理
    powerSet s = PowerSet s
    
    -- 分离公理
    separation predicate s = Comprehension s predicate
    
    -- 替换公理
    replacement f s = 
        let elements = setElements s
            images = map f elements
        in buildSetFromList images images
    
    -- 无穷公理
    infinity = 
        let zero = EmptySet
            successor x = Union x (Singleton x)
            naturalNumbers = iterate successor zero
        in buildSetFromList naturalNumbers naturalNumbers
    
    -- 选择公理
    choice setOfSets = 
        let nonEmptySets = filter (not . isEmpty) (setElements setOfSets)
        in \s -> head (setElements s)  -- 简化版本

-- 辅助函数
isEmpty :: Set a -> Bool
isEmpty EmptySet = True
isEmpty _ = False

-- ============================================================================
-- 序数运算
-- ============================================================================

-- 序数运算类
class OrdinalOperations a where
    -- 序数加法
    ordinalAdd :: a -> a -> a
    
    -- 序数乘法
    ordinalMultiply :: a -> a -> a
    
    -- 序数幂
    ordinalPower :: a -> a -> a
    
    -- 序数比较
    ordinalCompare :: a -> a -> Ordering

instance OrdinalOperations Ordinal where
    -- 序数加法
    ordinalAdd Zero b = b
    ordinalAdd (Successor a) b = Successor (ordinalAdd a b)
    ordinalAdd (Limit as) b = Limit (map (\a -> ordinalAdd a b) as)
    
    -- 序数乘法
    ordinalMultiply Zero _ = Zero
    ordinalMultiply (Successor a) b = ordinalAdd b (ordinalMultiply a b)
    ordinalMultiply (Limit as) b = Limit (map (\a -> ordinalMultiply a b) as)
    
    -- 序数幂
    ordinalPower _ Zero = Successor Zero
    ordinalPower a (Successor b) = ordinalMultiply a (ordinalPower a b)
    ordinalPower a (Limit bs) = Limit (map (\b -> ordinalPower a b) bs)
    
    -- 序数比较
    ordinalCompare Zero Zero = EQ
    ordinalCompare Zero _ = LT
    ordinalCompare _ Zero = GT
    ordinalCompare (Successor a) (Successor b) = ordinalCompare a b
    ordinalCompare (Successor a) (Limit bs) = LT
    ordinalCompare (Limit as) (Successor b) = GT
    ordinalCompare (Limit as) (Limit bs) = compareLimits as bs

-- 比较极限序数
compareLimits :: [Ordinal] -> [Ordinal] -> Ordering
compareLimits as bs = 
    let maxA = maximum as
        maxB = maximum bs
    in ordinalCompare maxA maxB

-- 自然数到序数的转换
naturalToOrdinal :: Integer -> Ordinal
naturalToOrdinal 0 = Zero
naturalToOrdinal n = Successor (naturalToOrdinal (n - 1))

-- 序数到自然数的转换（有限序数）
ordinalToNatural :: Ordinal -> Maybe Integer
ordinalToNatural Zero = Just 0
ordinalToNatural (Successor a) = 
    case ordinalToNatural a of
        Just n -> Just (n + 1)
        Nothing -> Nothing
ordinalToNatural (Limit _) = Nothing

-- ============================================================================
-- 基数运算
-- ============================================================================

-- 基数运算类
class CardinalOperations a where
    -- 基数加法
    cardinalAdd :: a -> a -> a
    
    -- 基数乘法
    cardinalMultiply :: a -> a -> a
    
    -- 基数幂
    cardinalPower :: a -> a -> a
    
    -- 基数比较
    cardinalCompare :: a -> a -> Ordering

instance CardinalOperations Cardinal where
    -- 基数加法
    cardinalAdd (FiniteCardinal a) (FiniteCardinal b) = FiniteCardinal (a + b)
    cardinalAdd (FiniteCardinal _) (Aleph _) = Aleph (Limit [])
    cardinalAdd (Aleph _) (FiniteCardinal _) = Aleph (Limit [])
    cardinalAdd (Aleph a) (Aleph b) = 
        case ordinalCompare a b of
            LT -> Aleph b
            _ -> Aleph a
    
    -- 基数乘法
    cardinalMultiply (FiniteCardinal a) (FiniteCardinal b) = FiniteCardinal (a * b)
    cardinalMultiply (FiniteCardinal 0) _ = FiniteCardinal 0
    cardinalMultiply (FiniteCardinal _) (Aleph _) = Aleph (Limit [])
    cardinalMultiply (Aleph _) (FiniteCardinal 0) = FiniteCardinal 0
    cardinalMultiply (Aleph _) (FiniteCardinal _) = Aleph (Limit [])
    cardinalMultiply (Aleph a) (Aleph b) = 
        case ordinalCompare a b of
            LT -> Aleph b
            _ -> Aleph a
    
    -- 基数幂
    cardinalPower (FiniteCardinal a) (FiniteCardinal b) = FiniteCardinal (a ^ b)
    cardinalPower (FiniteCardinal 0) (FiniteCardinal 0) = FiniteCardinal 1
    cardinalPower (FiniteCardinal 0) (FiniteCardinal _) = FiniteCardinal 0
    cardinalPower (FiniteCardinal _) (Aleph _) = Aleph (Limit [])
    cardinalPower (Aleph _) (FiniteCardinal 0) = FiniteCardinal 1
    cardinalPower (Aleph _) (FiniteCardinal _) = Aleph (Limit [])
    cardinalPower (Aleph a) (Aleph b) = Aleph (Successor (max a b))
    
    -- 基数比较
    cardinalCompare (FiniteCardinal a) (FiniteCardinal b) = compare a b
    cardinalCompare (FiniteCardinal _) (Aleph _) = LT
    cardinalCompare (Aleph _) (FiniteCardinal _) = GT
    cardinalCompare (Aleph a) (Aleph b) = ordinalCompare a b

-- 集合的基数
setCardinality :: Set a -> Cardinal
setCardinality s = 
    let elements = setElements s
        count = length elements
    in if count < maxBound
       then FiniteCardinal (fromIntegral count)
       else Aleph (Limit [])

-- 等势关系
equipotent :: Set a -> Set b -> Bool
equipotent s1 s2 = 
    let card1 = setCardinality s1
        card2 = setCardinality s2
    in card1 == card2

-- ============================================================================
-- 集合运算
-- ============================================================================

-- 集合运算类
class SetOperations a where
    -- 并集
    union :: Set a -> Set a -> Set a
    
    -- 交集
    intersection :: Set a -> Set a -> Set a
    
    -- 差集
    difference :: Set a -> Set a -> Set a
    
    -- 对称差
    symmetricDifference :: Set a -> Set a -> Set a
    
    -- 笛卡尔积
    cartesianProduct :: Set a -> Set b -> Set (a, b)
    
    -- 幂集
    powerSet :: Set a -> Set (Set a)

instance (Eq a, Eq b) => SetOperations a where
    -- 并集
    union s1 s2 = Union s1 s2
    
    -- 交集
    intersection s1 s2 = Intersection s1 s2
    
    -- 差集
    difference s1 s2 = Difference s1 s2
    
    -- 对称差
    symmetricDifference s1 s2 = 
        Union (difference s1 s2) (difference s2 s1)
    
    -- 笛卡尔积
    cartesianProduct s1 s2 = CartesianProduct s1 s2
    
    -- 幂集
    powerSet s = PowerSet s

-- ============================================================================
-- 关系运算
-- ============================================================================

-- 关系运算类
class RelationOperations a b where
    -- 关系合成
    compose :: Relation a b -> Relation b c -> Relation a c
    
    -- 关系逆
    inverse :: Relation a b -> Relation b a
    
    -- 关系限制
    restrict :: Relation a b -> Set a -> Relation a b
    
    -- 关系像
    image :: Relation a b -> Set a -> Set b

instance (Eq a, Eq b, Eq c) => RelationOperations a b where
    -- 关系合成
    compose r1 r2 = 
        let pairs1 = setElements (pairs r1)
            pairs2 = setElements (pairs r2)
            composedPairs = [(a, c) | (a, b) <- pairs1, (b', c) <- pairs2, b == b']
        in Relation {
            domain = domain r1,
            codomain = codomain r2,
            pairs = buildSetFromList composedPairs composedPairs
        }
    
    -- 关系逆
    inverse r = 
        let pairsList = setElements (pairs r)
            inversePairs = map (\(a, b) -> (b, a)) pairsList
        in Relation {
            domain = codomain r,
            codomain = domain r,
            pairs = buildSetFromList inversePairs inversePairs
        }
    
    -- 关系限制
    restrict r s = 
        let pairsList = setElements (pairs r)
            restrictedPairs = filter (\(a, _) -> member a s) pairsList
        in Relation {
            domain = s,
            codomain = codomain r,
            pairs = buildSetFromList restrictedPairs restrictedPairs
        }
    
    -- 关系像
    image r s = 
        let pairsList = setElements (pairs r)
            images = nub [b | (a, b) <- pairsList, member a s]
        in buildSetFromList images images

-- 关系的性质
class RelationProperties a b where
    -- 自反性
    reflexive :: Relation a a -> Bool
    
    -- 对称性
    symmetric :: Relation a a -> Bool
    
    -- 传递性
    transitive :: Relation a a -> Bool
    
    -- 反对称性
    antisymmetric :: Relation a a -> Bool

instance (Eq a) => RelationProperties a b where
    -- 自反性：对于所有 x，有 (x, x) ∈ R
    reflexive r = 
        let domainElements = setElements (domain r)
        in all (\x -> member (x, x) (pairs r)) domainElements
    
    -- 对称性：如果 (x, y) ∈ R，则 (y, x) ∈ R
    symmetric r = 
        let pairsList = setElements (pairs r)
        in all (\(x, y) -> member (y, x) (pairs r)) pairsList
    
    -- 传递性：如果 (x, y) ∈ R 且 (y, z) ∈ R，则 (x, z) ∈ R
    transitive r = 
        let pairsList = setElements (pairs r)
            allTriples = [(x, y, z) | (x, y) <- pairsList, (y', z) <- pairsList, y == y']
        in all (\(x, y, z) -> member (x, z) (pairs r)) allTriples
    
    -- 反对称性：如果 (x, y) ∈ R 且 (y, x) ∈ R，则 x = y
    antisymmetric r = 
        let pairsList = setElements (pairs r)
        in all (\(x, y) -> not (member (y, x) (pairs r)) || x == y) pairsList

-- ============================================================================
-- 函数运算
-- ============================================================================

-- 函数运算类
class FunctionOperations a b where
    -- 函数合成
    compose :: Function a b -> Function b c -> Function a c
    
    -- 函数限制
    restrict :: Function a b -> Set a -> Function a b
    
    -- 函数像
    image :: Function a b -> Set a -> Set b
    
    -- 函数逆像
    preimage :: Function a b -> Set b -> Set a

instance (Eq a, Eq b, Eq c) => FunctionOperations a b where
    -- 函数合成
    compose f g = 
        Function {
            domain = domain f,
            codomain = codomain g,
            mapping = mapping g . mapping f
        }
    
    -- 函数限制
    restrict f s = 
        Function {
            domain = s,
            codomain = codomain f,
            mapping = mapping f
        }
    
    -- 函数像
    image f s = 
        let domainElements = setElements s
            images = map (mapping f) domainElements
        in buildSetFromList images images
    
    -- 函数逆像
    preimage f t = 
        let codomainElements = setElements (codomain f)
            domainElements = setElements (domain f)
            preimages = [x | x <- domainElements, member (mapping f x) t]
        in buildSetFromList preimages preimages

-- 函数的性质
class FunctionProperties a b where
    -- 单射性
    injective :: Function a b -> Bool
    
    -- 满射性
    surjective :: Function a b -> Bool
    
    -- 双射性
    bijective :: Function a b -> Bool
    
    -- 可逆性
    invertible :: Function a b -> Bool

instance (Eq a, Eq b) => FunctionProperties a b where
    -- 单射性：不同的输入产生不同的输出
    injective f = 
        let domainElements = setElements (domain f)
            pairs = [(x, y) | x <- domainElements, y <- domainElements, x /= y]
        in all (\(x, y) -> mapping f x /= mapping f y) pairs
    
    -- 满射性：每个输出都有对应的输入
    surjective f = 
        let codomainElements = setElements (codomain f)
            domainElements = setElements (domain f)
            images = map (mapping f) domainElements
        in all (\y -> y `elem` images) codomainElements
    
    -- 双射性：既是单射又是满射
    bijective f = injective f && surjective f
    
    -- 可逆性：存在逆函数
    invertible f = bijective f

-- ============================================================================
-- 示例和测试
-- ============================================================================

-- 示例集合
exampleSet1 :: Set Integer
exampleSet1 = Union (Singleton 1) (Singleton 2)

exampleSet2 :: Set Integer
exampleSet2 = Union (Singleton 2) (Singleton 3)

-- 示例关系
exampleRelation :: Relation Integer Integer
exampleRelation = Relation {
    domain = exampleSet1,
    codomain = exampleSet2,
    pairs = CartesianProduct exampleSet1 exampleSet2
}

-- 示例函数
exampleFunction :: Function Integer Integer
exampleFunction = Function {
    domain = exampleSet1,
    codomain = exampleSet2,
    mapping = \x -> x + 1
}

-- 测试函数
testSetOperations :: IO ()
testSetOperations = do
    putStrLn "=== 集合运算测试 ==="
    
    -- 测试成员关系
    putStrLn $ "1 ∈ {1,2}: " ++ show (member 1 exampleSet1)
    putStrLn $ "3 ∈ {1,2}: " ++ show (member 3 exampleSet1)
    
    -- 测试子集关系
    putStrLn $ "{1} ⊆ {1,2}: " ++ show (subset (Singleton 1) exampleSet1)
    
    -- 测试并集
    let unionSet = union exampleSet1 exampleSet2
    putStrLn $ "{1,2} ∪ {2,3} = " ++ show (setElements unionSet)
    
    -- 测试交集
    let intersectionSet = intersection exampleSet1 exampleSet2
    putStrLn $ "{1,2} ∩ {2,3} = " ++ show (setElements intersectionSet)
    
    -- 测试基数
    putStrLn $ "|{1,2}| = " ++ show (setCardinality exampleSet1)

testOrdinalOperations :: IO ()
testOrdinalOperations = do
    putStrLn "\n=== 序数运算测试 ==="
    
    let one = Successor Zero
    let two = Successor one
    let three = Successor two
    
    putStrLn $ "1 + 2 = " ++ show (ordinalAdd one two)
    putStrLn $ "2 × 3 = " ++ show (ordinalMultiply two three)
    putStrLn $ "2^3 = " ++ show (ordinalPower two three)

testCardinalOperations :: IO ()
testCardinalOperations = do
    putStrLn "\n=== 基数运算测试 ==="
    
    let finite1 = FiniteCardinal 3
    let finite2 = FiniteCardinal 5
    
    putStrLn $ "3 + 5 = " ++ show (cardinalAdd finite1 finite2)
    putStrLn $ "3 × 5 = " ++ show (cardinalMultiply finite1 finite2)
    putStrLn $ "3^5 = " ++ show (cardinalPower finite1 finite2)

-- 主测试函数
main :: IO ()
main = do
    testSetOperations
    testOrdinalOperations
    testCardinalOperations
    putStrLn "\n=== 测试完成 ===" 