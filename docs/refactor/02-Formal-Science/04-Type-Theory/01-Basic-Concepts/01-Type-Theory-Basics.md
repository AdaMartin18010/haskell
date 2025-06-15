# 类型论基础

## 概述

类型论基础是理解现代类型系统的起点，它建立了类型、项和类型关系的基本概念。类型论为函数式编程、定理证明和形式化验证提供理论基础。

## 核心概念

### 1. 类型 (Types)

类型是值的集合，描述了程序可以操作的数据结构。

#### 形式化定义

```haskell
-- 基本类型
data Type = 
    Unit                           -- 单位类型
  | Bool                           -- 布尔类型
  | Int                            -- 整数类型
  | Float                          -- 浮点类型
  | String                         -- 字符串类型
  | Arrow Type Type               -- 函数类型 A → B
  | Product Type Type             -- 积类型 A × B
  | Sum Type Type                 -- 和类型 A + B
  | List Type                     -- 列表类型 [A]
  | Maybe Type                    -- 可选类型 Maybe A
  | Either Type Type              -- 或类型 Either A B
  | ForAll String Type            -- 全称类型 ∀α.A
  | Exists String Type            -- 存在类型 ∃α.A
  | Pi String Type Type           -- 依赖积类型 Πx:A.B
  | Sigma String Type Type        -- 依赖和类型 Σx:A.B

-- 类型相等性
instance Eq Type where
    Unit == Unit = True
    Bool == Bool = True
    Int == Int = True
    Float == Float = True
    String == String = True
    Arrow t1 t2 == Arrow t3 t4 = t1 == t3 && t2 == t4
    Product t1 t2 == Product t3 t4 = t1 == t3 && t2 == t4
    Sum t1 t2 == Sum t3 t4 = t1 == t3 && t2 == t4
    List t1 == List t2 = t1 == t2
    Maybe t1 == Maybe t2 = t1 == t2
    Either t1 t2 == Either t3 t4 = t1 == t3 && t2 == t4
    ForAll alpha t1 == ForAll beta t2 = alpha == beta && t1 == t2
    Exists alpha t1 == Exists beta t2 = alpha == beta && t1 == t2
    Pi x t1 t2 == Pi y t3 t4 = x == y && t1 == t3 && t2 == t4
    Sigma x t1 t2 == Sigma y t3 t4 = x == y && t1 == t3 && t2 == t4
    _ == _ = False
```

#### 类型构造

```haskell
-- 类型构造函数
unitType :: Type
unitType = Unit

boolType :: Type
boolType = Bool

intType :: Type
intType = Int

functionType :: Type -> Type -> Type
functionType dom cod = Arrow dom cod

productType :: Type -> Type -> Type
productType t1 t2 = Product t1 t2

sumType :: Type -> Type -> Type
sumType t1 t2 = Sum t1 t2

listType :: Type -> Type
listType t = List t

maybeType :: Type -> Type
maybeType t = Maybe t

eitherType :: Type -> Type -> Type
eitherType t1 t2 = Either t1 t2

-- 类型构造的语法糖
infixr 9 `functionType`
infixr 8 `productType`
infixr 7 `sumType`
infixr 6 `eitherType`
```

### 2. 项 (Terms)

项是类型的实例，表示具体的值或计算。

#### 2.1 形式化定义

```haskell
-- 项
data Term = 
    UnitTerm                       -- 单位值 ()
  | BoolTerm Bool                  -- 布尔值
  | IntTerm Int                    -- 整数值
  | FloatTerm Float                -- 浮点值
  | StringTerm String              -- 字符串值
  | Variable String                -- 变量 x
  | Lambda String Type Term        -- λ抽象 λx:A.t
  | Application Term Term          -- 应用 t u
  | Pair Term Term                 -- 序对 (t, u)
  | Fst Term                       -- 第一投影 fst t
  | Snd Term                       -- 第二投影 snd t
  | Inl Term                       -- 左注入 inl t
  | Inr Term                       -- 右注入 inr t
  | Case Term String Term String Term  -- 模式匹配 case t of inl x => u | inr y => v
  | Nil                            -- 空列表 []
  | Cons Term Term                 -- 列表构造 t:u
  | CaseList Term Term String String Term  -- 列表模式匹配
  | Nothing                        -- 无值
  | Just Term                      -- 有值 Just t
  | CaseMaybe Term Term String Term  -- 可选模式匹配
  | TypeLambda String Term         -- 类型抽象 Λα.t
  | TypeApplication Term Type      -- 类型应用 t[A]
  | Pack Type Term Type            -- 存在类型打包 pack A,t as ∃α.B
  | Unpack String String Term Term  -- 存在类型解包 unpack α,x = t in u

-- 项的相等性
instance Eq Term where
    UnitTerm == UnitTerm = True
    BoolTerm b1 == BoolTerm b2 = b1 == b2
    IntTerm i1 == IntTerm i2 = i1 == i2
    FloatTerm f1 == FloatTerm f2 = f1 == f2
    StringTerm s1 == StringTerm s2 = s1 == s2
    Variable x == Variable y = x == y
    Lambda x1 t1 u1 == Lambda x2 t2 u2 = x1 == x2 && t1 == t2 && u1 == u2
    Application t1 u1 == Application t2 u2 = t1 == t2 && u1 == u2
    Pair t1 u1 == Pair t2 u2 = t1 == t2 && u1 == u2
    Fst t1 == Fst t2 = t1 == t2
    Snd t1 == Snd t2 = t1 == t2
    Inl t1 == Inl t2 = t1 == t2
    Inr t1 == Inr t2 = t1 == t2
    Case t1 x1 u1 y1 v1 == Case t2 x2 u2 y2 v2 = 
        t1 == t2 && x1 == x2 && u1 == u2 && y1 == y2 && v1 == v2
    Nil == Nil = True
    Cons t1 u1 == Cons t2 u2 = t1 == t2 && u1 == u2
    Nothing == Nothing = True
    Just t1 == Just t2 = t1 == t2
    _ == _ = False
```

#### 项构造

```haskell
-- 基本值构造
unitValue :: Term
unitValue = UnitTerm

boolValue :: Bool -> Term
boolValue b = BoolTerm b

intValue :: Int -> Term
intValue i = IntTerm i

stringValue :: String -> Term
stringValue s = StringTerm s

-- 函数构造
lambda :: String -> Type -> Term -> Term
lambda x tau t = Lambda x tau t

apply :: Term -> Term -> Term
apply t u = Application t u

-- 积类型构造
pair :: Term -> Term -> Term
pair t u = Pair t u

fst :: Term -> Term
fst t = Fst t

snd :: Term -> Term
snd t = Snd t

-- 和类型构造
inl :: Term -> Term
inl t = Inl t

inr :: Term -> Term
inr t = Inr t

caseSum :: Term -> String -> Term -> String -> Term -> Term
caseSum t x u y v = Case t x u y v

-- 列表构造
nil :: Term
nil = Nil

cons :: Term -> Term -> Term
cons t u = Cons t u

caseList :: Term -> Term -> String -> String -> Term -> Term
caseList t nilCase x xs consCase = CaseList t nilCase x xs consCase

-- 可选类型构造
nothing :: Term
nothing = Nothing

just :: Term -> Term
just t = Just t

caseMaybe :: Term -> Term -> String -> Term -> Term
caseMaybe t nothingCase x justCase = CaseMaybe t nothingCase x justCase
```

### 3. 类型关系 (Type Relations)

类型关系定义了项与类型之间的对应关系。

#### 3.1 形式化定义

```haskell
-- 上下文
type Context = [(String, Type)]

-- 类型关系
data TypeRelation = TypeRelation {
    context :: Context,
    term :: Term,
    type_ :: Type
}

-- 类型检查
typeCheck :: Context -> Term -> Maybe Type
typeCheck ctx term = case term of
    UnitTerm -> Just Unit
    BoolTerm _ -> Just Bool
    IntTerm _ -> Just Int
    FloatTerm _ -> Just Float
    StringTerm _ -> Just String
    Variable x -> lookup x ctx
    Lambda x tau t -> do
        tau' <- typeCheck ((x, tau) : ctx) t
        return (Arrow tau tau')
    Application t u -> do
        tau1 <- typeCheck ctx t
        tau2 <- typeCheck ctx u
        case tau1 of
            Arrow dom cod -> 
                if dom == tau2 then Just cod else Nothing
            _ -> Nothing
    Pair t u -> do
        tau1 <- typeCheck ctx t
        tau2 <- typeCheck ctx u
        return (Product tau1 tau2)
    Fst t -> do
        tau <- typeCheck ctx t
        case tau of
            Product tau1 _ -> Just tau1
            _ -> Nothing
    Snd t -> do
        tau <- typeCheck ctx t
        case tau of
            Product _ tau2 -> Just tau2
            _ -> Nothing
    Inl t -> do
        tau <- typeCheck ctx t
        return (Sum tau (error "Unknown type"))
    Inr t -> do
        tau <- typeCheck ctx t
        return (Sum (error "Unknown type") tau)
    Case t x u y v -> do
        tau <- typeCheck ctx t
        case tau of
            Sum tau1 tau2 -> do
                tau3 <- typeCheck ((x, tau1) : ctx) u
                tau4 <- typeCheck ((y, tau2) : ctx) v
                if tau3 == tau4 then Just tau3 else Nothing
            _ -> Nothing
    Nil -> Just (List (error "Unknown type"))
    Cons t u -> do
        tau1 <- typeCheck ctx t
        tau2 <- typeCheck ctx u
        case tau2 of
            List tau -> 
                if tau1 == tau then Just (List tau) else Nothing
            _ -> Nothing
    Nothing -> Just (Maybe (error "Unknown type"))
    Just t -> do
        tau <- typeCheck ctx t
        return (Maybe tau)
    CaseMaybe t u x v -> do
        tau1 <- typeCheck ctx t
        case tau1 of
            Maybe tau -> do
                tau2 <- typeCheck ctx u
                tau3 <- typeCheck ((x, tau) : ctx) v
                if tau2 == tau3 then Just tau2 else Nothing
            _ -> Nothing
    TypeLambda alpha t -> do
        tau <- typeCheck ctx t
        return (ForAll alpha tau)
    TypeApplication t tau -> do
        sigma <- typeCheck ctx t
        case sigma of
            ForAll alpha sigma' -> Just (substitute alpha tau sigma')
            _ -> Nothing
    Pack tau1 t tau2 -> do
        tau3 <- typeCheck ctx t
        if tau3 == substitute alpha tau1 tau2
        then Just (Exists alpha tau2)
        else Nothing
    Unpack alpha x t u -> do
        tau1 <- typeCheck ctx t
        case tau1 of
            Exists beta tau2 -> do
                tau3 <- typeCheck ((x, substitute beta (Variable alpha) tau2) : ctx) u
                return tau3
            _ -> Nothing
```

#### 类型推导

```haskell
-- 类型推导算法
typeInference :: Context -> Term -> Maybe Type
typeInference ctx term = case term of
    UnitTerm -> Just Unit
    BoolTerm _ -> Just Bool
    IntTerm _ -> Just Int
    FloatTerm _ -> Just Float
    StringTerm _ -> Just String
    Variable x -> lookup x ctx
    Lambda x t -> do
        -- 为参数类型生成新变量
        alpha <- freshTypeVariable
        tau <- typeInference ((x, alpha) : ctx) t
        return (Arrow alpha tau)
    Application t u -> do
        tau1 <- typeInference ctx t
        tau2 <- typeInference ctx u
        alpha <- freshTypeVariable
        unify tau1 (Arrow tau2 alpha)
        return alpha
    Pair t u -> do
        tau1 <- typeInference ctx t
        tau2 <- typeInference ctx u
        return (Product tau1 tau2)
    Fst t -> do
        tau <- typeInference ctx t
        alpha <- freshTypeVariable
        beta <- freshTypeVariable
        unify tau (Product alpha beta)
        return alpha
    Snd t -> do
        tau <- typeInference ctx t
        alpha <- freshTypeVariable
        beta <- freshTypeVariable
        unify tau (Product alpha beta)
        return beta
    -- 其他情况类似...
```

### 4. 类型系统性质

#### 类型安全

```haskell
-- 类型安全：良类型的项不会卡住
typeSafety :: TypeTheory -> Bool
typeSafety theory = 
    all (\term -> 
        case typeCheck (context theory) term of
            Just _ -> not (isStuck term)
            Nothing -> True) 
        (terms theory)

-- 检查项是否卡住
isStuck :: Term -> Bool
isStuck term = case term of
    Variable _ -> False
    Lambda _ _ _ -> False
    Application t1 t2 -> 
        isStuck t1 || isStuck t2 || 
        (isValue t1 && isValue t2 && not (isReducible term))
    Pair t1 t2 -> isStuck t1 || isStuck t2
    Fst t -> isStuck t || not (isPair t)
    Snd t -> isStuck t || not (isPair t)
    Inl t -> isStuck t
    Inr t -> isStuck t
    Case t _ _ _ _ -> isStuck t || not (isSum t)
    Nil -> False
    Cons t u -> isStuck t || isStuck u
    CaseList t _ _ _ _ -> isStuck t || not (isList t)
    Nothing -> False
    Just t -> isStuck t
    CaseMaybe t _ _ _ -> isStuck t || not (isMaybe t)
    _ -> False

-- 检查项是否为值
isValue :: Term -> Bool
isValue term = case term of
    UnitTerm -> True
    BoolTerm _ -> True
    IntTerm _ -> True
    FloatTerm _ -> True
    StringTerm _ -> True
    Lambda _ _ _ -> True
    Pair t u -> isValue t && isValue u
    Inl t -> isValue t
    Inr t -> isValue t
    Nil -> True
    Cons t u -> isValue t && isValue u
    Nothing -> True
    Just t -> isValue t
    TypeLambda _ _ -> True
    Pack _ t _ -> isValue t
    _ -> False
```

#### 进展性

```haskell
-- 进展性：良类型的项要么是值，要么可以归约
progress :: TypeTheory -> Bool
progress theory = 
    all (\term -> 
        case typeCheck (context theory) term of
            Just _ -> isValue term || isReducible term
            Nothing -> True) 
        (terms theory)

-- 检查项是否可归约
isReducible :: Term -> Bool
isReducible term = case term of
    Application (Lambda _ _ _) _ -> True
    Fst (Pair _ _) -> True
    Snd (Pair _ _) -> True
    Case (Inl _) _ _ _ _ -> True
    Case (Inr _) _ _ _ _ -> True
    CaseList Nil _ _ _ _ -> True
    CaseList (Cons _ _) _ _ _ _ -> True
    CaseMaybe Nothing _ _ _ -> True
    CaseMaybe (Just _) _ _ _ -> True
    TypeApplication (TypeLambda _ _) _ -> True
    Unpack (Pack _ _ _) _ _ _ -> True
    _ -> False
```

## 应用示例

### 1. 简单类型系统

```haskell
-- 简单类型λ演算
data STLC = STLC {
    context :: Context,
    typingRules :: [TypingRule],
    reductionRules :: [ReductionRule]
}

-- 类型规则
data TypingRule = 
    VarRule                       -- 变量规则
  | AbsRule                       -- 抽象规则
  | AppRule                       -- 应用规则
  | PairRule                      -- 序对规则
  | FstRule                       -- 第一投影规则
  | SndRule                       -- 第二投影规则

-- 归约规则
data ReductionRule = 
    BetaReduction                 -- β归约
  | FstReduction                  -- 第一投影归约
  | SndReduction                  -- 第二投影归约
  | EtaReduction                  -- η归约

-- STLC类型检查
stlcTypeCheck :: Context -> Term -> Maybe Type
stlcTypeCheck ctx term = case term of
    Variable x -> lookup x ctx
    Lambda x tau t -> do
        tau' <- stlcTypeCheck ((x, tau) : ctx) t
        return (Arrow tau tau')
    Application t u -> do
        tau1 <- stlcTypeCheck ctx t
        tau2 <- stlcTypeCheck ctx u
        case tau1 of
            Arrow dom cod -> 
                if dom == tau2 then Just cod else Nothing
            _ -> Nothing
    Pair t u -> do
        tau1 <- stlcTypeCheck ctx t
        tau2 <- stlcTypeCheck ctx u
        return (Product tau1 tau2)
    Fst t -> do
        tau <- stlcTypeCheck ctx t
        case tau of
            Product tau1 _ -> Just tau1
            _ -> Nothing
    Snd t -> do
        tau <- stlcTypeCheck ctx t
        case tau of
            Product _ tau2 -> Just tau2
            _ -> Nothing
```

### 2. 多态类型系统

```haskell
-- System F
data SystemF = SystemF {
    typeVariables :: [String],
    termVariables :: [String],
    typingRules :: [SystemFTypingRule]
}

-- System F类型规则
data SystemFTypingRule = 
    TVarRule                      -- 类型变量规则
  | TAbsRule                      -- 类型抽象规则
  | TAppRule                      -- 类型应用规则
  | VarRule                       -- 变量规则
  | AbsRule                       -- 抽象规则
  | AppRule                       -- 应用规则

-- System F类型检查
systemFTypeCheck :: Context -> TypeContext -> Term -> Maybe Type
systemFTypeCheck ctx typeCtx term = case term of
    Variable x -> lookup x ctx
    Lambda x tau t -> do
        tau' <- systemFTypeCheck ((x, tau) : ctx) typeCtx t
        return (Arrow tau tau')
    Application t1 t2 -> do
        tau1 <- systemFTypeCheck ctx typeCtx t1
        tau2 <- systemFTypeCheck ctx typeCtx t2
        case tau1 of
            Arrow dom cod -> 
                if dom == tau2 then Just cod else Nothing
            _ -> Nothing
    TypeLambda alpha t -> do
        tau <- systemFTypeCheck ctx (alpha : typeCtx) t
        return (ForAll alpha tau)
    TypeApplication t tau -> do
        sigma <- systemFTypeCheck ctx typeCtx t
        case sigma of
            ForAll alpha sigma' -> Just (substitute alpha tau sigma')
            _ -> Nothing
```

## 与理论层的关系

类型论基础为理论层提供：

1. **语义基础**：编程语言语义的类型论解释
2. **类型系统**：类型系统的理论基础
3. **证明系统**：定理证明的类型论基础
4. **计算模型**：λ演算的计算模型

## 与具体科学层的关系

类型论基础指导具体科学层的应用：

1. **函数式编程**：类型系统的理论基础
2. **编译器设计**：类型检查和推导算法
3. **定理证明**：构造性证明系统
4. **程序验证**：类型安全的程序验证

## 相关链接

- [类型论主索引](../README.md)
- [类型与项](02-Types-and-Terms.md)
- [类型检查](03-Type-Checking.md)
- [类型推导](04-Type-Inference.md)
- [形式科学层主索引](../../README.md)
- [理论层](../../../03-Theory/README.md)
