# 迭代器模式（Iterator Pattern）

## 概述

迭代器模式是一种行为型设计模式，提供一种方法顺序访问聚合对象中的元素，而不暴露其内部表示。

## 理论基础

- **封装遍历逻辑**：将遍历逻辑封装在迭代器中
- **统一接口**：提供统一的遍历接口
- **支持多种遍历**：支持不同的遍历策略

## Rust实现示例

```rust
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
    fn has_next(&self) -> bool;
}

struct ConcreteAggregate {
    items: Vec<String>,
}

impl ConcreteAggregate {
    fn new() -> Self {
        Self { items: Vec::new() }
    }
    
    fn add_item(&mut self, item: String) {
        self.items.push(item);
    }
    
    fn create_iterator(&self) -> ConcreteIterator {
        ConcreteIterator {
            aggregate: self,
            index: 0,
        }
    }
}

struct ConcreteIterator<'a> {
    aggregate: &'a ConcreteAggregate,
    index: usize,
}

impl<'a> Iterator for ConcreteIterator<'a> {
    type Item = &'a String;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.aggregate.items.len() {
            let item = &self.aggregate.items[self.index];
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }
    
    fn has_next(&self) -> bool {
        self.index < self.aggregate.items.len()
    }
}

fn main() {
    let mut aggregate = ConcreteAggregate::new();
    aggregate.add_item("Item 1".to_string());
    aggregate.add_item("Item 2".to_string());
    aggregate.add_item("Item 3".to_string());
    
    let mut iterator = aggregate.create_iterator();
    while iterator.has_next() {
        if let Some(item) = iterator.next() {
            println!("{}", item);
        }
    }
}
```

## Haskell实现示例

```haskell
class Iterator a where
    next :: a -> Maybe (String, a)
    hasNext :: a -> Bool

data ConcreteAggregate = ConcreteAggregate [String]
newAggregate :: ConcreteAggregate
newAggregate = ConcreteAggregate []
addItem :: ConcreteAggregate -> String -> ConcreteAggregate
addItem (ConcreteAggregate items) item = ConcreteAggregate (item : items)
createIterator :: ConcreteAggregate -> ConcreteIterator
createIterator (ConcreteAggregate items) = ConcreteIterator items

data ConcreteIterator = ConcreteIterator [String]
instance Iterator ConcreteIterator where
    next (ConcreteIterator []) = Nothing
    next (ConcreteIterator (x:xs)) = Just (x, ConcreteIterator xs)
    hasNext (ConcreteIterator []) = False
    hasNext (ConcreteIterator (_:_)) = True

main = do
    let aggregate = addItem (addItem (addItem newAggregate "Item 1") "Item 2") "Item 3"
    let iterator = createIterator aggregate
    mapM_ print $ iterateWhile hasNext next iterator
  where
    iterateWhile p f x = case f x of
        Just (item, next_x) -> item : iterateWhile p f next_x
        Nothing -> []
```

## Lean实现思路

```lean
class Iterator (α : Type) where
  next : α → Option (String × α)
  hasNext : α → Bool

structure ConcreteAggregate where
  items : List String

def newAggregate : ConcreteAggregate := { items := [] }
def addItem (agg : ConcreteAggregate) (item : String) : ConcreteAggregate :=
  { agg with items := item :: agg.items }
def createIterator (agg : ConcreteAggregate) : ConcreteIterator :=
  { items := agg.items }

structure ConcreteIterator where
  items : List String

instance : Iterator ConcreteIterator where
  next iterator := match iterator.items with
    | [] => none
    | x :: xs => some (x, { iterator with items := xs })
  hasNext iterator := not (iterator.items.isEmpty)
```

## 应用场景

- 集合遍历
- 数据库查询结果遍历
- 文件系统遍历
- 网络数据流处理

## 最佳实践

- 提供多种迭代策略
- 支持并发安全迭代
- 优化内存使用
