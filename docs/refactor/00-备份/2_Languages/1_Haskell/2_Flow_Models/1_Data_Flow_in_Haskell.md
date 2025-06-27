# 1. Data Flow in Haskell

## 1.1. Core Principles

Data flow in Haskell is fundamentally different from imperative languages. It is shaped by two core principles:

1. **Purity**: Functions in Haskell are pure by default. This means their output depends only on their input, and they have no side effects (e.g., modifying state, I/O). This makes data flow explicit and easy to reason about. Data "flows" from one function to the next without hidden dependencies or modifications.

2. **Immutability**: Data structures in Haskell are immutable. When a "change" is needed, a new data structure is created instead of modifying the existing one. This prevents entire classes of bugs related to shared mutable state and simplifies understanding how data transforms through a program.

## 1.2. Mechanisms of Data Flow

The primary mechanism for data flow is **function composition**. Data flows through a pipeline of functions, where the output of one becomes the input of the next.

### Example: A Simple Data Transformation Pipeline

Consider a simple task: take a list of numbers, select the even ones, square them, and sum the result.

```haskell
processNumbers :: [Int] -> Int
processNumbers = sum . map (^2) . filter even

-- Example usage:
-- ghci> processNumbers [1, 2, 3, 4, 5]
-- 20
```

### 1.3. Visualizing the Flow

We can visualize this as a direct, linear flow:

```mermaid
graph TD
    A[Input: [1, 2, 3, 4, 5]] --> B(filter even);
    B --> C{Output: [2, 4]};
    C --> D(map (^2));
    D --> E{Output: [4, 16]};
    E --> F(sum);
    F --> G[Output: 20];
```

This diagram clearly shows how data is transformed at each stage. The next sections will explore more complex data flow patterns, including how monads manage the flow of data in the context of effects.
