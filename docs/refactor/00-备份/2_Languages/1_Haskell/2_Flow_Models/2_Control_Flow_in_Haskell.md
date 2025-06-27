# 2. Control Flow in Haskell

## 2.1. Declarative Control Flow

Unlike imperative languages that rely on loops, `if/else` statements, and exceptions, Haskell's control flow is primarily declarative. Programmers *declare* how to handle different cases rather than specifying a sequence of steps. The main mechanisms for this are pattern matching, guards, and monads.

## 2.2. Pattern Matching and Guards

Pattern matching is the most common form of control flow in Haskell. It allows a function to behave differently based on the structure of its input.

### Example: Factorial Function

```haskell
-- Using pattern matching on the value
factorial :: Word -> Word
factorial 0 = 1
factorial n = n * factorial (n - 1)
```

Guards can be used to add more complex boolean conditions to patterns.

```haskell
-- Using guards to define a function piecewise
describeNumber :: Int -> String
describeNumber n
  | n == 0    = "Zero"
  | odd n     = "An odd number"
  | otherwise = "An even number"
```

### 2.3. Monadic Control Flow

For programs with effects (like I/O, state, or potential failure), monads provide a powerful way to structure control flow. The `do` notation creates what looks like an imperative sequence, but is actually building a nested structure of monadic function calls.

### Example: User Interaction in IO

```haskell
-- This looks sequential, but it's composing IO actions
askAndGreet :: IO ()
askAndGreet = do
    putStrLn "What is your name?"
    name <- getLine
    if null name
        then putStrLn "Fine, be that way."
        else putStrLn ("Hello, " ++ name ++ "!")
```

### 2.4. Visualizing the Flow

We can visualize the monadic control flow for `askAndGreet` as a sequence of actions that depend on the context of `IO`.

```mermaid
graph TD
    A[Start] --> B(putStrLn "What is your name?");
    B --> C(getLine);
    C --> D{name};
    D --> E{if null name};
    E -- True --> F(putStrLn "Fine...");
    E -- False --> G(putStrLn "Hello, ...");
    F --> H[End];
    G --> H;
```

This illustrates how monads allow us to chain operations together in a way that is both expressive and pure, separating the description of the control flow from its execution.
