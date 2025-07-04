# 时序逻辑 (Temporal Logic)

## 概述

时序逻辑是形式化验证和模型检测的核心理论，用于描述和验证系统的时间相关性质。它包括线性时序逻辑(LTL)、计算树逻辑(CTL)和分支时序逻辑(CTL*)等。

## 核心概念

### 1. 线性时序逻辑 (LTL)

- **原子命题**: 基本的状态属性
- **时序算子**: G(全局)、F(未来)、X(下一个)、U(直到)
- **逻辑连接词**: ∧(与)、∨(或)、¬(非)、→(蕴含)

### 2. 分支时序逻辑 (CTL)

- **路径量词**: A(所有路径)、E(存在路径)
- **时序算子**: G(全局)、F(未来)、X(下一个)、U(直到)
- **状态公式**: 描述状态性质
- **路径公式**: 描述路径性质

## 理论基础

### 1. LTL语法和语义

```rust
#[derive(Debug, Clone, PartialEq)]
enum LTLFormula {
    Atom(String),
    Not(Box<LTLFormula>),
    And(Box<LTLFormula>, Box<LTLFormula>),
    Or(Box<LTLFormula>, Box<LTLFormula>),
    Implies(Box<LTLFormula>, Box<LTLFormula>),
    Next(Box<LTLFormula>),
    Until(Box<LTLFormula>, Box<LTLFormula>),
    Globally(Box<LTLFormula>),
    Finally(Box<LTLFormula>),
}

impl LTLFormula {
    fn atom(name: &str) -> Self {
        LTLFormula::Atom(name.to_string())
    }
    
    fn not(formula: LTLFormula) -> Self {
        LTLFormula::Not(Box::new(formula))
    }
    
    fn and(left: LTLFormula, right: LTLFormula) -> Self {
        LTLFormula::And(Box::new(left), Box::new(right))
    }
    
    fn or(left: LTLFormula, right: LTLFormula) -> Self {
        LTLFormula::Or(Box::new(left), Box::new(right))
    }
    
    fn implies(left: LTLFormula, right: LTLFormula) -> Self {
        LTLFormula::Implies(Box::new(left), Box::new(right))
    }
    
    fn next(formula: LTLFormula) -> Self {
        LTLFormula::Next(Box::new(formula))
    }
    
    fn until(left: LTLFormula, right: LTLFormula) -> Self {
        LTLFormula::Until(Box::new(left), Box::new(right))
    }
    
    fn globally(formula: LTLFormula) -> Self {
        LTLFormula::Globally(Box::new(formula))
    }
    
    fn finally(formula: LTLFormula) -> Self {
        LTLFormula::Finally(Box::new(formula))
    }
}

// LTL模型检测
struct LTLModelChecker {
    states: Vec<String>,
    transitions: Vec<(String, String)>,
    labels: HashMap<String, Vec<String>>,
}

impl LTLModelChecker {
    fn new() -> Self {
        Self {
            states: Vec::new(),
            transitions: Vec::new(),
            labels: HashMap::new(),
        }
    }
    
    fn add_state(&mut self, state: String) {
        self.states.push(state);
    }
    
    fn add_transition(&mut self, from: String, to: String) {
        self.transitions.push((from, to));
    }
    
    fn add_label(&mut self, state: String, label: String) {
        self.labels.entry(state).or_insert_with(Vec::new).push(label);
    }
    
    fn check_ltl(&self, formula: &LTLFormula, state: &str) -> bool {
        match formula {
            LTLFormula::Atom(name) => {
                self.labels.get(state)
                    .map(|labels| labels.contains(name))
                    .unwrap_or(false)
            }
            LTLFormula::Not(f) => !self.check_ltl(f, state),
            LTLFormula::And(left, right) => {
                self.check_ltl(left, state) && self.check_ltl(right, state)
            }
            LTLFormula::Or(left, right) => {
                self.check_ltl(left, state) || self.check_ltl(right, state)
            }
            LTLFormula::Implies(left, right) => {
                !self.check_ltl(left, state) || self.check_ltl(right, state)
            }
            LTLFormula::Next(f) => {
                self.check_next(f, state)
            }
            LTLFormula::Until(left, right) => {
                self.check_until(left, right, state)
            }
            LTLFormula::Globally(f) => {
                self.check_globally(f, state)
            }
            LTLFormula::Finally(f) => {
                self.check_finally(f, state)
            }
        }
    }
    
    fn check_next(&self, formula: &LTLFormula, state: &str) -> bool {
        // 检查所有后继状态
        for (from, to) in &self.transitions {
            if from == state {
                if !self.check_ltl(formula, to) {
                    return false;
                }
            }
        }
        true
    }
    
    fn check_until(&self, left: &LTLFormula, right: &LTLFormula, state: &str) -> bool {
        // 简化实现：检查是否存在路径满足 left U right
        self.check_until_recursive(left, right, state, &mut Vec::new())
    }
    
    fn check_until_recursive(&self, left: &LTLFormula, right: &LTLFormula, 
                           state: &str, visited: &mut Vec<String>) -> bool {
        if visited.contains(&state.to_string()) {
            return false; // 避免循环
        }
        
        visited.push(state.to_string());
        
        // 检查当前状态是否满足right
        if self.check_ltl(right, state) {
            visited.pop();
            return true;
        }
        
        // 检查当前状态是否满足left
        if !self.check_ltl(left, state) {
            visited.pop();
            return false;
        }
        
        // 检查后继状态
        for (from, to) in &self.transitions {
            if from == state {
                if self.check_until_recursive(left, right, to, visited) {
                    visited.pop();
                    return true;
                }
            }
        }
        
        visited.pop();
        false
    }
    
    fn check_globally(&self, formula: &LTLFormula, state: &str) -> bool {
        // 检查所有可达状态是否都满足formula
        self.check_globally_recursive(formula, state, &mut Vec::new())
    }
    
    fn check_globally_recursive(&self, formula: &LTLFormula, state: &str, 
                              visited: &mut Vec<String>) -> bool {
        if visited.contains(&state.to_string()) {
            return true; // 已访问过的状态假设满足
        }
        
        visited.push(state.to_string());
        
        // 检查当前状态
        if !self.check_ltl(formula, state) {
            visited.pop();
            return false;
        }
        
        // 检查后继状态
        for (from, to) in &self.transitions {
            if from == state {
                if !self.check_globally_recursive(formula, to, visited) {
                    visited.pop();
                    return false;
                }
            }
        }
        
        visited.pop();
        true
    }
    
    fn check_finally(&self, formula: &LTLFormula, state: &str) -> bool {
        // 检查是否存在路径最终满足formula
        self.check_finally_recursive(formula, state, &mut Vec::new())
    }
    
    fn check_finally_recursive(&self, formula: &LTLFormula, state: &str, 
                             visited: &mut Vec<String>) -> bool {
        if visited.contains(&state.to_string()) {
            return false; // 避免循环
        }
        
        visited.push(state.to_string());
        
        // 检查当前状态
        if self.check_ltl(formula, state) {
            visited.pop();
            return true;
        }
        
        // 检查后继状态
        for (from, to) in &self.transitions {
            if from == state {
                if self.check_finally_recursive(formula, to, visited) {
                    visited.pop();
                    return true;
                }
            }
        }
        
        visited.pop();
        false
    }
}
```

### 2. CTL语法和语义

```rust
#[derive(Debug, Clone, PartialEq)]
enum CTLFormula {
    Atom(String),
    Not(Box<CTLFormula>),
    And(Box<CTLFormula>, Box<CTLFormula>),
    Or(Box<CTLFormula>, Box<CTLFormula>),
    Implies(Box<CTLFormula>, Box<CTLFormula>),
    AX(Box<CTLFormula>),
    EX(Box<CTLFormula>),
    AG(Box<CTLFormula>),
    EG(Box<CTLFormula>),
    AF(Box<CTLFormula>),
    EF(Box<CTLFormula>),
    AU(Box<CTLFormula>, Box<CTLFormula>),
    EU(Box<CTLFormula>, Box<CTLFormula>),
}

impl CTLFormula {
    fn atom(name: &str) -> Self {
        CTLFormula::Atom(name.to_string())
    }
    
    fn not(formula: CTLFormula) -> Self {
        CTLFormula::Not(Box::new(formula))
    }
    
    fn and(left: CTLFormula, right: CTLFormula) -> Self {
        CTLFormula::And(Box::new(left), Box::new(right))
    }
    
    fn or(left: CTLFormula, right: CTLFormula) -> Self {
        CTLFormula::Or(Box::new(left), Box::new(right))
    }
    
    fn implies(left: CTLFormula, right: CTLFormula) -> Self {
        CTLFormula::Implies(Box::new(left), Box::new(right))
    }
    
    fn ax(formula: CTLFormula) -> Self {
        CTLFormula::AX(Box::new(formula))
    }
    
    fn ex(formula: CTLFormula) -> Self {
        CTLFormula::EX(Box::new(formula))
    }
    
    fn ag(formula: CTLFormula) -> Self {
        CTLFormula::AG(Box::new(formula))
    }
    
    fn eg(formula: CTLFormula) -> Self {
        CTLFormula::EG(Box::new(formula))
    }
    
    fn af(formula: CTLFormula) -> Self {
        CTLFormula::AF(Box::new(formula))
    }
    
    fn ef(formula: CTLFormula) -> Self {
        CTLFormula::EF(Box::new(formula))
    }
    
    fn au(left: CTLFormula, right: CTLFormula) -> Self {
        CTLFormula::AU(Box::new(left), Box::new(right))
    }
    
    fn eu(left: CTLFormula, right: CTLFormula) -> Self {
        CTLFormula::EU(Box::new(left), Box::new(right))
    }
}

struct CTLModelChecker {
    states: Vec<String>,
    transitions: Vec<(String, String)>,
    labels: HashMap<String, Vec<String>>,
}

impl CTLModelChecker {
    fn new() -> Self {
        Self {
            states: Vec::new(),
            transitions: Vec::new(),
            labels: HashMap::new(),
        }
    }
    
    fn add_state(&mut self, state: String) {
        self.states.push(state);
    }
    
    fn add_transition(&mut self, from: String, to: String) {
        self.transitions.push((from, to));
    }
    
    fn add_label(&mut self, state: String, label: String) {
        self.labels.entry(state).or_insert_with(Vec::new).push(label);
    }
    
    fn check_ctl(&self, formula: &CTLFormula, state: &str) -> bool {
        match formula {
            CTLFormula::Atom(name) => {
                self.labels.get(state)
                    .map(|labels| labels.contains(name))
                    .unwrap_or(false)
            }
            CTLFormula::Not(f) => !self.check_ctl(f, state),
            CTLFormula::And(left, right) => {
                self.check_ctl(left, state) && self.check_ctl(right, state)
            }
            CTLFormula::Or(left, right) => {
                self.check_ctl(left, state) || self.check_ctl(right, state)
            }
            CTLFormula::Implies(left, right) => {
                !self.check_ctl(left, state) || self.check_ctl(right, state)
            }
            CTLFormula::AX(f) => self.check_ax(f, state),
            CTLFormula::EX(f) => self.check_ex(f, state),
            CTLFormula::AG(f) => self.check_ag(f, state),
            CTLFormula::EG(f) => self.check_eg(f, state),
            CTLFormula::AF(f) => self.check_af(f, state),
            CTLFormula::EF(f) => self.check_ef(f, state),
            CTLFormula::AU(left, right) => self.check_au(left, right, state),
            CTLFormula::EU(left, right) => self.check_eu(left, right, state),
        }
    }
    
    fn check_ax(&self, formula: &CTLFormula, state: &str) -> bool {
        // 所有后继状态都满足formula
        for (from, to) in &self.transitions {
            if from == state {
                if !self.check_ctl(formula, to) {
                    return false;
                }
            }
        }
        true
    }
    
    fn check_ex(&self, formula: &CTLFormula, state: &str) -> bool {
        // 存在后继状态满足formula
        for (from, to) in &self.transitions {
            if from == state {
                if self.check_ctl(formula, to) {
                    return true;
                }
            }
        }
        false
    }
    
    fn check_ag(&self, formula: &CTLFormula, state: &str) -> bool {
        // 所有路径的所有状态都满足formula
        self.check_ag_recursive(formula, state, &mut Vec::new())
    }
    
    fn check_ag_recursive(&self, formula: &CTLFormula, state: &str, 
                         visited: &mut Vec<String>) -> bool {
        if visited.contains(&state.to_string()) {
            return true; // 已访问过的状态假设满足
        }
        
        visited.push(state.to_string());
        
        // 检查当前状态
        if !self.check_ctl(formula, state) {
            visited.pop();
            return false;
        }
        
        // 检查所有后继状态
        for (from, to) in &self.transitions {
            if from == state {
                if !self.check_ag_recursive(formula, to, visited) {
                    visited.pop();
                    return false;
                }
            }
        }
        
        visited.pop();
        true
    }
    
    fn check_eg(&self, formula: &CTLFormula, state: &str) -> bool {
        // 存在路径的所有状态都满足formula
        self.check_eg_recursive(formula, state, &mut Vec::new())
    }
    
    fn check_eg_recursive(&self, formula: &CTLFormula, state: &str, 
                         visited: &mut Vec<String>) -> bool {
        if visited.contains(&state.to_string()) {
            return true; // 循环路径满足EG
        }
        
        visited.push(state.to_string());
        
        // 检查当前状态
        if !self.check_ctl(formula, state) {
            visited.pop();
            return false;
        }
        
        // 检查是否存在后继状态满足EG
        for (from, to) in &self.transitions {
            if from == state {
                if self.check_eg_recursive(formula, to, visited) {
                    visited.pop();
                    return true;
                }
            }
        }
        
        visited.pop();
        false
    }
    
    fn check_af(&self, formula: &CTLFormula, state: &str) -> bool {
        // 所有路径最终都满足formula
        self.check_af_recursive(formula, state, &mut Vec::new())
    }
    
    fn check_af_recursive(&self, formula: &CTLFormula, state: &str, 
                         visited: &mut Vec<String>) -> bool {
        if visited.contains(&state.to_string()) {
            return false; // 避免循环
        }
        
        visited.push(state.to_string());
        
        // 检查当前状态
        if self.check_ctl(formula, state) {
            visited.pop();
            return true;
        }
        
        // 检查所有后继状态
        for (from, to) in &self.transitions {
            if from == state {
                if !self.check_af_recursive(formula, to, visited) {
                    visited.pop();
                    return false;
                }
            }
        }
        
        visited.pop();
        true
    }
    
    fn check_ef(&self, formula: &CTLFormula, state: &str) -> bool {
        // 存在路径最终满足formula
        self.check_ef_recursive(formula, state, &mut Vec::new())
    }
    
    fn check_ef_recursive(&self, formula: &CTLFormula, state: &str, 
                         visited: &mut Vec<String>) -> bool {
        if visited.contains(&state.to_string()) {
            return false; // 避免循环
        }
        
        visited.push(state.to_string());
        
        // 检查当前状态
        if self.check_ctl(formula, state) {
            visited.pop();
            return true;
        }
        
        // 检查后继状态
        for (from, to) in &self.transitions {
            if from == state {
                if self.check_ef_recursive(formula, to, visited) {
                    visited.pop();
                    return true;
                }
            }
        }
        
        visited.pop();
        false
    }
    
    fn check_au(&self, left: &CTLFormula, right: &CTLFormula, state: &str) -> bool {
        // 所有路径都满足 left U right
        self.check_au_recursive(left, right, state, &mut Vec::new())
    }
    
    fn check_au_recursive(&self, left: &CTLFormula, right: &CTLFormula, 
                         state: &str, visited: &mut Vec<String>) -> bool {
        if visited.contains(&state.to_string()) {
            return false; // 避免循环
        }
        
        visited.push(state.to_string());
        
        // 检查当前状态是否满足right
        if self.check_ctl(right, state) {
            visited.pop();
            return true;
        }
        
        // 检查当前状态是否满足left
        if !self.check_ctl(left, state) {
            visited.pop();
            return false;
        }
        
        // 检查所有后继状态
        for (from, to) in &self.transitions {
            if from == state {
                if !self.check_au_recursive(left, right, to, visited) {
                    visited.pop();
                    return false;
                }
            }
        }
        
        visited.pop();
        true
    }
    
    fn check_eu(&self, left: &CTLFormula, right: &CTLFormula, state: &str) -> bool {
        // 存在路径满足 left U right
        self.check_eu_recursive(left, right, state, &mut Vec::new())
    }
    
    fn check_eu_recursive(&self, left: &CTLFormula, right: &CTLFormula, 
                         state: &str, visited: &mut Vec<String>) -> bool {
        if visited.contains(&state.to_string()) {
            return false; // 避免循环
        }
        
        visited.push(state.to_string());
        
        // 检查当前状态是否满足right
        if self.check_ctl(right, state) {
            visited.pop();
            return true;
        }
        
        // 检查当前状态是否满足left
        if !self.check_ctl(left, state) {
            visited.pop();
            return false;
        }
        
        // 检查后继状态
        for (from, to) in &self.transitions {
            if from == state {
                if self.check_eu_recursive(left, right, to, visited) {
                    visited.pop();
                    return true;
                }
            }
        }
        
        visited.pop();
        false
    }
}
```

## Haskell实现示例

```haskell
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- LTL公式定义
data LTLFormula = Atom String
                | Not LTLFormula
                | And LTLFormula LTLFormula
                | Or LTLFormula LTLFormula
                | Implies LTLFormula LTLFormula
                | Next LTLFormula
                | Until LTLFormula LTLFormula
                | Globally LTLFormula
                | Finally LTLFormula
                deriving (Show, Eq)

-- CTL公式定义
data CTLFormula = CTLAtom String
                | CTLNot CTLFormula
                | CTLAnd CTLFormula CTLFormula
                | CTLOr CTLFormula CTLFormula
                | CTLImplies CTLFormula CTLFormula
                | AX CTLFormula
                | EX CTLFormula
                | AG CTLFormula
                | EG CTLFormula
                | AF CTLFormula
                | EF CTLFormula
                | AU CTLFormula CTLFormula
                | EU CTLFormula CTLFormula
                deriving (Show, Eq)

-- 模型定义
data Model = Model
    { states :: Set String
    , transitions :: Set (String, String)
    , labels :: Map String (Set String)
    }

-- LTL模型检测
checkLTL :: Model -> LTLFormula -> String -> Bool
checkLTL model formula state = 
    case formula of
        Atom name -> 
            case Map.lookup state (labels model) of
                Just labelSet -> Set.member name labelSet
                Nothing -> False
        Not f -> not (checkLTL model f state)
        And left right -> 
            checkLTL model left state && checkLTL model right state
        Or left right -> 
            checkLTL model left state || checkLTL model right state
        Implies left right -> 
            not (checkLTL model left state) || checkLTL model right state
        Next f -> checkNext model f state
        Until left right -> checkUntil model left right state
        Globally f -> checkGlobally model f state
        Finally f -> checkFinally model f state

checkNext :: Model -> LTLFormula -> String -> Bool
checkNext model formula state = 
    let successors = [to | (from, to) <- Set.toList (transitions model), from == state]
    in all (\s -> checkLTL model formula s) successors

checkUntil :: Model -> LTLFormula -> LTLFormula -> String -> Bool
checkUntil model left right state = 
    checkUntilRecursive model left right state Set.empty

checkUntilRecursive :: Model -> LTLFormula -> LTLFormula -> String -> Set String -> Bool
checkUntilRecursive model left right state visited
    | Set.member state visited = False
    | checkLTL model right state = True
    | not (checkLTL model left state) = False
    | otherwise = 
        let successors = [to | (from, to) <- Set.toList (transitions model), from == state]
            newVisited = Set.insert state visited
        in any (\s -> checkUntilRecursive model left right s newVisited) successors

checkGlobally :: Model -> LTLFormula -> String -> Bool
checkGlobally model formula state = 
    checkGloballyRecursive model formula state Set.empty

checkGloballyRecursive :: Model -> LTLFormula -> String -> Set String -> Bool
checkGloballyRecursive model formula state visited
    | Set.member state visited = True
    | not (checkLTL model formula state) = False
    | otherwise = 
        let successors = [to | (from, to) <- Set.toList (transitions model), from == state]
            newVisited = Set.insert state visited
        in all (\s -> checkGloballyRecursive model formula s newVisited) successors

checkFinally :: Model -> LTLFormula -> String -> Bool
checkFinally model formula state = 
    checkFinallyRecursive model formula state Set.empty

checkFinallyRecursive :: Model -> LTLFormula -> String -> Set String -> Bool
checkFinallyRecursive model formula state visited
    | Set.member state visited = False
    | checkLTL model formula state = True
    | otherwise = 
        let successors = [to | (from, to) <- Set.toList (transitions model), from == state]
            newVisited = Set.insert state visited
        in any (\s -> checkFinallyRecursive model formula s newVisited) successors

-- CTL模型检测
checkCTL :: Model -> CTLFormula -> String -> Bool
checkCTL model formula state = 
    case formula of
        CTLAtom name -> 
            case Map.lookup state (labels model) of
                Just labelSet -> Set.member name labelSet
                Nothing -> False
        CTLNot f -> not (checkCTL model f state)
        CTLAnd left right -> 
            checkCTL model left state && checkCTL model right state
        CTLOr left right -> 
            checkCTL model left state || checkCTL model right state
        CTLImplies left right -> 
            not (checkCTL model left state) || checkCTL model right state
        AX f -> checkAX model f state
        EX f -> checkEX model f state
        AG f -> checkAG model f state
        EG f -> checkEG model f state
        AF f -> checkAF model f state
        EF f -> checkEF model f state
        AU left right -> checkAU model left right state
        EU left right -> checkEU model left right state

checkAX :: Model -> CTLFormula -> String -> Bool
checkAX model formula state = 
    let successors = [to | (from, to) <- Set.toList (transitions model), from == state]
    in all (\s -> checkCTL model formula s) successors

checkEX :: Model -> CTLFormula -> String -> Bool
checkEX model formula state = 
    let successors = [to | (from, to) <- Set.toList (transitions model), from == state]
    in any (\s -> checkCTL model formula s) successors

checkAG :: Model -> CTLFormula -> String -> Bool
checkAG model formula state = 
    checkAGRecursive model formula state Set.empty

checkAGRecursive :: Model -> CTLFormula -> String -> Set String -> Bool
checkAGRecursive model formula state visited
    | Set.member state visited = True
    | not (checkCTL model formula state) = False
    | otherwise = 
        let successors = [to | (from, to) <- Set.toList (transitions model), from == state]
            newVisited = Set.insert state visited
        in all (\s -> checkAGRecursive model formula s newVisited) successors

checkEG :: Model -> CTLFormula -> String -> Bool
checkEG model formula state = 
    checkEGRecursive model formula state Set.empty

checkEGRecursive :: Model -> CTLFormula -> String -> Set String -> Bool
checkEGRecursive model formula state visited
    | Set.member state visited = True
    | not (checkCTL model formula state) = False
    | otherwise = 
        let successors = [to | (from, to) <- Set.toList (transitions model), from == state]
            newVisited = Set.insert state visited
        in any (\s -> checkEGRecursive model formula s newVisited) successors

checkAF :: Model -> CTLFormula -> String -> Bool
checkAF model formula state = 
    checkAFRecursive model formula state Set.empty

checkAFRecursive :: Model -> CTLFormula -> String -> Set String -> Bool
checkAFRecursive model formula state visited
    | Set.member state visited = False
    | checkCTL model formula state = True
    | otherwise = 
        let successors = [to | (from, to) <- Set.toList (transitions model), from == state]
            newVisited = Set.insert state visited
        in all (\s -> checkAFRecursive model formula s newVisited) successors

checkEF :: Model -> CTLFormula -> String -> Bool
checkEF model formula state = 
    checkEFRecursive model formula state Set.empty

checkEFRecursive :: Model -> CTLFormula -> String -> Set String -> Bool
checkEFRecursive model formula state visited
    | Set.member state visited = False
    | checkCTL model formula state = True
    | otherwise = 
        let successors = [to | (from, to) <- Set.toList (transitions model), from == state]
            newVisited = Set.insert state visited
        in any (\s -> checkEFRecursive model formula s newVisited) successors

checkAU :: Model -> CTLFormula -> CTLFormula -> String -> Bool
checkAU model left right state = 
    checkAURecursive model left right state Set.empty

checkAURecursive :: Model -> CTLFormula -> CTLFormula -> String -> Set String -> Bool
checkAURecursive model left right state visited
    | Set.member state visited = False
    | checkCTL model right state = True
    | not (checkCTL model left state) = False
    | otherwise = 
        let successors = [to | (from, to) <- Set.toList (transitions model), from == state]
            newVisited = Set.insert state visited
        in all (\s -> checkAURecursive model left right s newVisited) successors

checkEU :: Model -> CTLFormula -> CTLFormula -> String -> Bool
checkEU model left right state = 
    checkEURecursive model left right state Set.empty

checkEURecursive :: Model -> CTLFormula -> CTLFormula -> String -> Set String -> Bool
checkEURecursive model left right state visited
    | Set.member state visited = False
    | checkCTL model right state = True
    | not (checkCTL model left state) = False
    | otherwise = 
        let successors = [to | (from, to) <- Set.toList (transitions model), from == state]
            newVisited = Set.insert state visited
        in any (\s -> checkEURecursive model left right s newVisited) successors
```

## Lean实现思路

```lean
import Lean.Data.HashMap
import Lean.Data.HashMap.Basic

-- LTL公式定义
inductive LTLFormula where
  | atom : String → LTLFormula
  | not : LTLFormula → LTLFormula
  | and : LTLFormula → LTLFormula → LTLFormula
  | or : LTLFormula → LTLFormula → LTLFormula
  | implies : LTLFormula → LTLFormula → LTLFormula
  | next : LTLFormula → LTLFormula
  | until : LTLFormula → LTLFormula → LTLFormula
  | globally : LTLFormula → LTLFormula
  | finally : LTLFormula → LTLFormula

-- CTL公式定义
inductive CTLFormula where
  | atom : String → CTLFormula
  | not : CTLFormula → CTLFormula
  | and : CTLFormula → CTLFormula → CTLFormula
  | or : CTLFormula → CTLFormula → CTLFormula
  | implies : CTLFormula → CTLFormula → CTLFormula
  | ax : CTLFormula → CTLFormula
  | ex : CTLFormula → CTLFormula
  | ag : CTLFormula → CTLFormula
  | eg : CTLFormula → CTLFormula
  | af : CTLFormula → CTLFormula
  | ef : CTLFormula → CTLFormula
  | au : CTLFormula → CTLFormula → CTLFormula
  | eu : CTLFormula → CTLFormula → CTLFormula

-- 模型定义
structure Model where
  states : List String
  transitions : List (String × String)
  labels : HashMap String (List String)

-- LTL模型检测
def checkLTL (model : Model) (formula : LTLFormula) (state : String) : Bool :=
  match formula with
  | LTLFormula.atom name => 
    match model.labels.find? state with
    | some labelList => labelList.contains name
    | none => false
  | LTLFormula.not f => not (checkLTL model f state)
  | LTLFormula.and left right => 
    checkLTL model left state && checkLTL model right state
  | LTLFormula.or left right => 
    checkLTL model left state || checkLTL model right state
  | LTLFormula.implies left right => 
    not (checkLTL model left state) || checkLTL model right state
  | LTLFormula.next f => checkNext model f state
  | LTLFormula.until left right => checkUntil model left right state
  | LTLFormula.globally f => checkGlobally model f state
  | LTLFormula.finally f => checkFinally model f state

def checkNext (model : Model) (formula : LTLFormula) (state : String) : Bool :=
  let successors := model.transitions.filter (fun (from, _) => from == state)
    |>.map (fun (_, to) => to)
  successors.all (fun s => checkLTL model formula s)

def checkUntil (model : Model) (left right : LTLFormula) (state : String) : Bool :=
  checkUntilRecursive model left right state []

def checkUntilRecursive (model : Model) (left right : LTLFormula) 
                       (state : String) (visited : List String) : Bool :=
  if visited.contains state then false
  else if checkLTL model right state then true
  else if not (checkLTL model left state) then false
  else
    let successors := model.transitions.filter (fun (from, _) => from == state)
      |>.map (fun (_, to) => to)
    let newVisited := state :: visited
    successors.any (fun s => checkUntilRecursive model left right s newVisited)

def checkGlobally (model : Model) (formula : LTLFormula) (state : String) : Bool :=
  checkGloballyRecursive model formula state []

def checkGloballyRecursive (model : Model) (formula : LTLFormula) 
                          (state : String) (visited : List String) : Bool :=
  if visited.contains state then true
  else if not (checkLTL model formula state) then false
  else
    let successors := model.transitions.filter (fun (from, _) => from == state)
      |>.map (fun (_, to) => to)
    let newVisited := state :: visited
    successors.all (fun s => checkGloballyRecursive model formula s newVisited)

def checkFinally (model : Model) (formula : LTLFormula) (state : String) : Bool :=
  checkFinallyRecursive model formula state []

def checkFinallyRecursive (model : Model) (formula : LTLFormula) 
                         (state : String) (visited : List String) : Bool :=
  if visited.contains state then false
  else if checkLTL model formula state then true
  else
    let successors := model.transitions.filter (fun (from, _) => from == state)
      |>.map (fun (_, to) => to)
    let newVisited := state :: visited
    successors.any (fun s => checkFinallyRecursive model formula s newVisited)

-- CTL模型检测
def checkCTL (model : Model) (formula : CTLFormula) (state : String) : Bool :=
  match formula with
  | CTLFormula.atom name => 
    match model.labels.find? state with
    | some labelList => labelList.contains name
    | none => false
  | CTLFormula.not f => not (checkCTL model f state)
  | CTLFormula.and left right => 
    checkCTL model left state && checkCTL model right state
  | CTLFormula.or left right => 
    checkCTL model left state || checkCTL model right state
  | CTLFormula.implies left right => 
    not (checkCTL model left state) || checkCTL model right state
  | CTLFormula.ax f => checkAX model f state
  | CTLFormula.ex f => checkEX model f state
  | CTLFormula.ag f => checkAG model f state
  | CTLFormula.eg f => checkEG model f state
  | CTLFormula.af f => checkAF model f state
  | CTLFormula.ef f => checkEF model f state
  | CTLFormula.au left right => checkAU model left right state
  | CTLFormula.eu left right => checkEU model left right state

def checkAX (model : Model) (formula : CTLFormula) (state : String) : Bool :=
  let successors := model.transitions.filter (fun (from, _) => from == state)
    |>.map (fun (_, to) => to)
  successors.all (fun s => checkCTL model formula s)

def checkEX (model : Model) (formula : CTLFormula) (state : String) : Bool :=
  let successors := model.transitions.filter (fun (from, _) => from == state)
    |>.map (fun (_, to) => to)
  successors.any (fun s => checkCTL model formula s)

def checkAG (model : Model) (formula : CTLFormula) (state : String) : Bool :=
  checkAGRecursive model formula state []

def checkAGRecursive (model : Model) (formula : CTLFormula) 
                    (state : String) (visited : List String) : Bool :=
  if visited.contains state then true
  else if not (checkCTL model formula state) then false
  else
    let successors := model.transitions.filter (fun (from, _) => from == state)
      |>.map (fun (_, to) => to)
    let newVisited := state :: visited
    successors.all (fun s => checkAGRecursive model formula s newVisited)

def checkEG (model : Model) (formula : CTLFormula) (state : String) : Bool :=
  checkEGRecursive model formula state []

def checkEGRecursive (model : Model) (formula : CTLFormula) 
                    (state : String) (visited : List String) : Bool :=
  if visited.contains state then true
  else if not (checkCTL model formula state) then false
  else
    let successors := model.transitions.filter (fun (from, _) => from == state)
      |>.map (fun (_, to) => to)
    let newVisited := state :: visited
    successors.any (fun s => checkEGRecursive model formula s newVisited)

def checkAF (model : Model) (formula : CTLFormula) (state : String) : Bool :=
  checkAFRecursive model formula state []

def checkAFRecursive (model : Model) (formula : CTLFormula) 
                    (state : String) (visited : List String) : Bool :=
  if visited.contains state then false
  else if checkCTL model formula state then true
  else
    let successors := model.transitions.filter (fun (from, _) => from == state)
      |>.map (fun (_, to) => to)
    let newVisited := state :: visited
    successors.all (fun s => checkAFRecursive model formula s newVisited)

def checkEF (model : Model) (formula : CTLFormula) (state : String) : Bool :=
  checkEFRecursive model formula state []

def checkEFRecursive (model : Model) (formula : CTLFormula) 
                    (state : String) (visited : List String) : Bool :=
  if visited.contains state then false
  else if checkCTL model formula state then true
  else
    let successors := model.transitions.filter (fun (from, _) => from == state)
      |>.map (fun (_, to) => to)
    let newVisited := state :: visited
    successors.any (fun s => checkEFRecursive model formula s newVisited)

def checkAU (model : Model) (left right : CTLFormula) (state : String) : Bool :=
  checkAURecursive model left right state []

def checkAURecursive (model : Model) (left right : CTLFormula) 
                    (state : String) (visited : List String) : Bool :=
  if visited.contains state then false
  else if checkCTL model right state then true
  else if not (checkCTL model left state) then false
  else
    let successors := model.transitions.filter (fun (from, _) => from == state)
      |>.map (fun (_, to) => to)
    let newVisited := state :: visited
    successors.all (fun s => checkAURecursive model left right s newVisited)

def checkEU (model : Model) (left right : CTLFormula) (state : String) : Bool :=
  checkEURecursive model left right state []

def checkEURecursive (model : Model) (left right : CTLFormula) 
                    (state : String) (visited : List String) : Bool :=
  if visited.contains state then false
  else if checkCTL model right state then true
  else if not (checkCTL model left state) then false
  else
    let successors := model.transitions.filter (fun (from, _) => from == state)
      |>.map (fun (_, to) => to)
    let newVisited := state :: visited
    successors.any (fun s => checkEURecursive model left right s newVisited)
```

## 应用场景

### 1. 硬件验证

- **电路验证**: 验证数字电路的正确性
- **协议验证**: 验证通信协议的安全性
- **时序性质**: 验证实时系统的时序约束

### 2. 软件验证

- **程序正确性**: 验证程序满足规约
- **并发系统**: 验证多线程程序的正确性
- **安全性质**: 验证系统的安全属性

### 3. 系统建模

- **状态机建模**: 将系统建模为状态转换图
- **性质规约**: 用时序逻辑描述系统性质
- **模型检测**: 自动验证系统模型

### 4. 人工智能

- **规划问题**: 验证智能体的行为规划
- **多智能体系统**: 验证协作行为
- **知识表示**: 用逻辑表示时间相关知识

## 最佳实践

### 1. 公式设计

- 使用简洁的公式表达性质
- 避免复杂的嵌套结构
- 考虑公式的可读性

### 2. 模型构建

- 准确建模系统行为
- 考虑所有相关状态
- 验证模型的正确性

### 3. 检测策略

- 选择合适的检测算法
- 处理状态空间爆炸
- 优化检测性能

### 4. 结果解释

- 理解检测结果含义
- 分析反例和证据
- 指导系统改进

## 性能考虑

### 1. 状态空间

- 状态数量增长
- 转换关系复杂度
- 内存使用优化

### 2. 检测算法

- 算法复杂度分析
- 并行化处理
- 启发式优化

### 3. 可扩展性

- 大规模系统建模
- 分布式检测
- 增量验证

## 总结

时序逻辑为系统验证提供了强大的形式化工具。通过深入理解LTL、CTL等时序逻辑的语法和语义，可以准确描述和验证系统的时间相关性质，为硬件和软件系统的正确性提供理论保证。
