# Fundamentals-of-Compiler-Configuration

Repository for assignments and projects from the Fundamentals of Compiler Configuration course.

## Overview

This repository contains projects that implement core compiler components step by step:
- **Type Checking** (Semantic Analysis)
- **IR Generation** (Intermediate Representation Generation)
- **Optimization**

---

## Prj1: Type Checker

A static type checker for a C-style language implemented in F#.

### Supported Types
| Type | Description |
|------|-------------|
| `int` | Integer |
| `bool` | Boolean |
| `int*` | Integer pointer |
| `bool*` | Boolean pointer |

### Supported Expressions
- **Literals**: `NULL`, numbers, `true`/`false`
- **Variables**: variable reference, dereference (`*x`), address-of (`&x`)
- **Arithmetic operations**: `+`, `-`, `*`, `/`, unary `-`
- **Comparison operations**: `==`, `!=`, `<=`, `<`, `>=`, `>`
- **Logical operations**: `&&`, `||`, `!`

### Supported Statements
- **Declaration/Definition**: `int x;`, `int x = 0;`
- **Assignment**: `x = 10;`, `*x = 10;`
- **Control flow**: `if-else`, `while`
- **Return**: `return`

### Implementation Details
- Uses symbol table (`Map<Identifier, CType>`) for variable type management
- Applies type rules for each expression and statement
- Returns line numbers where semantic errors occur

### How to Run
```bash
cd Prj1
dotnet build
dotnet run <program_file>
python3 check.py  # Validate test cases
```

---

## Prj2: IR Generator

A project that translates AST into 3-address code IR (Intermediate Representation).

### Additional Type Support
| Type | Description |
|------|-------------|
| `int[N]` | Integer array |
| `bool[N]` | Boolean array |

### IR Instructions
| Instruction | Description | Example |
|-------------|-------------|---------|
| `Set` | Set value to register | `r = 10` |
| `LocalAlloc` | Allocate stack memory | `r = alloc(4)` |
| `UnOp` | Unary operation | `r = -a` |
| `BinOp` | Binary operation | `r = a + b` |
| `Load` | Load from memory | `r1 = load r2` |
| `Store` | Store to memory | `store a, r` |
| `Goto` | Unconditional jump | `goto L1` |
| `GotoIf` | Conditional jump (true) | `if a then goto L1` |
| `GotoIfNot` | Conditional jump (false) | `ifnot a then goto L1` |
| `Label` | Label definition | `label L1` |
| `Ret` | Return | `ret a` |

### Translation Rules
- **Variables**: Store address register in symbol table, access via `Load`/`Store`
- **Arrays**: Calculate offset as index × element size
- **Short-circuit evaluation**: Use conditional jumps for `&&`, `||` operations
- **Control flow**: Transform `if`/`while` into labels and jumps

### How to Run
```bash
cd Prj2
dotnet build
dotnet run <program_file> <input_file>
python3 check.py  # Validate test cases
```

---

## Prj3: IR Optimizer

A project that performs various optimizations based on Data Flow Analysis (DFA).

### Data Flow Analysis (DFA)

#### 1. Reaching Definition Analysis
- **Direction**: Forward
- **Meet operator**: Union (∪)
- **Transfer function**: `RD_out[n] = GEN[n] ∪ (RD_in[n] - KILL[n])`
- **Usage**: Constant Propagation

#### 2. Available Expression Analysis
- **Direction**: Forward
- **Meet operator**: Intersection (∩)
- **Transfer function**: `AE_out[n] = GEN[n] ∪ (AE_in[n] - KILL[n])`
- **Usage**: CSE, Copy Propagation

#### 3. Liveness Analysis
- **Direction**: Backward
- **Meet operator**: Union (∪)
- **Transfer function**: `LA_in[n] = USE[n] ∪ (LA_out[n] - DEF[n])`
- **Usage**: Dead Code Elimination

### Implemented Optimization Techniques

| Optimization | Description | Example |
|--------------|-------------|---------|
| **Constant Folding** | Evaluate constants at compile time | `3 + 5` → `8` |
| **Constant Propagation** | Propagate constant values to use sites | `x = 5; y = x` → `y = 5` |
| **Copy Propagation** | Replace copied values with originals | `y = x; z = y` → `z = x` |
| **CSE** | Common Subexpression Elimination | Reuse `a+b` if computed twice |
| **Dead Code Elimination** | Remove unused code | Remove operations whose results are unused |
| **Mem2Reg** | Promote memory accesses to registers | Eliminate `Load`/`Store` |

### CFG (Control Flow Graph)
- Nodes: IR instructions
- Edges: Control flow (sequential, jump, conditional jump)
- Composed of `InstrMap`, `SuccMap`, `PredMap`

### How to Run
```bash
cd Prj3
dotnet build
dotnet run <program_file> <input_file>
python3 check.py  # Validate test cases
```

---

## Project Structure

```
├── Prj1/                    # Type Checker
│   └── src/
│       ├── AST.fs           # AST definition
│       ├── TypeCheck.fs     # Type checking logic
│       ├── Parser.fsy       # Parser definition
│       └── Lexer.fsl        # Lexer definition
│
├── Prj2/                    # IR Generator
│   └── src/
│       ├── AST.fs           # Extended AST (array support)
│       ├── IR.fs            # IR instruction definition
│       ├── Translate.fs     # AST → IR translation
│       └── Executor.fs      # IR interpreter
│
├── Prj3/                    # IR Optimizer
│   └── src/
│       ├── CFG.fs           # Control Flow Graph
│       ├── DFA.fs           # Data Flow Analysis
│       └── Optimize.fs      # Optimization passes
│
├── HW1/                     # Homework 1 (Lex/Yacc)
└── HW2/                     # Homework 2 (F# Practice)
```

---

## Tech Stack

- **Language**: F# (.NET)
- **Parser Generator**: FsLexYacc
- **Build Tool**: dotnet CLI

---

## References

- Dragon Book (Compilers: Principles, Techniques, and Tools)
- [F# Documentation](https://docs.microsoft.com/en-us/dotnet/fsharp/)
- [FsLexYacc](https://fsprojects.github.io/FsLexYacc/)