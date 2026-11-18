
# Oat Compiler

A compiler for the C-like **Oat programming language**, developed in OCaml as part of the Compiler Design course at ETH Zürich.

This project was developed jointly by two students and covers compiler construction from lexical analysis to x86-64 code generation, including register allocation and optimizations.

## Features

- Lexical analysis and parsing
- Static type checking
- Translation to LLVMlite intermediate representation
- x86-64 assembly code generation
- Liveness analysis
- Graph-coloring register allocation
- Register spilling
- Alias analysis
- Constant propagation
- Dead-code elimination

## Compiler Architecture

```text
Oat Source Code (.oat)
        |
        v
   Lexer / Parser
        |
        v
  Abstract Syntax Tree
        |
        v
    Type Checker
        |
        v
 LLVMlite IR Generation
        |
        v
    Optimizations
        |
        v
    Liveness Analysis
        |
        v
  Register Allocation
        |
        v
 x86-64 Code Generation
        |
        v
   x86-64 Assembly
```

## Repository Structure

- `compiler/` - Final HW6 compiler project
- `original-submissions/` - Submitted source code from HW1–HW6
- `examples/` - Example Oat programs

The coursework was completed incrementally. Later assignments included updated course infrastructure and potentially reference implementations of earlier components. The original submissions are preserved separately to document the work submitted by the team.

## Building

The compiler uses OCaml and the original course Makefile.

Requirements include:
- OCaml
- ocamlbuild
- Menhir
- num OCaml package
- Make
- Clang

Build the compiler:

```bash
cd compiler
make
```

## Running Tests

On Linux:

```bash
./main.native -linux --test
```

On macOS:

```bash
./main.native --test
```

## Example

Compile and execute an Oat program on Linux:

```bash
./main.native -linux --execute-x86 \
  ../examples/return_17.oat
```

Use dataflow liveness analysis, graph-coloring
register allocation, and optimizations:

```bash
./main.native -linux \
  --liveness dataflow \
  --regalloc better \
  -O1 \
  --execute-x86 ../examples/return_17.oat
```

The build and examples still require verification in a supported OCaml environment.

## Limitations

This project targets the educational Oat language, not the complete C language.

LLVMlite is a simplified LLVM-like intermediate representation.

## Authors

Developed jointly by:
- Jan Häussermann
- Konstantin Lucny

As part of the Compiler Design course at ETH Zürich.

Some infrastructure, libraries, tests, and reference implementations were provided by the course and are not original student work.

