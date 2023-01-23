# Typechecker $ LLVM compiler

## Prerequisites

 * Haskell Stack
 * LLVM
 * BNFC
 * Happy
 * Alex

## Make:
```
make
```

## Run

Typechecker  
```
./latc [-v] <file [files...]>

```

Compiler
```
./latc_llvm [-v] <file [files...]>
```

## What has been done
 
 * Basic Latte typechecker and LLVM compiler 
 * Using PHI nodes instead of `alloca` and `store`
 * Copy Propagation and Constant Folding
 * Dead Code Elimination
 * Global Common Subexpression Elimination
 * Extensions:
    * Classes with virtual methods

Important note: Even though the typechecker is able to validate arrays, the compiler does not support them.
It informs the user with an error message.

## Source structure

 * src/
    * Latte.cf - Grammar
    * Forontend/
        * Desugaring.hs - Desugaring of the AST, mainly transforming `for` loops into `while` loops and 
        incrementation and decrementation of variables into simple arithmetic.
        * Typechecker.hs - Typechecking of the AST.
    * Backend/
        * Milkremover.hs - Transforms Latte into Espresso IR
        * SingleShotAffogato.hs - Transform Espresso IR into SSA form and performs (CP, DCE, GCSE) loop until a fixpoint is reached.
        * ArabicaGenearator.hs - Generates LLVM IR from Espresso IR, assuming it is in SSA form. 
        Here is where the main vritual methods are implemented.
        * ASTInterpreter.hs - An early version of Espresso IR interpreter, used for debugging.
 * tests/ - Tests for the typechecker and the compiler (tests/extensions/arrays1 are irrelevant)
 * lib/ - Latte standard library with addition of `concatStrings`, `compareStrings` and `__calloc__`

## Verbose output

 * .desugared - Latte program after desugaring
 * .esp - Espresso IR
 * .esp.ssa - Espresso IR in SSA form after optimizations
 * .ll - LLVM IR
 * .bc - LLVM Bitcode