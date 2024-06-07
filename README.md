# About
BRAT is a functional programming language designed for writing quantum experiments. For an introduction to BRAT, see the [extended abstract](papers/planqc-2024/brat-planqc.pdf) submitted to PLanQC 2024.

# Installation
To build BRAT from source, you will need:
- GHC 9.6.4 (can be installed with the `ghcup` tool)
- The `stack` build tool for Haskell

Then, navigate to the `src` directory and run `stack install`.

This will add the `brat` and `brat-lsp` binaries  to `~/.local/bin`, and copy configuration for the emacs editor mode to `~/.local/share/brat/`.

There is also a plugin for the VS Code editor. To install this, look at `vscode/README.md`.

# Usage
### Typechecking
By default, the installed `brat` executable  will typecheck a program given as an argument, e.g.:
```sh
brat my-program.brat
```
which, if `my-program` typechecks, will print out the parsed versions of the declarations and a list of remaining holes.

### Compiling
The `--compile` flag can be used to compile the BRAT program to the [hugr](https://github.com/CQCL/hugr) IR and print the JSON representation to the command line.

### Validating
There is a tool in the root of the repository called `hugr_validator` (install by `cd hugr_validator && cargo install --path .`) which is used to check that the JSON output from BRAT constitutes a valid hugr. This is invoked by:
```sh
brat --compile my-program.brat | hugr_validator
```

# Reference
The [`src/examples`](src/examples) directory contains some examples of BRAT programs.
For example:
- Quantum teleportation: [teleportation.brat](src/examples/teleportation.brat)
- Quantum Fourier transform: [teleportation.brat](src/examples/teleportation.brat)
- Simple Repeat-Until-Success: [rus.brat](src/examples/rus.brat)
- Ising Hamiltonian: [ising.brat](src/examples/ising.brat)

This directory also contains tests of syntax features which, while terse, may serve as a reference in the short term.
For example:
- [unified.brat](src/examples/unified.brat) contains some functional programs
- [dollar_kind.brat](src/examples/dollar_kind.brat) tests polymorphism over kernel types
- [tups.brat](src/examples/tups.brat) tests heterogenous lists
- [compjuxt.brat](src/examples/compjuxt.brat), `src/examples/composition.brat` contain tests for diagrammatic syntax
- [pass.brat](src/examples/pass.brat) tests the 'passthrough' (`..`) operator
- [portpulling.brat](src/examples/portpulling.brat) demonstrates port pulling
