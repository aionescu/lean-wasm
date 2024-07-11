# lean-wasm

An intrinsically-typed WebAssembly interpreter written in Lean 4.

## Requirements

* `lean` >= 4.9.0
* `lake` >= 5.0.0

Both can be installed via [elan](https://github.com/leanprover/elan), the Lean toolchain manager.

## Building the code

```sh
lake build
```

## Running the examples

```sh
lake exe lean-wasm
```
