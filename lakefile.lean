import Lake
open Lake DSL

package «lean-wasm» where
  srcDir := "src"
  -- add package configuration options here

lean_lib «LeanWasm» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-wasm» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
