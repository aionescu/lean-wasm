import LeanWasm.Examples

open HList.Notation

def main (_args : List String) : IO Unit := do
  print_example "unreachable" unreachable ([].)
  print_example "simple_add" simple_add ([].)
  print_example "locals_simple" locals_simple ([].)
  print_example "factorial" factorial (5 :. [].)
  print_example "memory_simple" memory_simple ([].)
  print_example "memory_trap" memory_trap ([].)
