import Lake
open Lake DSL

package «Lean4IntN» where
  -- add package configuration options here

lean_lib «Lean4IntN» where
  -- add library configuration options here

@[default_target]
lean_exe «lean4intn» where
  root := `Main
