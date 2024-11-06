import Lake
open Lake DSL

package "refts" where
  version := v!"0.1.0"

lean_lib «Refts» where
  -- add library configuration options here

@[default_target]
lean_exe "refts" where
  root := `Main
