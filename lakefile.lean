import Lake
open Lake DSL

package hyperlocal where
  -- Put all Lean sources under `formalisation/`
  srcDir := "formalisation"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0-rc2"

@[default_target]
lean_lib «Hyperlocal» where
  -- add library configuration options here
