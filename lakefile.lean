import Lake
open Lake DSL

package «hyperlocal» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Hyperlocal» where
  -- add library configuration options here
