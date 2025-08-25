import Lake
open Lake DSL

package «hyperlocal» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.9.1"

@[default_target]
lean_lib «Hyperlocal» where
  -- add library configuration options here
