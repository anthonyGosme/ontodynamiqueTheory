import Lake
open Lake DSL

package «monProjetLean» where
  name := "monProjetLean"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"

lean_lib «MonProjetLean» where
