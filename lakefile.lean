import Lake
open Lake DSL

require aesop from git
  "https://github.com/leanprover-community/aesop.git" @ "v4.14.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

package Example

@[default_target]
lean_lib Example
