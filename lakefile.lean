import Lake
open Lake DSL

package «imo-test» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «ImoTest» where
  srcDir := "."
