import Lake
open Lake DSL

package «formalization» where
  -- Settings applied to both builds and targets
  leanOptions := #[
    ⟨`autoImplicit, false⟩ -- Keeps code strict and well-structured
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.15.0"

@[default_target]
lean_lib «Formalization» where
  -- Your formalization files will live inside a folder named 'Formalization'
