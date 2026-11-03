import Lake
open Lake Study

package «formalization» where
  -- Settings applied to both builds and targets
  leanOptions := #[
    ⟨`autoImplicit, false⟩ -- Keeps code strict and well-structured
  ]

require mathlib from git
  "https://github.com"

@[default_target]
lean_lib «Formalization» where
  -- Your formalization files will live inside a folder named 'Formalization'
