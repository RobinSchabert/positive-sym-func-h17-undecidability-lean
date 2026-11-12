import Lake
open Lake DSL

package anydim where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- Mathlib is pinned to a commit that is compatible with the toolchain in `lean-toolchain`.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "6036e0e71f6aa8440c202943b86f1540d75f67d2"

@[default_target]
lean_lib AnyDim where
  roots := #[`AnyDim]
