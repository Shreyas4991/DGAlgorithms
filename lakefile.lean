import Lake
open Lake DSL

package «DGAlgorithms» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "stable"

@[default_target]
lean_lib «DGAlgorithms» where
  -- add any library configuration options here
