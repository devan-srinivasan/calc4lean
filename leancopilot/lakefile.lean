import Lake
open Lake DSL

package «calc4lean» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.6.0"

@[default_target]
lean_lib «Calc4lean» where
  -- add any library configuration options here
