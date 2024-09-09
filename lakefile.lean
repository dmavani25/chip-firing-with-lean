import Lake
open Lake DSL

package "chip-firing-with-lean" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require "leanprover-community" / "mathlib"
require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"

@[default_target]
lean_lib «ChipFiringWithLean» where
  -- add any library configuration options here
