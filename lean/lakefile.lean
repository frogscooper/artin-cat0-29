import Lake
open Lake DSL
package ArtinSlim where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
@[default_target] lean_lib OAI where
  globs := #[.andSubmodules `OAI.GroupTheory.ArtinCAT0]
lean_lib ComparatorChallenges where
  globs := #[.one `ComparatorChallenges.ArtinCAT0]
