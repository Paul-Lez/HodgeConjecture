import Lake

open Lake DSL

package kirovCompat

require mathlib from "../../.lake/packages/mathlib"

lean_lib KirovDolbeault where
  globs := #[.andSubmodules `KirovDolbeault]
