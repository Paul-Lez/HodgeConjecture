import Lake

open Lake DSL

package HodgeKirovCompat where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

lean_lib KirovDolbeault where
  srcDir := ".research_jacobian/vendor/kirov-dolbeault-port"
  roots := #[`KirovDolbeault.Dolbeault.SerreResidueRamifiedRealSlitGeometry]
