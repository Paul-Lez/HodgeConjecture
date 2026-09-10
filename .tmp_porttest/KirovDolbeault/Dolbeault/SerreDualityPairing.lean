/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreDuality
import KirovDolbeault.Dolbeault.CohomologicalRR
import KirovDolbeault.LinearSystem
import KirovDolbeault.Genus
import KirovDolbeault.Dolbeault.CanonicalFormIso

/-!
# Serre duality on `X` — the direct Forster §17 route (the plan of record)

This is the **direct** route to `arithmeticGenus_eq_genus` and `serre_h1_eq`, following Forster
*Lectures on Riemann Surfaces* §17 (Serre Duality Theorem) verbatim — **no Dolbeault comparison and no
Hodge symmetry**. Forster §17 is entirely PDE-free (harmonic forms first appear in §19, which §16–17
never use); it proves, for the **canonical divisor** `K`, the perfect residue pairing

  `⟨ω, ξ⟩ := Res(ω·ξ)`,   `ι_D : H⁰(X, Ω_{−D}) → H¹(X, 𝒪_D)*`

is an isomorphism (Forster 17.6 injective + 17.9 surjective), whence (17.10/17.11)

  `dim H¹(X, 𝒪_D) = dim H⁰(X, Ω_{−D})`,  and at `D = 0`:  `g = dim H¹(X,𝒪) = dim H⁰(X,Ω)`.

Using Forster 17.4 (`Ω_{−D} ≅ 𝒪_{K−D}` via multiplication by a meromorphic 1-form with divisor `K`),
we phrase the pairing on the **already-built junk-free linear system** `L(K−D)` (`lDim (K−D)`), so we do
**not** need a separate meromorphic-1-form space:

  `ι_D : lSysModule (K − D) → (𝔘.cechH1 D)*`,   bijective ⟹  `h1Dim D = lDim (K − D)`  (= `serre_h1_eq`).

## What is proved here (complete, downstream of the bundled `SerreDualityData`)

The abstract finite-dimensional cores are already proven in `SerreDuality.lean`:
`finrank_le_of_injective_to_dual` (17.6) and `serre_surjectivity_dim_core` (17.9). This file bundles the
**geometric instantiation** of §17 into one honest, non-vacuous structure `SerreDualityData 𝔘` (the
canonical `K`, the residue pairing, its injectivity and surjectivity, and the finiteness of `H¹`), and
**derives** `serre_eq` (17.11), `serre_h1_eq`, and `arithmeticGenus_eq_genus` from it. The `≤` half wires
`finrank_le_of_injective_to_dual` directly; the `≥` half uses the bundled surjectivity (whose eventual
construction runs `serre_surjectivity_dim_core` on the §17.9 dimension count).

## The keystone (CLOSED by the flip)

The §17 instantiation, formerly the ∀-cover sorry `exists_serreDualityData` here, is now
PROVEN in its honest ∃-cover form `exists_serreDualityData_cover`
(`KeystonePackaging.lean`): the T-lane frame-trace construction
(`FrameTrace.exists_canonicalData_residueAtom`) through the #194 genus split and the
#193 capstone. See the note at the end of this file.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.4–17.11; Miranda, *Algebraic Curves and
Riemann Surfaces*, §VIII.3.
-/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The Forster §17 instantiation** (the geometric data of Serre duality on `X`): a canonical divisor
`K` with `lDim K = kirovGenus` (17.4 at `D=0`: `𝒪_K ≅ Ω`), and the residue pairing
`ι_D : L(K−D) → (H¹(𝒪_D))*` which is bijective (17.6 injective + 17.9 surjective), with `H¹` finite. -/
structure SerreDualityData (𝔘 : FiniteCover X) where
  /-- The canonical divisor `K = div ω₀` of a nonzero meromorphic 1-form. -/
  K : Divisor X
  /-- 17.4 at `D=0`: `𝒪_K ≅ Ω` gives `lDim K = dim H⁰(Ω) = kirovGenus`. -/
  hKgenus : lDim (X := X) K = kirovGenus X
  /-- The residue pairing `ι_D : L(K−D) → (H¹(𝒪_D))*`, `⟨f,ξ⟩ = Res((f·ω₀)·ξ)` (Forster 17.5). -/
  ι : ∀ D : Divisor X, lSysModule (K - D) →ₗ[ℂ] Module.Dual ℂ (𝔘.cechH1 D)
  /-- **17.6 — injectivity** (the residue-1 witness). -/
  ι_inj : ∀ D : Divisor X, Function.Injective (ι D)
  /-- **17.9 — surjectivity** (the dimension count via `serre_surjectivity_dim_core`). -/
  ι_surj : ∀ D : Divisor X, Function.Surjective (ι D)
  /-- `H¹(X, 𝒪_D)` is finite-dimensional (Forster §14 finiteness). -/
  finH1 : ∀ D : Divisor X, FiniteDimensional ℂ (𝔘.cechH1 D)

namespace SerreDualityData

variable {𝔘 : FiniteCover X}

/-- **Forster 17.11 — the Serre duality dimension equality.** `dim H¹(X,𝒪_D) = dim H⁰(X,𝒪_{K−D})`,
i.e. `h1Dim D = lDim (K − D)`. The pairing `ι_D` is bijective, so `L(K−D) ≃ (H¹(𝒪_D))*`, and the dual
of a finite-dimensional space has equal dimension. -/
theorem serre_eq (data : SerreDualityData 𝔘) (D : Divisor X) :
    𝔘.h1Dim D = lDim (X := X) (data.K - D) := by
  haveI := data.finH1 D
  -- `ι_D` is a linear equivalence `L(K−D) ≃ (H¹(𝒪_D))*`.
  let e : lSysModule (data.K - D) ≃ₗ[ℂ] Module.Dual ℂ (𝔘.cechH1 D) :=
    LinearEquiv.ofBijective (data.ι D) ⟨data.ι_inj D, data.ι_surj D⟩
  -- `finrank H¹(𝒪_D) = finrank (H¹(𝒪_D))* = finrank L(K−D)`.
  have h : finrank ℂ (𝔘.cechH1 D) = finrank ℂ (lSysModule (data.K - D)) := by
    rw [← Subspace.dual_finrank_eq (K := ℂ) (V := 𝔘.cechH1 D), ← e.finrank_eq]
  -- `h1Dim D = finrank H¹(𝒪_D)`, `lDim (K−D) = finrank L(K−D)` (both definitional).
  exact h

/-- **The `≤` half wired through the 17.6 core** (`finrank_le_of_injective_to_dual`): injectivity of the
pairing gives `lDim (K−D) ≤ h1Dim D`. (Recorded separately to exhibit the core wiring; subsumed by
`serre_eq`.) -/
theorem lDim_le_h1Dim (data : SerreDualityData 𝔘) (D : Divisor X) :
    lDim (X := X) (data.K - D) ≤ 𝔘.h1Dim D := by
  haveI := data.finH1 D
  exact SerreDuality.finrank_le_of_injective_to_dual (data.ι D) (data.ι_inj D)

/-- **Forster 17.10 at `D = 0` — `arithmeticGenus_eq_genus`.** `h1Dim 0 = kirovGenus X`. -/
theorem arithmeticGenus (data : SerreDualityData 𝔘) : 𝔘.h1Dim 0 = kirovGenus X := by
  rw [data.serre_eq 0, sub_zero]; exact data.hKgenus

/-- **General Serre duality `serre_h1_eq`** from the data: a single canonical `K` works for all `D`. -/
theorem serreH1 (data : SerreDualityData 𝔘) :
    ∃ K : Divisor X, ∀ D : Divisor X, 𝔘.h1Dim D = lDim (X := X) (K - D) :=
  ⟨data.K, data.serre_eq⟩

end SerreDualityData

/-! The former ∀-cover keystone sorry `exists_serreDualityData` (and its two `_serre`
wrappers `arithmeticGenus_eq_genus_serre` / `serre_h1_eq_serre`) lived here. The keystone
flip replaced it by the honest **∃-cover form**, PROVEN unconditionally in
`KeystonePackaging.lean` (`exists_serreDualityData_cover`): the T-lane frame-trace
construction (`FrameTrace.exists_canonicalData_residueAtom`) fed through the #194 genus
split and the #193 capstone. The sole top-level consumer
(`RiemannRoch.exists_riemannRoch_divisor`) now takes the cover EXHIBITED by the keystone
(`DolbeaultLadder.riemannRoch_equality_of_data`); see `docs/planning/FLIP_CHECKLIST.md`. -/

end Jacobians.Dolbeault

end
