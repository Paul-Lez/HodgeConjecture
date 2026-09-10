/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreCupProduct
import KirovDolbeault.Dolbeault.SerreResiduePairing

/-!
# Forster §17.5/17.6 — assembling `SerreResidueRealization` from the cup product + global residue

This file **assembles** the make-or-break Forster §17.5 residue pairing
`ι_D : L(K−D) → (H¹(𝒪_D))*`, `⟨f, ξ⟩ = Res((f·ω₀)·ξ)`, and the §17.6 non-degeneracy `dz/z` witness,
into a `SerreResidueRealization 𝔘 K` (the structure `SerreResiduePairing.lean` derives
`pairing_injective` / `lDim_le_h1Dim` / `toSerreDualityData` from).

The pairing factors through the Forster §17.4 isomorphism `ω₀· : 𝒪_K ≅ Ω`
(`Jacobians.Dolbeault.CanonicalFormIso`), under which `H¹(X,Ω) ≅ 𝔘.cechH1 K` and the product
`(f·ω₀)·ξ ↦ f·ξ` becomes the **cup product** `cup 𝔘 D K : lSysModule (K−D) →ₗ (cechH1 D →ₗ cechH1 K)`
already built complete (`SerreCupProduct.lean`).  What remains is the global residue functional
`Res : H¹(X,Ω) ≅ cechH1 K → ℂ` (Forster 17.2–17.3, the Mittag–Leffler **connecting map** of a Čech
class to a distribution of 1-forms, whose total residue is well-defined by the 1-form residue theorem
`∑Res = 0` — the genuinely-greenfield analytic descent).  We isolate exactly that residue functional
plus its §17.6 non-degeneracy into one named structure `GlobalResidue 𝔘 K`, and **derive** the full
`SerreResidueRealization` from it together with the proven cup product.

## What is proved here (complete, axiom-clean) — the reduction

* `GlobalResidue.toSerreResidueRealization` — from a `GlobalResidue 𝔘 K` (the residue functional +
  non-degeneracy), the §17.5 pairing `pairing D := res ∘ cup` and the §17.6 witness are **derived**,
  giving a `SerreResidueRealization 𝔘 K`.  Hence (`SerreResiduePairing.lean`) `pairing_injective`,
  `lDim_le_h1Dim`, and the bridge to `SerreDualityData` all follow.

The cup product is PROVEN; only the global residue functional + its non-degeneracy (the connecting-map
analysis) is the remaining named input, isolating the Serre wall to its smallest honest residual.

## Soundness

`GlobalResidue` is **sound and non-circular**: `res` is an honest ℂ-linear functional (not a junk zero
map — its non-degeneracy field forces `res (cup f ξ) = 1 ≠ 0` for every nonzero `[f]`, the genuine
`dz/z` residue-1 datum of Forster §17.6, `exists_formFnResidue_eq_one_of_localRep_ne_zero`); the source
`lSysModule (K−D)` is the junk-free germ quotient (no `lDim ≡ 0` collapse); and it does **not** route
through Riemann–Roch (RR depends on this).  The well-definedness of `res` on classes genuinely consumes
the 1-form residue theorem `∑Res = 0` (Part 1 of `SerreResiduePairing.lean`,
`res_eq_of_globalMeromorphic_diff`), which is what the connecting-map realization must supply.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.2–17.6.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Module

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **[ISOLATED INPUT — the global residue functional on `H¹(X,Ω) ≅ cechH1 K`].**  The remaining
Forster §17.2–17.3 datum after the cup product (`SerreCupProduct.lean`) is built: the **global residue
functional** `res : 𝔘.cechH1 K →ₗ[ℂ] ℂ` on `H¹(X,Ω)` (identified with `𝔘.cechH1 K` via the §17.4
isomorphism `ω₀· : 𝒪_K ≅ Ω`), together with the §17.6 **non-degeneracy** witness for the residue
pairing `⟨f, ξ⟩ = res (cup f ξ)`.

`res` is the Mittag–Leffler realization of a Čech class as a distribution of 1-forms followed by its
total residue (the connecting map of Forster 17.2 + `Res` of 17.3); it is **well-defined** on
cohomology classes precisely by the 1-form residue theorem `∑Res = 0` (Part 1 of
`SerreResiduePairing.lean`).  Building `res` (the connecting map) is the genuinely-greenfield analytic
descent that remains; it is isolated here as the single named field.

The `nondegenerate` field is the genuine §17.6 `dz/z` non-degeneracy: it forces `res (cup f ξ) = 1`
for a suitable class `ξ` whenever `[f] ≠ 0`, so the derived pairing is *not* a junk zero map (the
`dz/z` residue-1 datum, `exists_formFnResidue_eq_one_of_localRep_ne_zero`, pushed through cup+res). -/
structure GlobalResidue (𝔘 : FiniteCover X) (K : Divisor X) where
  /-- The global residue functional `Res : H¹(X,Ω) ≅ 𝔘.cechH1 K → ℂ` (Forster 17.2–17.3, the
  Mittag–Leffler realization of a Čech class + its total residue, well-defined by `∑Res = 0`). -/
  res : 𝔘.toFiniteFamily.cechH1 K →ₗ[ℂ] ℂ
  /-- **§17.6 non-degeneracy (the `dz/z` witness).**  For every nonzero class `0 ≠ [f] ∈ L(K−D)` there
  is a class `ξ ∈ H¹(𝒪_D)` whose cup-then-residue is `1`:  `res (cup f ξ) = 1`.  This forces the
  derived pairing `⟨f, ξ⟩ = res (cup f ξ)` to be non-degenerate (Forster §17.6's residue-1 witness). -/
  nondegenerate : ∀ (D : Divisor X) (v : lSysModule (K - D)), v ≠ 0 →
    ∃ ξ : 𝔘.toFiniteFamily.cechH1 D, res (cup (𝔘 := 𝔘.toFiniteFamily) D K v ξ) = 1

namespace GlobalResidue

variable {𝔘 : FiniteCover X} {K : Divisor X}

/-- The **§17.5 residue pairing** `ι_D : L(K−D) → (H¹(𝒪_D))*`, `⟨f, ξ⟩ = res (cup f ξ)`, as an
ℂ-linear map into the dual: post-compose the cup product `cup f : H¹(𝒪_D) → H¹(𝒪_K)` (which is itself
ℂ-linear in `f`) with the global residue functional `res`.  This is `Res ∘ cup`, the Forster §17.5
pairing after the §17.4 reduction. -/
def pairing (R : GlobalResidue 𝔘 K) (D : Divisor X) :
    lSysModule (K - D) →ₗ[ℂ] Module.Dual ℂ (𝔘.toFiniteFamily.cechH1 D) :=
  -- `f ↦ (ξ ↦ res (cup f ξ))`: compose the residue functional with the cup `cup f`, both linear.
  (LinearMap.llcomp ℂ (𝔘.toFiniteFamily.cechH1 D) (𝔘.toFiniteFamily.cechH1 K) ℂ R.res) ∘ₗ
    (cup (𝔘 := 𝔘.toFiniteFamily) D K)

@[simp] theorem pairing_apply (R : GlobalResidue 𝔘 K) (D : Divisor X) (v : lSysModule (K - D))
    (ξ : 𝔘.toFiniteFamily.cechH1 D) :
    (R.pairing D v) ξ = R.res (cup (𝔘 := 𝔘.toFiniteFamily) D K v ξ) :=
  rfl

/-- **The assembled `SerreResidueRealization`** (Forster §17.5 pairing + §17.6 witness).  From a
`GlobalResidue 𝔘 K` (the global residue functional + non-degeneracy) and the proven cup product, the
residue realization is assembled: the pairing is `res ∘ cup` (ℂ-linear), and the §17.6 witness is the
non-degeneracy field.  Feeding this to `SerreResiduePairing.lean` gives `pairing_injective`,
`lDim_le_h1Dim`, and `toSerreDualityData`. -/
def toSerreResidueRealization (R : GlobalResidue 𝔘 K) :
    SerreResidueRealization 𝔘 K where
  pairing := R.pairing
  witness := fun D v hv => by
    obtain ⟨ξ, hξ⟩ := R.nondegenerate D v hv
    exact ⟨ξ, by rw [R.pairing_apply]; exact hξ⟩

/-- **§17.6 injectivity of the residue pairing** (the EASY half), via the assembled realization. -/
theorem pairing_injective (R : GlobalResidue 𝔘 K) (D : Divisor X) :
    Function.Injective (R.pairing D) :=
  R.toSerreResidueRealization.pairing_injective D

/-- **§17.6 — the EASY-half dimension bound `lDim (K−D) ≤ h1Dim D`** from the residue realization. -/
theorem lDim_le_h1Dim (R : GlobalResidue 𝔘 K) (D : Divisor X)
    (hfin : FiniteDimensional ℂ (𝔘.toFiniteFamily.cechH1 D)) :
    lDim (X := X) (K - D) ≤ 𝔘.toFiniteFamily.h1Dim D :=
  R.toSerreResidueRealization.lDim_le_h1Dim D hfin

/-- **The full chain `GlobalResidue → SerreDualityData`** (the ladder target).  Wiring the §17.5/17.6
EASY half (the residue pairing `res ∘ cup` + its derived injectivity) all the way into the
`SerreDualityData 𝔘` that the Riemann–Roch / Serre ladder (`SerreDualityPairing.lean`) consumes:
the residue realization supplies `K`, the pairing `ι`, and its injectivity (`pairing_injective`); the
externally-named inputs are `hKgenus` (Forster §17.4, proven via `CanonicalFormIso`), the §17.9
surjectivity (the HARD half, supplied separately), and finiteness (Forster §14, `finiteDimensional_cechH1`).
This exhibits the residue pairing's contribution to the ladder, not in isolation. -/
def toSerreDualityData (R : GlobalResidue 𝔘 K)
    (hKgenus : lDim (X := X) K = kirovGenus X)
    (ι_surj : ∀ D : Divisor X, Function.Surjective (R.pairing D))
    (finH1 : ∀ D : Divisor X, FiniteDimensional ℂ (𝔘.toFiniteFamily.cechH1 D)) :
    SerreDualityData 𝔘 :=
  R.toSerreResidueRealization.toSerreDualityData hKgenus ι_surj finH1

end GlobalResidue

end Jacobians.Dolbeault

end
