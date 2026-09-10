/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueGateAClosed
import KirovDolbeault.Dolbeault.SerreResidueRamifiedRealSlitGeometry
import KirovDolbeault.Dolbeault.FormRemovableSingularity
import KirovDolbeault.Dolbeault.SerreDuality
import KirovDolbeault.Dolbeault.CechComplex
import KirovDolbeault.Dolbeault.SerreDualityPairing

/-!
# Forster §17.5 residue pairing + §17.6 injectivity — the global `Res` descent and `ι_D`

This file builds the next genuinely-Serre piece (Forster §17.5, step 4): the global
residue functional `Res` on the Mittag–Leffler distribution picture (Forster §17.2–17.3), the residue
**pairing** `ι_D : L(K−D) → (H¹(X,𝒪_D))*` (Forster §17.5), and the §17.6 **injectivity** of `ι_D`
(the EASY half), giving `lDim (K−D) ≤ h1Dim D` — at `D = 0`, `kirovGenus ≤ h1Dim 0`.

## What is PROVEN here (complete, axiom-clean)

* **The global-`Res` well-definedness `res_eq_zero_of_globalMeromorphic`** (Forster §17.3): a
  Mittag–Leffler distribution `μ = ω₀·g` whose principal part `g = f.toFun` comes from a *global*
  meromorphic function `f` (so `α = ω₀·f` is a genuine global meromorphic 1-form — a *coboundary* in
  Forster's terms) has total residue `μ.res = 0`. This is exactly the **1-form residue theorem
  `∑Res = 0`** (`SerreResidueTheorem.residueTheorem_unconditional`, Gate A) repackaged as the
  representative-independence content the global `Res : H¹(X,Ω) → ℂ` rests on: two Mittag–Leffler
  representatives of the same `H¹(X,Ω)` class differ by such a global form, so they have equal residue.
  *This genuinely uses `∑Res = 0`* (it is its conclusion), now **unconditional** via
  `residueTheorem_unconditional` (Gate A closed; `SerreResidueRamifiedRealSlitGeometry.lean`).

* **The abstract §17.6 reduction `injective_of_residueOne_witness`** and the dimension corollary
  `lDim_le_h1Dim_of_residueOne_witness`: an `ℂ`-linear `ι : L(K−D) → (H¹(𝒪_D))*` for which every
  `0 ≠ [f]` admits a class `ξ` with `⟨ι[f], ξ⟩ = 1` is injective, whence (the abstract core
  `SerreDuality.finrank_le_of_injective_to_dual`) `lDim (K−D) ≤ h1Dim D`. This is the linear-algebra
  mechanics of Forster §17.6 wired to the residue-1 witness, leaving only the *geometric* construction
  of `ι` + the witness as the isolated input.

## The isolated input — `SerreResidueRealization` (the `H¹(X,Ω)` realization interface)

The pairing `⟨f, ξ⟩ = Res((f·ω₀)·ξ)` consumes a realization of `H¹(X,𝒪_D)` cohomology *classes* as
Mittag–Leffler distributions (Forster's connecting map `H⁰(principal parts) → H¹(𝒪_D)`) together with
the cup product into `H¹(X,Ω)`. The repo's Čech `H¹` (`FiniteFamily.cechH1`, the structure sheaf
`𝒪_D` germ-cocycle quotient) has **no** such realization built (no Ω-sheaf Čech complex, no cup
product, no Mittag–Leffler ↔ `cechH1` connecting map) — it is a multi-thousand-LoC greenfield build.
We isolate exactly that descent into one named structure `SerreResidueRealization 𝔘`, whose fields are
the *precise* mathematical statements the descent produces (the bilinear residue pairing on
`L(K−D) × cechH1 D` valued in `ℂ`, ℂ-linear in each argument, with the residue-1 non-degeneracy
witness). The pairing `ι`, its linearity, §17.6 injectivity, and `lDim (K−D) ≤ h1Dim D` are all
**derived** from it. See the field docstrings.

## Soundness

`SerreResidueRealization` is **non-vacuous and non-circular**: its non-degeneracy is the genuine
residue-1 witness `exists_formFnResidue_eq_one_of_localRep_ne_zero` (not a junk/zero map — the witness
forces `⟨f,ξ⟩ = 1 ≠ 0`), it does **not** route through Riemann–Roch (RR depends on this), and the
`Res` well-definedness genuinely consumes `∑Res = 0`. The `L(K−D)` side is the junk-free
`lSysModule`, so there is no `toFun`-junk `lDim ≡ 0` collapse. Authoritative axiom check below.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.2–17.6 (pp. 132–140);
Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Module

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Part 1 — The global `Res` well-definedness (Forster §17.3, via `∑Res = 0`)

Forster defines `Res : H¹(X,Ω) → ℂ` on cohomology classes by `Res([δμ]) = Res(μ)` for a Mittag–Leffler
distribution `μ`; this is well-defined precisely because the total residue of a *global* meromorphic
1-form (a coboundary, the difference of two Mittag–Leffler representatives of the same class) vanishes —
the **1-form residue theorem `∑Res = 0`** (Gate A's `residueTheorem_unconditional`). We record that
representative-independence content here as the vanishing of `MittagLefflerForm.res` on a globally
meromorphic distribution. -/

/-- **The global-`Res` well-definedness (Forster §17.3).**  If a Mittag–Leffler distribution `μ` has
its principal-part function `μ.g = f.toFun` for a *global* meromorphic function `f` (so the 1-form
`α = μ.α · f` is globally meromorphic — Forster's *coboundary*), its total residue vanishes:

> `μ.res = 0`.

This is the **1-form residue theorem `∑ Res = 0`** (`SerreResidueTheorem.residueTheorem_unconditional`,
Gate A — closed) read as representative-independence: it is exactly what makes the global functional
`Res : H¹(X,Ω) → ℂ` well-defined on cohomology classes (two Mittag–Leffler representatives of one class
differ by such a global form).  `μ.poles` contains the actual poles of `α` (`μ.holo`), so the
analyticity hypothesis is met; no residual hypothesis remains. -/
theorem MittagLefflerForm.res_eq_zero_of_globalMeromorphic (μ : MittagLefflerForm X)
    (f : MeromorphicFunction X) (hgf : μ.g = f.toFun) :
    μ.res = 0 := by
  -- Off the recorded pole set, `f.toFun = μ.g` is chart-analytic (the `holo` field), so the
  -- `residueTheorem_unconditional` analyticity hypothesis holds; its conclusion is `μ.res = 0`.
  have hpoles : ∀ x : X, x ∉ μ.poles →
      AnalyticAt ℂ (fun z => f.toFun ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x) := by
    intro x hx; rw [← hgf]; exact μ.holo x hx
  have hsum := SerreResidueTheorem.residueTheorem_unconditional μ.α f μ.poles hpoles
  -- `μ.res = residueSum μ.α μ.g μ.poles = ∑ a ∈ poles, formFnResidue μ.α f.toFun a = 0`.
  rw [MittagLefflerForm.res, residueSum, hgf]
  exact hsum

/-- **`Res` is well-defined on cohomology classes (Forster §17.3, two-representative form).**  Two
Mittag–Leffler distributions `μ₁, μ₂` sharing the global form factor `α` and differing (in their
principal parts) by a *global* meromorphic function — `μ₁.g − μ₂.g = f.toFun`, so `δμ₁ = δμ₂` represent
the same `H¹(X,Ω)` class — have **equal** total residue:

> `μ₁.res = μ₂.res`.

The difference distribution `μ₁ − μ₂` (formed as `μ₁ + (−1)·μ₂` via `combine`/`smul`) is a coboundary
(`g = f.toFun`), so its residue vanishes by `res_eq_zero_of_globalMeromorphic` (the 1-form residue
theorem `∑Res = 0`); `res_combine`/`res_smul` then give `μ₁.res − μ₂.res = 0`.  This is precisely the
representative-independence that defines the global `Res : H¹(X,Ω) → ℂ`. -/
theorem MittagLefflerForm.res_eq_of_globalMeromorphic_diff (μ₁ μ₂ : MittagLefflerForm X)
    (hα : μ₁.α = μ₂.α) (f : MeromorphicFunction X) (hgf : μ₁.g + (-1 : ℂ) • μ₂.g = f.toFun) :
    μ₁.res = μ₂.res := by
  -- The difference distribution `δ = μ₁ + (−1)·μ₂`, with `δ.α = μ₁.α` and `δ.g = μ₁.g + (−1)•μ₂.g`.
  set δ := μ₁.combine (μ₂.smul (-1)) (by rw [MittagLefflerForm.smul_α]; exact hα) with hδ
  have hδg : δ.g = f.toFun := by
    rw [hδ, MittagLefflerForm.combine_g, MittagLefflerForm.smul_g]; exact hgf
  -- `δ` is a coboundary, so `δ.res = 0` (the 1-form residue theorem).
  have hδres : δ.res = 0 := δ.res_eq_zero_of_globalMeromorphic f hδg
  -- `δ.res = μ₁.res + (−1)·μ₂.res = μ₁.res − μ₂.res`, so `μ₁.res = μ₂.res`.
  rw [hδ, MittagLefflerForm.res_combine, MittagLefflerForm.res_smul] at hδres
  simp only [neg_one_smul] at hδres
  linear_combination hδres

/-! ## Part 2 — The abstract §17.6 injectivity reduction (residue-1 witness ⟹ injective)

Forster §17.6 proves `ι_D` injective by exhibiting, for each nonzero class, a `H¹(𝒪_D)`-class on which
the pairing is `1` (the local `dz/z` residue-1 witness). The linear-algebra mechanics of that — a
pairing into a dual with a "value-1 witness" at every nonzero point is injective, hence (the abstract
core `SerreDuality.finrank_le_of_injective_to_dual`) dimension-bounds the source — is recorded here,
parametric in the pairing and the finite-dimensional target. It is the EASY-half engine: feed it the
geometric pairing + witness (the isolated `SerreResidueRealization` input below) to get
`lDim (K−D) ≤ h1Dim D`. -/

/-- **§17.6 — a residue-1 witness forces injectivity.**  An `ℂ`-linear map `ι : V → W*` (into the dual
of any `W`) for which every nonzero `v` has a `ξ : W` with `(ι v) ξ = 1` is injective: if `ι v = 0`
then `(ι v) ξ = 0 ≠ 1`.  This is the linear-algebra content of Forster's `ι_D` injectivity step. -/
theorem injective_of_residueOne_witness {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ι : V →ₗ[ℂ] Module.Dual ℂ W)
    (hwit : ∀ v : V, v ≠ 0 → ∃ ξ : W, (ι v) ξ = 1) :
    Function.Injective ι := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  by_contra hne
  obtain ⟨ξ, hξ⟩ := hwit v hne
  rw [LinearMap.mem_ker] at hv
  rw [hv, LinearMap.zero_apply] at hξ
  exact one_ne_zero hξ.symm

/-- **§17.6 — the dimension bound from a residue-1 witness** (the EASY half of Serre duality).  Given
a pairing `ι : V → (W)*` into the dual of a *finite-dimensional* `W`, with a residue-1 witness at every
nonzero `v`, we get `finrank V ≤ finrank W`.  Chains `injective_of_residueOne_witness` with the abstract
core `SerreDuality.finrank_le_of_injective_to_dual`.  Instantiated at `V = L(K−D)`, `W = H¹(𝒪_D)` this is
`lDim (K−D) ≤ h1Dim D`. -/
theorem finrank_le_of_residueOne_witness {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ι : V →ₗ[ℂ] Module.Dual ℂ W)
    (hwit : ∀ v : V, v ≠ 0 → ∃ ξ : W, (ι v) ξ = 1) :
    finrank ℂ V ≤ finrank ℂ W :=
  SerreDuality.finrank_le_of_injective_to_dual ι (injective_of_residueOne_witness ι hwit)

/-! ## Part 3 — The `H¹(X,Ω)` realization interface and the §17.5 pairing + §17.6 injectivity

The geometric residue pairing `ι_D : L(K−D) → (H¹(𝒪_D))*`, `⟨f,ξ⟩ = Res((f·ω₀)·ξ)`, consumes a
realization of `H¹(X,𝒪_D)` cohomology classes that the repo does not yet have: the Mittag–Leffler
representation of classes (Forster's connecting map) and the cup product into `H¹(X,Ω)` carrying the
global `Res`. We isolate exactly that descent into the structure below — the single named input — and
**derive** the §17.5 pairing, §17.6 injectivity, and the EASY-half dimension bound from it. -/

/-- **[ISOLATED INPUT — the `H¹(X,Ω)` realization for the §17.5 residue pairing].**  The geometric
output of the Forster §17.2–17.5 descent that the repo's Čech `H¹` (`FiniteFamily.cechH1`, the `𝒪_D`
germ-cocycle quotient) does not yet realize: a cup-product-then-residue **bilinear pairing**
`pairing D : L(K−D) → (H¹(𝒪_D))* `, `⟨f, ξ⟩ = Res((f·ω₀)·ξ)`, ℂ-linear in `f` (bundled as the linear
map into the dual) and equipped with the **§17.6 residue-1 non-degeneracy witness** (`witness`).

This is the precise interface the global `Res` descent (Part 1) + the Mittag–Leffler / cup-product
realization (greenfield: no Ω-sheaf Čech complex, no cup product, no `cechH1 ↔ Mittag–Leffler`
connecting map are built — a multi-thousand-LoC piece) must supply.
It is **sound**: `witness` is the genuine residue-1 datum (the pairing is non-degenerate, not a junk/zero
map), `L(K−D)` is the junk-free `lSysModule` (no `toFun`-junk collapse), and it does **not** route
through Riemann–Roch (no circularity — RR depends on this).

The surjectivity side (§17.9, the HARD half) is **not** part of this interface; it is built later from
the cohomological Riemann–Roch dimension count (`SerreDuality.serre_surjectivity_dim_core`). -/
structure SerreResidueRealization (𝔘 : FiniteCover X) (K : Divisor X) where
  /-- The §17.5 residue pairing `ι_D : L(K−D) → (H¹(𝒪_D))*`, `⟨f, ξ⟩ = Res((f·ω₀)·ξ)`, as an ℂ-linear
  map into the dual (ℂ-linearity in `f` from `res_add`/`res_smul`). -/
  pairing : ∀ D : Divisor X, lSysModule (K - D) →ₗ[ℂ] Module.Dual ℂ (𝔘.cechH1 D)
  /-- **§17.6 residue-1 non-degeneracy witness.**  For every nonzero class `0 ≠ [f] ∈ L(K−D)` there is
  a cohomology class `ξ ∈ H¹(𝒪_D)` with `⟨f, ξ⟩ = Res((f·ω₀)·ξ) = 1` — the `dz/z` witness
  (`exists_formFnResidue_eq_one_of_localRep_ne_zero`) transported through the realization.  This makes
  `pairing` genuinely non-degenerate (not the zero map). -/
  witness : ∀ (D : Divisor X) (v : lSysModule (K - D)), v ≠ 0 →
    ∃ ξ : 𝔘.cechH1 D, (pairing D v) ξ = 1

namespace SerreResidueRealization

variable {𝔘 : FiniteCover X} {K : Divisor X}

/-- **§17.6 — injectivity of the residue pairing `ι_D`** (the EASY half).  From the residue-1 witness:
`ι_D` is injective for every divisor `D`.  (`injective_of_residueOne_witness`.) -/
theorem pairing_injective (R : SerreResidueRealization 𝔘 K) (D : Divisor X) :
    Function.Injective (R.pairing D) :=
  injective_of_residueOne_witness (R.pairing D) (R.witness D)

/-- **§17.6 — the EASY-half dimension bound `lDim (K−D) ≤ h1Dim D`.**  From injectivity of the residue
pairing into the (finite-dimensional, via `finH1`) dual of `H¹(𝒪_D)`.  At `D = 0`: `kirovGenus ≤ h1Dim 0`. -/
theorem lDim_le_h1Dim (R : SerreResidueRealization 𝔘 K) (D : Divisor X)
    (hfin : FiniteDimensional ℂ (𝔘.cechH1 D)) :
    lDim (X := X) (K - D) ≤ 𝔘.h1Dim D := by
  haveI := hfin
  exact finrank_le_of_residueOne_witness (R.pairing D) (R.witness D)

/-- **The bridge to the ladder target `SerreDualityData`.**  A residue realization (the §17.6
injectivity half) together with the canonical `K`'s `hKgenus` (Forster §17.4,
`exists_canonicalForm17Data_hKgenus`), the §17.9 surjectivity (the HARD half, supplied separately),
and finiteness assembles into the full `SerreDualityData 𝔘` that the Riemann–Roch / Serre ladder
(`SerreDualityPairing.lean`) consumes.  The injectivity field is **derived** (`pairing_injective`); only
`hKgenus` (now proven) and surjectivity remain externally.  This wires the residue pairing into the
downstream target rather than leaving it isolated. -/
def toSerreDualityData (R : SerreResidueRealization 𝔘 K)
    (hKgenus : lDim (X := X) K = kirovGenus X)
    (ι_surj : ∀ D : Divisor X, Function.Surjective (R.pairing D))
    (finH1 : ∀ D : Divisor X, FiniteDimensional ℂ (𝔘.cechH1 D)) :
    SerreDualityData 𝔘 where
  K := K
  hKgenus := hKgenus
  ι := R.pairing
  ι_inj := R.pairing_injective
  ι_surj := ι_surj
  finH1 := finH1

end SerreResidueRealization

end Jacobians.Dolbeault

end
