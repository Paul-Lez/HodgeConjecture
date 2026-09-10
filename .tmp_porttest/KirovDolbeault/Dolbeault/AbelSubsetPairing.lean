/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.AbelSubsetCriterion
import KirovDolbeault.Dolbeault.FineResidue.CoboundaryVanish
import KirovDolbeault.Dolbeault.FineResidue.OmegaWitness
import KirovDolbeault.Dolbeault.FormCoeff
import KirovDolbeault.HolomorphicForms

/-!
# Abel ⊆ campaign, P-block: the concrete period pairing `σ ↦ ∫_X σ∧ω`

Realization of the period functional that the S-block's abstract criterion
(`mem_dbarImage_of_periodFunctional`, `AbelSubsetCriterion.lean`) consumes — rungs P1–P6 of
`docs/planning/AB_ROUTE.md`.  The global integral is the PoU-planar `FineResidue.resIntegral`;
the pairing's `(1,1)` chart-coefficient family is the product of

* the **(0,1) read** of `σ ∈ A^{0,1}(X)` — the proven `cutoffPullback` of the forward Dolbeault
  comparison (smooth, compactly supported, `ℝ`-linear in `σ`), whose `conj φ′` overlap law
  (`cutoffPullback_overlap_law`, **P1**) we derive from the cross-chart cancellation
  `dbar_planarDiff_eq_zero` + the Wirtinger chain rule — no frame computations;
* a **holomorphic `(1,0)` slot family** `g` (`IsOneZeroCoeff`, in the application the chart
  coefficients `omegaCoeff 𝔇 ω` of a global holomorphic 1-form).

Main declarations:

* `pairCoeff 𝔇 σ g` / `pairCoeff_mem_oneOneCoeff` (**P2**) — the product family is a global
  `(1,1)` chart-coefficient family (`conj φ′ · φ′ = |φ′|²`, R1's `OneOneLawAt`).
* `pairFormL 𝔇 hσ hg` / `pairOmega 𝔇 σ α` (**P3**) — the pairing `∫_X σ∧ω` as the
  `resIntegral` of `pairCoeff`; `ℝ`-linear in `σ`, `ℂ`-linear in the holomorphic slot
  (`pairOmega_slot_smul`, `pairOmega_slot_add`), `ℂ`-homogeneous in `σ` through constant
  rescaling (`pairOmega_cSmul`).
* `pairOmega_dbarL` (**P4**, the Stokes kill) — `∫_X ∂̄u∧ω = 0`: per chart the Leibniz split
  `ρ̃ⱼ·∂̄ũⱼ·gⱼ = ∂̄(ρ̃ⱼ·ũⱼ·gⱼ) − ∂̄ρ̃ⱼ·ũⱼ·gⱼ` plus the planar Stokes atom, then the proven
  relocation + PoU-reinsertion kill of `CoboundaryVanish` at the global weight `β = u`.
* `exists_pairOmega_ne_zero` (**P5**, nondegeneracy) — every nonzero holomorphic form pairs
  nontrivially against some `(0,1)`-form: a one-chart bump witness `σ = h·∂̄w` whose pairing is
  `∫ χ·|f|² > 0` at a point where the coefficient `f` of `ω` does not vanish.
* `pairPeriod_surjective` (**P5**) — the period functional `Λ = (pairOmega · ωᵢ)ᵢ` onto
  `ℂ^g` is surjective: its range is a `ℂ`-subspace (P3 homogeneity) meeting no annihilating
  hyperplane (P5 nondegeneracy + slot linearity).
* `dbar_solvable_of_pairOmega_eq_zero` (**P6**, the solvability theorem) — Forster 19.10:
  a `(0,1)`-form pairing to zero against every holomorphic 1-form is `∂̄`-exact.  S4 + P4 + P5.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §19.10, §20; Miranda,
*Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. X §2.
-/

open Complex Filter MeasureTheory
open scoped Manifold ContDiff Topology Classical
open TopologicalSpace (Opens)

-- Same permissive transparency as `RealForms`/`DolbeaultComparisonInverse`/`Integral` (the
-- `SmoothCFunctions` coercions and hom-bundle instances below need it).
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable (𝔇 : ChartDiskCover X)

/-! ## P1 — the `(0,1)` overlap law of the cutoff chart-pullback

The chart-`j` read of `σ ∈ A^{0,1}` used throughout is the **proven** forward-comparison datum
`𝔇.cutoffPullback j σ` (smooth with compact support, equal to the honest read `σ x (frame 1)` on
the chart image of `U j` where the disk bump is `1`).  Its `(0,1)` transformation law on overlaps
falls out of three public bricks of the comparison proof — no frame algebra:

* `∂̄(planarPrimitive i σ) = cutoffPullback i σ`  (`dbar_planarPrimitive`),
* the cross-chart cancellation `∂̄(P_k∘φ − P_j) = 0` on overlaps (`dbar_planarDiff_eq_zero`),
* the Wirtinger chain rule `∂̄(f∘φ) = conj φ′ · (∂̄f)∘φ` (`dbarDisk_comp_holo`). -/

/-- The `FineResidue` transition map is the extended-chart transition (the model embedding of
`𝓘(ℝ, ℂ)` is the identity, so both are the bare chart composite). -/
theorem transitionMap_eq_extChartAt (j k : 𝔇.toFiniteCover.ι) (z : ℂ) :
    transitionMap 𝔇 j k z
      = (extChartAt 𝓘(ℝ, ℂ) (𝔇.center k)) ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).symm z) := rfl

/-- **P1 — the pointwise `(0,1)` overlap law of the cutoff chart-pullback.**  At the chart-`j`
coordinate of every overlap point `x ∈ U j ⊓ U k`,

  `σ̃_j = (σ̃_k ∘ φ_{jk}) · conj φ′_{jk}`,   `σ̃_i := cutoffPullback 𝔇 i σ`.

Derivation: both disk primitives satisfy `∂̄P_i = σ̃_i`; the relocated difference `P_k∘φ − P_j`
is `∂̄`-closed at the overlap (`dbar_planarDiff_eq_zero`), and the chain rule turns
`∂̄(P_k∘φ)` into `conj φ′ · σ̃_k∘φ`. -/
theorem cutoffPullback_overlap_law {σ : SmoothCOneForms X} (hσ : σ ∈ OneFormsZeroOne X)
    {j k : 𝔇.toFiniteCover.ι} {x : X} (hxj : x ∈ (𝔇.U j : Set X))
    (hxk : x ∈ (𝔇.U k : Set X)) :
    𝔇.cutoffPullback j σ (chartMap 𝔇 j x)
      = 𝔇.cutoffPullback k σ (transitionMap 𝔇 j k (chartMap 𝔇 j x))
          * (starRingEnd ℂ) (deriv (transitionMap 𝔇 j k) (chartMap 𝔇 j x)) := by
  set z₀ := chartMap 𝔇 j x with hz₀
  set τ := transitionMap 𝔇 j k with hτ
  -- The relocated difference of the disk primitives is `∂̄`-closed at `z₀` (the relocated read
  -- is definitionally `P_k ∘ τ` — the model embedding of `𝓘(ℝ, ℂ)` is the identity).
  have hdiff0 : DbarDisk.dbar (fun z => (𝔇.planarPrimitive k σ ∘ τ) z
      - 𝔇.planarPrimitive j σ z) z₀ = 0 :=
    𝔇.dbar_planarDiff_eq_zero hσ j k hxj hxk
  -- Differentiability of the pieces at `z₀`.
  have hτdiff : DifferentiableAt ℂ τ z₀ :=
    (transitionMap_analyticAt 𝔇 hxj hxk).differentiableAt
  have hPk : DifferentiableAt ℝ (𝔇.planarPrimitive k σ) (τ z₀) :=
    (𝔇.contDiff_planarPrimitive k σ).differentiable (by norm_num) _
  have hPj : DifferentiableAt ℝ (𝔇.planarPrimitive j σ) z₀ :=
    (𝔇.contDiff_planarPrimitive j σ).differentiable (by norm_num) _
  have hPkτ : DifferentiableAt ℝ (𝔇.planarPrimitive k σ ∘ τ) z₀ :=
    hPk.comp z₀ (hτdiff.restrictScalars ℝ)
  -- `∂̄` of the difference splits termwise.
  have hsub : DbarDisk.dbar (fun z => (𝔇.planarPrimitive k σ ∘ τ) z
        - 𝔇.planarPrimitive j σ z) z₀
      = DbarDisk.dbar (𝔇.planarPrimitive k σ ∘ τ) z₀
        - DbarDisk.dbar (𝔇.planarPrimitive j σ) z₀ := by
    unfold DbarDisk.dbar
    rw [show (fun z => (𝔇.planarPrimitive k σ ∘ τ) z - 𝔇.planarPrimitive j σ z)
        = (𝔇.planarPrimitive k σ ∘ τ) - 𝔇.planarPrimitive j σ from rfl,
      fderiv_sub hPkτ hPj]
    simp only [ContinuousLinearMap.sub_apply]
    ring
  rw [hsub] at hdiff0
  -- Chain rule on the relocated primitive, then read the two `∂̄`s as cutoff pullbacks.
  rw [dbarDisk_comp_holo (𝔇.planarPrimitive k σ) τ z₀ hPk hτdiff,
    𝔇.dbar_planarPrimitive k σ (τ z₀), 𝔇.dbar_planarPrimitive j σ z₀] at hdiff0
  linear_combination -hdiff0

/-! ## P2 — the pairing `(1,1)` chart-coefficient family -/

/-- The **pairing `(1,1)` chart-coefficient family** of a smooth `(0,1)`-form `σ` and a
holomorphic `(1,0)` slot family `g`:

  `t_j := σ̃_j · g_j`,   `σ̃_j = cutoffPullback 𝔇 j σ`

— the chart-coefficient presentation of the global `(1,1)`-form `σ∧ω` whose surface integral is
the period pairing.  (For the cutoff-vs-honest-read discrepancy outside the disks: the residue
integral weights by `pouCoeff`, which vanishes there, so only the honest read is ever
integrated.) -/
noncomputable def pairCoeff (σ : SmoothCOneForms X) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) :
    𝔇.toFiniteCover.ι → ℂ → ℂ :=
  fun j z => 𝔇.cutoffPullback j σ z * g j z

@[simp] theorem pairCoeff_apply (σ : SmoothCOneForms X) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ)
    (j : 𝔇.toFiniteCover.ι) (z : ℂ) :
    pairCoeff 𝔇 σ g j z = 𝔇.cutoffPullback j σ z * g j z := rfl

/-- **P2 — the pairing family is a global `(1,1)` chart-coefficient family.**  Smoothness is the
(global) smoothness of the cutoff pullback times the analyticity of the slot; the `(1,1)` law
`normSq φ′` assembles as `conj φ′` (P1) times `φ′` (the slot's `OneZeroLawAt`), by
`Complex.mul_conj`. -/
theorem pairCoeff_mem_oneOneCoeff {σ : SmoothCOneForms X} (hσ : σ ∈ OneFormsZeroOne X)
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) :
    pairCoeff 𝔇 σ g ∈ oneOneCoeff 𝔇 := by
  rw [mem_oneOneCoeff]
  constructor
  · intro j x hx
    exact ((𝔇.contDiff_cutoffPullback j σ).contDiffAt).mul
      (((hg.1 j x hx).restrictScalars (𝕜 := ℝ)).contDiffAt)
  · intro j k x hx
    unfold OneOneLawAt
    filter_upwards [(isOpen_overlapImage 𝔇 j k).mem_nhds ⟨x, hx, rfl⟩, hg.2 j k x hx]
      with z hzov hzg
    obtain ⟨x', hx', hzx'⟩ := hzov
    subst hzx'
    have hlaw := cutoffPullback_overlap_law 𝔇 hσ hx'.1 hx'.2
    have hns : ((normSq (deriv (transitionMap 𝔇 j k) (chartMap 𝔇 j x')) : ℝ) : ℂ)
        = deriv (transitionMap 𝔇 j k) (chartMap 𝔇 j x')
            * (starRingEnd ℂ) (deriv (transitionMap 𝔇 j k) (chartMap 𝔇 j x')) :=
      (Complex.mul_conj _).symm
    simp only [pairCoeff_apply]
    rw [hlaw, hzg, hns]
    ring

/-! ## P3 — the pairing as a linear functional

`pairFormL 𝔇 hg : A^{0,1}(X) →ₗ[ℝ] ℂ` is `resIntegral` of the pairing family; linearity in `σ`
comes from the (proven) `ℝ`-linearity of the cutoff pullback through the `ℂ`-linearity of
`resIntegral`. -/

/-- The pairing family bundled as an element of the `(1,1)` submodule. -/
noncomputable def pairElem {σ : SmoothCOneForms X} (hσ : σ ∈ OneFormsZeroOne X)
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) : oneOneCoeff 𝔇 :=
  ⟨pairCoeff 𝔇 σ g, pairCoeff_mem_oneOneCoeff 𝔇 hσ hg⟩

/-- **P3 — the period pairing against a fixed holomorphic slot family, as an `ℝ`-linear
functional on `A^{0,1}(X)`**:

  `σ ↦ ∮_X σ∧ω := resIntegral 𝔇 (σ̃·g)`.

(`ℝ`-linear because `A^{0,1}` carries only `Module ℝ`; `ℂ`-rescaling is `pairFormL_cSmulForm`
below.) -/
noncomputable def pairFormL {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) :
    ↥(OneFormsZeroOne X) →ₗ[ℝ] ℂ where
  toFun σ := resIntegral 𝔇 (pairElem 𝔇 σ.2 hg)
  map_add' σ τ := by
    have helem : pairElem 𝔇 (σ + τ).2 hg = pairElem 𝔇 σ.2 hg + pairElem 𝔇 τ.2 hg := by
      apply Subtype.ext
      show pairCoeff 𝔇 ((σ : SmoothCOneForms X) + (τ : SmoothCOneForms X)) g
        = pairCoeff 𝔇 (σ : SmoothCOneForms X) g + pairCoeff 𝔇 (τ : SmoothCOneForms X) g
      funext j z
      simp only [pairCoeff_apply, 𝔇.cutoffPullback_add j, Pi.add_apply]
      ring
    rw [helem, map_add]
  map_smul' c σ := by
    have helem : pairElem 𝔇 (c • σ).2 hg = (c : ℂ) • pairElem 𝔇 σ.2 hg := by
      apply Subtype.ext
      show pairCoeff 𝔇 (c • (σ : SmoothCOneForms X)) g
        = (c : ℂ) • pairCoeff 𝔇 (σ : SmoothCOneForms X) g
      funext j z
      simp only [pairCoeff_apply, 𝔇.cutoffPullback_smul j, Pi.smul_apply, smul_eq_mul,
        Complex.real_smul]
      ring
    rw [helem, map_smul, RingHom.id_apply, smul_eq_mul, Complex.real_smul]

theorem pairFormL_apply {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g)
    (σ : ↥(OneFormsZeroOne X)) :
    pairFormL 𝔇 hg σ = resIntegral 𝔇 (pairElem 𝔇 σ.2 hg) := rfl

/-- **The period pairing against a global holomorphic 1-form** — `pairFormL` at the canonical
slot family `omegaCoeff 𝔇 α` (the chart coefficients of `α`, R-lane witness
`isOneZeroCoeff_omegaCoeff`). -/
noncomputable def pairOmega (σ : ↥(OneFormsZeroOne X)) (α : HolomorphicOneForms X) : ℂ :=
  pairFormL 𝔇 (isOneZeroCoeff_omegaCoeff 𝔇 α) σ

theorem pairOmega_apply (σ : ↥(OneFormsZeroOne X)) (α : HolomorphicOneForms X) :
    pairOmega 𝔇 σ α
      = resIntegral 𝔇 (pairElem 𝔇 σ.2 (isOneZeroCoeff_omegaCoeff 𝔇 α)) := rfl

/-! ## P4 — the Stokes kill: `∫_X ∂̄u ∧ ω = 0`

Per chart: the cutoff pullback of `∂̄u` is the planar `∂̄` of the chart read of `u`
(`cutoffPullback_dbarL`, the chart-bridge + chain-rule computation), the Leibniz split
`ρ̃ⱼ·∂̄ũⱼ·gⱼ = ∂̄(ρ̃ⱼ·ũⱼ·gⱼ) − ∂̄ρ̃ⱼ·(ũⱼ·gⱼ)` (its total-derivative part dying by the planar
Stokes atom), and then the **proven** relocation + PoU-reinsertion kill of `CoboundaryVanish`
at the global weight `β = u`. -/

/-- **P4a — the cutoff pullback of `∂̄u` is the planar `∂̄` of the chart read of `u`** on the
chart image of the cover disk.  The intrinsic Wirtinger scalar transported to the cover chart:
chart bridge at `x`'s own chart (`dbar_apply_one_eq_dbarDisk`), conjugate-homogeneity of the
`(0,1)` fiber (`proj01_eq_conj_smul`), the frame identity
(`frameVector_eq_deriv_transition_symm`), and the Wirtinger chain rule reassembling the two
`conj` factors. -/
theorem cutoffPullback_dbarL {u : SmoothCFunctions X} {j : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U j : Set X)) :
    𝔇.cutoffPullback j (dbarL u) (chartMap 𝔇 j x)
      = DbarDisk.dbar (fun ζ => u ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x) := by
  set ej := extChartAt 𝓘(ℝ, ℂ) (𝔇.center j) with hej
  set ex := extChartAt 𝓘(ℝ, ℂ) x with hexx
  set z₀ := chartMap 𝔇 j x with hz₀
  set σtr := (ex : X → ℂ) ∘ (ej.symm : ℂ → X) with hσtr
  have hxsrc : x ∈ ej.source := 𝔇.subset_chart_source j hx
  have hsymm : ej.symm z₀ = x := ej.left_inv hxsrc
  -- The disk bump is `1` on the disk.
  have hball : ej x ∈ Metric.ball (ej (𝔇.center j)) (𝔇.radius j) := by
    have h := hx
    rw [𝔇.isDisk j] at h
    exact h.1
  have hχ : (𝔇.diskBump j) z₀ = 1 :=
    (𝔇.diskBump j).one_of_mem_closedBall (Metric.ball_subset_closedBall hball)
  -- Unfold the cutoff pullback at `z₀` and substitute the frame vector.
  rw [show 𝔇.cutoffPullback j (dbarL u) z₀ = ((𝔇.diskBump j) z₀ : ℝ) •
      ((dbarL u) (ej.symm z₀)) ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) (𝔇.center j)) (ej.symm z₀)) (1 : ℂ))
    from rfl, hχ, hsymm, one_smul,
    frameVector_eq_deriv_transition_symm (𝔇.center j) x hxsrc]
  -- Re-read the left side as `proj01 (mfderiv u x)` applied to the (planar) `deriv σtr (ej x)`,
  -- so the conjugate-homogeneity + chart bridge apply.
  show proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x) (deriv σtr (ej x))
    = DbarDisk.dbar (fun ζ => u ((chartAt ℂ (𝔇.center j)).symm ζ)) z₀
  rw [proj01_eq_conj_smul, dbar_apply_one_eq_dbarDisk u x]
  -- Read the right-hand side through the holomorphic inverse transition `σtr = eₓ ∘ ej.symm`.
  have hσdiff : DifferentiableAt ℂ σtr z₀ :=
    differentiableAt_chartTransition_symm (𝔇.center j) x hxsrc
  have hσz₀ : σtr z₀ = ex x := by
    rw [hσtr]
    simp only [Function.comp_apply, hsymm]
  have hev : (fun ζ => u ((chartAt ℂ (𝔇.center j)).symm ζ))
      =ᶠ[𝓝 z₀] (fun ζ => u (ex.symm ζ)) ∘ σtr := by
    have hcont : ContinuousAt ej.symm z₀ :=
      continuousAt_extChartAt_symm'' (ej.map_source hxsrc)
    have hmem : ∀ᶠ ζ in 𝓝 z₀, ej.symm ζ ∈ ex.source := by
      refine hcont.preimage_mem_nhds ?_
      rw [hsymm]
      exact (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x)
    filter_upwards [hmem] with ζ hζ
    simp only [Function.comp_apply, hσtr]
    rw [ex.left_inv hζ]
    rfl
  have hudiff : DifferentiableAt ℝ (fun ζ => u (ex.symm ζ)) (σtr z₀) := by
    rw [hσz₀]
    exact (contDiffAt_chartSymmRead u.contMDiff
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))).differentiableAt (by simp)
  rw [dbar_congr_of_eventuallyEq hev,
    dbarDisk_comp_holo (fun ζ => u (ex.symm ζ)) σtr z₀ hudiff hσdiff, hσz₀]
  rfl

/-- **P4b — the per-chart Leibniz/Stokes step at a global smooth `β`** (the `∂̄u`-pairing
analogue of `integral_pouCoeff_glueCoeff_of_coboundary`): the `j`-th summand of the pairing
integral is, after the Leibniz split

  `ρ̃ⱼ·∂̄β̃ⱼ·gⱼ = ∂̄(ρ̃ⱼ·(β̃ⱼ·gⱼ)) − ∂̄ρ̃ⱼ·(β̃ⱼ·gⱼ)`

and the planar Stokes atom on the total-derivative term, minus the PoU-reinserted overlap sum
ready for the (proven) relocation. -/
theorem integral_pouCoeff_dbarRead_mul {β : X → ℂ}
    (hβ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) β) {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    (hg : IsOneZeroCoeff 𝔇 g) (j : 𝔇.toFiniteCover.ι) :
    ∫ z, pouCoeff 𝔇 j z
        * (DbarDisk.dbar (fun ζ => β ((chartAt ℂ (𝔇.center j)).symm ζ)) z * g j z)
      = - ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
  have hBsm := contDiffAt_pouAverageRead_mul 𝔇 hβ hg j
  -- the everywhere pointwise Leibniz identity
  have hpt : ∀ z, pouCoeff 𝔇 j z
      * (DbarDisk.dbar (fun ζ => β ((chartAt ℂ (𝔇.center j)).symm ζ)) z * g j z)
      = DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z
        - DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z) := by
    intro z
    by_cases hzU : z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X)
    · obtain ⟨x, hxU, rfl⟩ := hzU
      have hzt : chartMap 𝔇 j x ∈ (chartAt ℂ (𝔇.center j)).target :=
        (chartAt ℂ (𝔇.center j)).map_source (mem_chartSource_of_mem_U 𝔇 hxU)
      have hβd : DifferentiableAt ℝ
          (fun ζ => β ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x) :=
        (contDiffAt_chartSymmRead hβ hzt).differentiableAt (by simp)
      have hgd : DifferentiableAt ℝ (g j) (chartMap 𝔇 j x) :=
        ((hg.1 j x hxU).restrictScalars (𝕜 := ℝ)).differentiableAt
      have hdbarB : DbarDisk.dbar
            (fun ζ => β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ) (chartMap 𝔇 j x)
          = DbarDisk.dbar (fun ζ => β ((chartAt ℂ (𝔇.center j)).symm ζ))
              (chartMap 𝔇 j x) * g j (chartMap 𝔇 j x) := by
        rw [dbar_mul hβd hgd,
          DbarDisk.dbar_eq_zero_of_differentiableAt (hg.1 j x hxU).differentiableAt,
          mul_zero, add_zero]
      have hdbarPB : DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) (chartMap 𝔇 j x)
          = DbarDisk.dbar (pouCoeff 𝔇 j) (chartMap 𝔇 j x)
              * (β ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x))
                  * g j (chartMap 𝔇 j x))
            + pouCoeff 𝔇 j (chartMap 𝔇 j x)
              * DbarDisk.dbar
                  (fun ζ => β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)
                  (chartMap 𝔇 j x) :=
        dbar_mul ((contDiff_pouCoeff 𝔇 j).differentiable (by simp) _)
          ((hBsm _ ⟨x, hxU, rfl⟩).differentiableAt (by simp))
      rw [hdbarPB, hdbarB]
      ring
    · have hzs : z ∉ chartMap 𝔇 j '' tsupport (cechPoU 𝔇 j) := fun hc =>
        hzU (Set.image_mono (fun y hy => cechPoU_subordinate 𝔇 j hy) hc)
      have hP0 : pouCoeff 𝔇 j z = 0 := Set.indicator_of_notMem hzU _
      have hD0 : DbarDisk.dbar (pouCoeff 𝔇 j) z = 0 :=
        dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hzs
      have hPB0 : DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
          * (β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z = 0 := by
        refine dbar_eq_zero_of_eventuallyEq_zero ?_
        filter_upwards [(isCompact_image_tsupport_cechPoU 𝔇
          j).isClosed.isOpen_compl.mem_nhds hzs] with ζ hζ
        rw [pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hζ, zero_mul]
      rw [hP0, hD0, hPB0, zero_mul, zero_mul, sub_zero]
  -- integrability bookkeeping (the `CoboundaryVanish` clearance pattern)
  have hDBcd : ContDiff ℝ (⊤ : ℕ∞) fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    contDiff_of_chartImage_clearance 𝔇
      (fun z hz => (ChartDiskCover.contDiffAt_dbar_chartDisk
        (contDiff_pouCoeff 𝔇 j).contDiffAt).mul (hBsm z hz))
      (fun z hz => by rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hz, zero_mul])
  have hDBcs : HasCompactSupport fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    (DbarDisk.hasCompactSupport_dbar (hasCompactSupport_pouCoeff 𝔇 j)).mul_right
  have hI1 : Integrable fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    hDBcd.continuous.integrable_of_hasCompactSupport hDBcs
  have hPBcd : ContDiff ℝ (⊤ : ℕ∞) fun ζ => pouCoeff 𝔇 j ζ
      * (β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ) :=
    contDiff_pouCoeff_mul 𝔇 hBsm
  have hPBcs : HasCompactSupport fun ζ => pouCoeff 𝔇 j ζ
      * (β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ) :=
    (hasCompactSupport_pouCoeff 𝔇 j).mul_right
  have hI2 : Integrable fun z => DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
      * (β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z :=
    (DbarDisk.continuous_dbar hPBcd).integrable_of_hasCompactSupport
      (DbarDisk.hasCompactSupport_dbar hPBcs)
  calc ∫ z, pouCoeff 𝔇 j z
      * (DbarDisk.dbar (fun ζ => β ((chartAt ℂ (𝔇.center j)).symm ζ)) z * g j z)
      = ∫ z, (DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z
          - DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = (∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z)
          - ∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
        integral_sub hI2 hI1
    _ = - ∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
          * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z) := by
        rw [integral_dbar_eq_zero hPBcd hPBcs, zero_sub]
    _ = - ∫ z, ∑ k, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [← Finset.sum_mul, sum_rhoC_apply, one_mul]
    _ = - ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
        congr 1
        refine integral_finsetSum Finset.univ fun k _ => ?_
        have hcd : ContDiff ℝ (⊤ : ℕ∞) fun z =>
            rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
              * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                  * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) :=
          contDiff_of_chartImage_clearance 𝔇
            (fun z hz => (contDiffAt_chartSymmRead (rhoC 𝔇 k).contMDiff
              (chartMap_image_U_subset_target 𝔇 j hz)).mul hDBcd.contDiffAt)
            (fun z hz => by
              rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hz, zero_mul, mul_zero])
        exact hcd.continuous.integrable_of_hasCompactSupport hDBcs.mul_left

/-- **P4 — the Stokes kill.**  The period pairing annihilates the image of `∂̄`:

  `∮_X ∂̄u ∧ ω = 0`

for every real-smooth `u : X → ℂ` and every holomorphic `(1,0)` slot family.  Per chart the
integrand is `ρ̃ⱼ·∂̄ũⱼ·gⱼ` (P4a); Leibniz + planar Stokes (P4b), the proven relocation
(`integral_overlapTerm_relocate` at `β = u`), and the PoU-reinsertion kill
(`sum_integral_relocated_eq_zero`) finish exactly as in Forster §17.3 step 5. -/
theorem pairFormL_dbarL {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g)
    (u : SmoothCFunctions X) :
    pairFormL 𝔇 hg ⟨dbarL u, dbarL_mem_zeroOne u⟩ = 0 := by
  have happly : pairFormL 𝔇 hg ⟨dbarL u, dbarL_mem_zeroOne u⟩
      = ∑ j, ∫ z, pouCoeff 𝔇 j z * (𝔇.cutoffPullback j (dbarL u) z * g j z) := rfl
  rw [happly]
  -- replace the cutoff pullback of `∂̄u` by the planar `∂̄` of the chart read (P4a)
  have hcongr : ∀ j, (∫ z, pouCoeff 𝔇 j z * (𝔇.cutoffPullback j (dbarL u) z * g j z))
      = ∫ z, pouCoeff 𝔇 j z
          * (DbarDisk.dbar (fun ζ => u ((chartAt ℂ (𝔇.center j)).symm ζ)) z * g j z) := by
    intro j
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only
    by_cases hzU : z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X)
    · obtain ⟨x, hxU, rfl⟩ := hzU
      rw [cutoffPullback_dbarL 𝔇 hxU]
    · rw [show pouCoeff 𝔇 j z = 0 from Set.indicator_of_notMem hzU _, zero_mul, zero_mul]
  calc ∑ j, ∫ z, pouCoeff 𝔇 j z * (𝔇.cutoffPullback j (dbarL u) z * g j z)
      = ∑ j, ∫ z, pouCoeff 𝔇 j z
          * (DbarDisk.dbar (fun ζ => u ((chartAt ℂ (𝔇.center j)).symm ζ)) z * g j z) :=
        Finset.sum_congr rfl fun j _ => hcongr j
    _ = ∑ j, - ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (u ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) :=
        Finset.sum_congr rfl fun j _ =>
          integral_pouCoeff_dbarRead_mul 𝔇 u.contMDiff hg j
    _ = - ∑ j, ∑ k, ∫ z, pouCoeff 𝔇 k z
          * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
              * (u ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => congrArg Neg.neg <|
          Finset.sum_congr rfl fun k _ =>
            integral_overlapTerm_relocate 𝔇 u.contMDiff hg j k
    _ = - ∑ k, ∑ j, ∫ z, pouCoeff 𝔇 k z
          * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
              * (u ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) := by
        rw [Finset.sum_comm]
    _ = 0 := by
        rw [Finset.sum_eq_zero fun k _ => sum_integral_relocated_eq_zero 𝔇 u.contMDiff hg k,
          neg_zero]

/-- **P4 at the canonical slot**: `∮_X ∂̄u ∧ α = 0` for every global holomorphic 1-form. -/
theorem pairOmega_dbarL (u : SmoothCFunctions X) (α : HolomorphicOneForms X) :
    pairOmega 𝔇 ⟨dbarL u, dbarL_mem_zeroOne u⟩ α = 0 :=
  pairFormL_dbarL 𝔇 (isOneZeroCoeff_omegaCoeff 𝔇 α) u

/-! ## P5a — chart-lift plumbing for the nondegeneracy witness

The witness `(0,1)`-form of P5 is `σ = h·∂̄w` with `h, w` global smooth functions manufactured
from planar data in a single cover chart: the disk bump of the cover (promoted to a
`SmoothBumpFunction`) times the chart pullback.  Plus two planar atoms: `∂̄(conj) = 1` and the
constant-rescaling read of `cSmulForm`. -/

/-- The disk bump of cover index `j`, promoted to a manifold `SmoothBumpFunction` at the center
(the cover's `closedBall ⊆ target` field discharges the support condition). -/
noncomputable def diskSmoothBump (j : 𝔇.toFiniteCover.ι) :
    SmoothBumpFunction 𝓘(ℝ, ℂ) (𝔇.center j) where
  toContDiffBump := 𝔇.diskBump j
  closedBall_subset := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ, Set.inter_univ]
    exact 𝔇.diskBump_support_subset_target j

/-- The **chart lift** of a planar smooth function `F` over cover index `j`: the global smooth
function `x ↦ χⱼ(x)·F(eⱼ x)` with `χⱼ` the disk smooth bump — equal to `F ∘ eⱼ` on the cover
disk (`chartLift_symm_read`), supported in the chart source over the support of `F`
(`chartLift_ne_zero`). -/
noncomputable def chartLift (j : 𝔇.toFiniteCover.ι) (F : ℂ → ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : SmoothCFunctions X :=
  ⟨fun x => ((diskSmoothBump 𝔇 j) x : ℝ) • F (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j) x),
    (diskSmoothBump 𝔇 j).contMDiff_smul
      (hF.contMDiff.comp_contMDiffOn contMDiffOn_extChartAt)⟩

@[simp] theorem chartLift_apply (j : 𝔇.toFiniteCover.ι) (F : ℂ → ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : X) :
    chartLift 𝔇 j F hF x
      = ((diskSmoothBump 𝔇 j) x : ℝ) • F (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j) x) := rfl

/-- On the (chart image of the) cover disk, the chart lift reads back the planar function. -/
theorem chartLift_symm_read (j : 𝔇.toFiniteCover.ι) {F : ℂ → ℂ}
    {hF : ContDiff ℝ (⊤ : ℕ∞) F} {z : ℂ}
    (hz : z ∈ Metric.ball (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j) (𝔇.center j)) (𝔇.radius j)) :
    chartLift 𝔇 j F hF ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).symm z) = F z := by
  set e := extChartAt 𝓘(ℝ, ℂ) (𝔇.center j) with he
  have hztgt : z ∈ e.target := 𝔇.closedBall_subset_target j (Metric.ball_subset_closedBall hz)
  have hsrc : e.symm z ∈ e.source := e.map_target hztgt
  have hez : e (e.symm z) = z := e.right_inv hztgt
  have hchart : e.symm z ∈ (chartAt ℂ (𝔇.center j)).source := by
    rwa [he, extChartAt_source] at hsrc
  have h1 : (diskSmoothBump 𝔇 j) (e.symm z) = 1 := by
    refine (diskSmoothBump 𝔇 j).one_of_dist_le hchart ?_
    show dist (e (e.symm z)) (e (𝔇.center j)) ≤ 𝔇.radius j
    rw [hez]
    exact le_of_lt (Metric.mem_ball.mp hz)
  show ((diskSmoothBump 𝔇 j) (e.symm z) : ℝ) • F (e (e.symm z)) = F z
  rw [h1, hez, one_smul]

/-- A nonvanishing point of a chart lift lies in the chart source, with chart coordinate in the
support of the planar function. -/
theorem chartLift_ne_zero {j : 𝔇.toFiniteCover.ι} {F : ℂ → ℂ}
    {hF : ContDiff ℝ (⊤ : ℕ∞) F} {x : X} (hx : chartLift 𝔇 j F hF x ≠ 0) :
    x ∈ (chartAt ℂ (𝔇.center j)).source
      ∧ F (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j) x) ≠ 0 := by
  have hχ : (diskSmoothBump 𝔇 j) x ≠ 0 := by
    intro h0
    exact hx (by rw [chartLift_apply, h0]; simp)
  have hF0 : F (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j) x) ≠ 0 := by
    intro h0
    exact hx (by rw [chartLift_apply, h0, smul_zero])
  exact ⟨(diskSmoothBump 𝔇 j).support_subset_source (Function.mem_support.mpr hχ), hF0⟩

/-- The planar Wirtinger derivative of conjugation is `1`: `∂̄(conj) = 1`. -/
theorem dbar_conj (z : ℂ) : DbarDisk.dbar (fun w => (starRingEnd ℂ) w) z = 1 := by
  have hfun : (fun w : ℂ => (starRingEnd ℂ) w) = ⇑Complex.conjCLE :=
    funext fun w => (Complex.conjCLE_apply w).symm
  unfold DbarDisk.dbar
  rw [hfun, Complex.conjCLE.fderiv]
  simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The cutoff pullback of a `cSmulForm` rescaling reads the scalar at the surface point. -/
theorem cutoffPullback_cSmulForm (j : 𝔇.toFiniteCover.ι) (c : SmoothCFunctions X)
    (g : SmoothCOneForms X) (z : ℂ) :
    𝔇.cutoffPullback j (cSmulForm c g) z
      = c ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).symm z) * 𝔇.cutoffPullback j g z := by
  set y := (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).symm z with hy
  show ((𝔇.diskBump j) z : ℝ) • ((cSmulForm c g) y) ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) (𝔇.center j)) y) (1 : ℂ))
    = c y * (((𝔇.diskBump j) z : ℝ) • (g y) ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) (𝔇.center j)) y) (1 : ℂ)))
  rw [cSmulForm_apply, ContinuousLinearMap.smul_apply, smul_comm]
  rfl

/-! ## P5b — the single-chart collapse of the pairing integral

For a `(0,1)`-form supported (as a section) in a closed subset of ONE cover disk, the pairing
integral collapses to the single chart-`j₀` planar integral: relocate every PoU term to chart
`j₀` (the R4 relocation lemma) and reinsert `∑ ρ = 1`. -/

/-- If the section `σ` vanishes outside `S`, a nonvanishing value of `cutoffPullback j σ`
forces the chart point into `S` (and the planar point into the chart target). -/
theorem cutoffPullback_ne_zero {σ : SmoothCOneForms X} {S : Set X}
    (hsupp : ∀ y, y ∉ S → σ y = 0) {j : 𝔇.toFiniteCover.ι} {z : ℂ}
    (hz : 𝔇.cutoffPullback j σ z ≠ 0) :
    z ∈ (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).target
      ∧ (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).symm z ∈ S := by
  set y := (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).symm z with hy
  have hχ : (𝔇.diskBump j) z ≠ 0 := by
    intro h0
    refine hz ?_
    show ((𝔇.diskBump j) z : ℝ) • _ = 0
    rw [h0]
    simp
  have hztgt : z ∈ (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).target := by
    refine 𝔇.diskBump_support_subset_target j (Metric.ball_subset_closedBall ?_)
    rw [← (𝔇.diskBump j).support_eq]
    exact Function.mem_support.mpr hχ
  refine ⟨hztgt, ?_⟩
  by_contra hyS
  refine hz ?_
  show ((𝔇.diskBump j) z : ℝ) • (σ y) _ = 0
  rw [hsupp y hyS]
  simp

/-- **P5b — the single-chart collapse.**  If `σ` vanishes outside a closed `S ⊆ U j₀`, the
pairing integral is the single chart-`j₀` term:

  `resIntegral (σ̃·g) = ∫_ℂ σ̃_{j₀}·g_{j₀}`.

Each PoU summand vanishes off the `(l, j₀)` overlap image, relocates to chart `j₀`
(`setIntegral_overlap_relocate` at the weight `ρ_l`), and the weights reinsert to `1`. -/
theorem resIntegral_pairElem_of_support {σ : SmoothCOneForms X} (hσ : σ ∈ OneFormsZeroOne X)
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) {j₀ : 𝔇.toFiniteCover.ι}
    {S : Set X} (hS : IsClosed S) (hSU : S ⊆ (𝔇.U j₀ : Set X))
    (hsupp : ∀ y, y ∉ S → σ y = 0) :
    resIntegral 𝔇 (pairElem 𝔇 hσ hg) = ∫ z, pairCoeff 𝔇 σ g j₀ z := by
  set t := pairCoeff 𝔇 σ g with ht
  have htmem : IsOneOneCoeff 𝔇 t := pairCoeff_mem_oneOneCoeff 𝔇 hσ hg
  -- the compact planar trace of the section support in chart `j₀`
  have hScpt : IsCompact S := hS.isCompact
  have hK : IsCompact (chartMap 𝔇 j₀ '' S) := by
    refine hScpt.image_of_continuousOn ?_
    exact (chartAt ℂ (𝔇.center j₀)).continuousOn.mono fun y hy =>
      mem_chartSource_of_mem_U 𝔇 (hSU hy)
  -- a nonvanishing value of `t j₀` happens only on the planar trace
  have htj₀ : ∀ w, t j₀ w ≠ 0 → w ∈ chartMap 𝔇 j₀ '' S := by
    intro w hw
    have hcut : 𝔇.cutoffPullback j₀ σ w ≠ 0 := fun h0 => hw (by rw [ht]; simp [h0])
    obtain ⟨hwtgt, hyS⟩ := cutoffPullback_ne_zero 𝔇 hsupp hcut
    exact ⟨(extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀)).symm w, hyS, by
      show (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀)) _ = w
      exact (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀)).right_inv hwtgt⟩
  -- per cover index: localize to the overlap, relocate to chart `j₀`, re-extend
  have hterm : ∀ l, (∫ z, pouCoeff 𝔇 l z * t l z)
      = ∫ w, rhoC 𝔇 l ((chartAt ℂ (𝔇.center j₀)).symm w) * t j₀ w := by
    intro l
    -- step 1: the chart-`l` integrand vanishes off the `(l, j₀)` overlap image
    have hvan1 : ∀ z, z ∉ overlapImage 𝔇 l j₀ → pouCoeff 𝔇 l z * t l z = 0 := by
      intro z hz
      by_cases hzU : z ∈ chartMap 𝔇 l '' (𝔇.U l : Set X)
      · obtain ⟨y, hyU, rfl⟩ := hzU
        by_cases hcut : 𝔇.cutoffPullback l σ (chartMap 𝔇 l y) = 0
        · rw [ht]
          simp [hcut]
        · obtain ⟨-, hyS⟩ := cutoffPullback_ne_zero 𝔇 hsupp hcut
          have hsymm : (extChartAt 𝓘(ℝ, ℂ) (𝔇.center l)).symm (chartMap 𝔇 l y) = y :=
            (extChartAt 𝓘(ℝ, ℂ) (𝔇.center l)).left_inv (𝔇.subset_chart_source l hyU)
          rw [hsymm] at hyS
          exact absurd ⟨y, ⟨hyU, hSU hyS⟩, rfl⟩ hz
      · rw [show pouCoeff 𝔇 l z = 0 from Set.indicator_of_notMem hzU _, zero_mul]
    -- step 2: on the overlap image the PoU weight is the surface weight
    have hcongr1 : ∀ z ∈ overlapImage 𝔇 l j₀,
        pouCoeff 𝔇 l z * t l z
          = rhoC 𝔇 l ((chartAt ℂ (𝔇.center l)).symm z) * t l z := by
      rintro z ⟨y, hy, rfl⟩
      have hsymm : (chartAt ℂ (𝔇.center l)).symm (chartMap 𝔇 l y) = y :=
        (chartAt ℂ (𝔇.center l)).left_inv (mem_chartSource_of_mem_U 𝔇 hy.1)
      rw [pouCoeff_chartMap 𝔇 hy.1, hsymm]
    -- step 3: the chart-`j₀` integrand vanishes off the `(j₀, l)` overlap image
    have hvan2 : ∀ w, w ∉ overlapImage 𝔇 j₀ l →
        rhoC 𝔇 l ((chartAt ℂ (𝔇.center j₀)).symm w) * t j₀ w = 0 := by
      intro w hw
      by_cases htw : t j₀ w = 0
      · rw [htw, mul_zero]
      · obtain ⟨y, hyS, rfl⟩ := htj₀ w htw
        have hyU : y ∈ (𝔇.U j₀ : Set X) := hSU hyS
        have hsymm : (chartAt ℂ (𝔇.center j₀)).symm (chartMap 𝔇 j₀ y) = y :=
          (chartAt ℂ (𝔇.center j₀)).left_inv (mem_chartSource_of_mem_U 𝔇 hyU)
        rw [hsymm]
        have hyUl : y ∉ (𝔇.U l : Set X) := fun hyl => hw ⟨y, ⟨hyU, hyl⟩, rfl⟩
        have hsupp_l : y ∉ tsupport (cechPoU 𝔇 l) := fun hs =>
          hyUl (cechPoU_subordinate 𝔇 l hs)
        have hr : rhoC 𝔇 l y = 0 := by
          simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM,
            image_eq_zero_of_notMem_tsupport hsupp_l]
          rfl
        rw [hr, zero_mul]
    calc ∫ z, pouCoeff 𝔇 l z * t l z
        = ∫ z in overlapImage 𝔇 l j₀, pouCoeff 𝔇 l z * t l z :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hvan1).symm
      _ = ∫ z in overlapImage 𝔇 l j₀,
            rhoC 𝔇 l ((chartAt ℂ (𝔇.center l)).symm z) * t l z :=
          MeasureTheory.setIntegral_congr_fun
            (isOpen_overlapImage 𝔇 l j₀).measurableSet hcongr1
      _ = ∫ w in overlapImage 𝔇 j₀ l,
            rhoC 𝔇 l ((chartAt ℂ (𝔇.center j₀)).symm w) * t j₀ w :=
          setIntegral_overlap_relocate 𝔇 htmem l j₀ fun y => rhoC 𝔇 l y
      _ = ∫ w, rhoC 𝔇 l ((chartAt ℂ (𝔇.center j₀)).symm w) * t j₀ w :=
          setIntegral_eq_integral_of_forall_compl_eq_zero hvan2
  -- continuity + compact support of the relocated integrands (clearance off the planar trace)
  have htcont : ∀ w ∉ chartMap 𝔇 j₀ '' S, t j₀ w = 0 := fun w hw => by
    by_contra h0
    exact hw (htj₀ w h0)
  have hcont : ∀ l, Continuous fun w =>
      rhoC 𝔇 l ((chartAt ℂ (𝔇.center j₀)).symm w) * t j₀ w := by
    intro l
    rw [continuous_iff_continuousAt]
    intro w
    by_cases hwK : w ∈ chartMap 𝔇 j₀ '' S
    · obtain ⟨y, hyS, rfl⟩ := hwK
      have hyU : y ∈ (𝔇.U j₀ : Set X) := hSU hyS
      have hwtgt : chartMap 𝔇 j₀ y ∈ (chartAt ℂ (𝔇.center j₀)).target :=
        (chartAt ℂ (𝔇.center j₀)).map_source (mem_chartSource_of_mem_U 𝔇 hyU)
      refine ContinuousAt.mul ?_ (ContinuousAt.mul ?_ ?_)
      · exact (contDiffAt_chartSymmRead (rhoC 𝔇 l).contMDiff hwtgt).continuousAt
      · exact (𝔇.contDiff_cutoffPullback j₀ σ).continuous.continuousAt
      · exact (hg.1 j₀ y hyU).continuousAt
    · have hev : (fun w => rhoC 𝔇 l ((chartAt ℂ (𝔇.center j₀)).symm w) * t j₀ w)
          =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hwK] with w' hw'
        rw [htcont w' hw', mul_zero]
      exact continuousAt_const.congr hev.symm
  have hsupport : ∀ l, HasCompactSupport fun w =>
      rhoC 𝔇 l ((chartAt ℂ (𝔇.center j₀)).symm w) * t j₀ w := by
    intro l
    refine HasCompactSupport.intro hK fun w hw => ?_
    rw [htcont w hw, mul_zero]
  -- assemble: sum the relocated terms and reinsert `∑ ρ = 1`
  calc resIntegral 𝔇 (pairElem 𝔇 hσ hg)
      = ∑ l, ∫ z, pouCoeff 𝔇 l z * t l z := rfl
    _ = ∑ l, ∫ w, rhoC 𝔇 l ((chartAt ℂ (𝔇.center j₀)).symm w) * t j₀ w :=
        Finset.sum_congr rfl fun l _ => hterm l
    _ = ∫ w, ∑ l, rhoC 𝔇 l ((chartAt ℂ (𝔇.center j₀)).symm w) * t j₀ w :=
        (integral_finsetSum Finset.univ fun l _ =>
          (hcont l).integrable_of_hasCompactSupport (hsupport l)).symm
    _ = ∫ w, t j₀ w := by
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        dsimp only
        rw [← Finset.sum_mul, sum_rhoC_apply, one_mul]

/-! ## P5c — nondegeneracy: a nonzero form pairs nontrivially -/

/-- A nonzero holomorphic 1-form has a nonvanishing chart coefficient **in some cover chart**:
the nonvanishing own-chart coefficient point (`exists_localRep_self_ne_zero`) transferred
through the chart-invariant form order (`formOrderW_chart_invariant`: order `0` in the own
chart ⟹ order `0`, hence value `≠ 0`, in the covering chart). -/
theorem exists_omegaCoeff_ne_zero_of_ne_zero (α : HolomorphicOneForms X) (hα : α ≠ 0) :
    ∃ (j₀ : 𝔇.toFiniteCover.ι) (a : X), a ∈ (𝔇.U j₀ : Set X) ∧
      omegaCoeff 𝔇 α j₀ (chartMap 𝔇 j₀ a) ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_localRep_self_ne_zero α hα
  obtain ⟨j₀, haU⟩ : ∃ j₀, a ∈ (𝔇.U j₀ : Set X) := by
    have hmem : a ∈ ((⨆ i, 𝔇.U i : Opens X) : Set X) := by
      rw [𝔇.toFiniteCover.covers]
      trivial
    exact Opens.mem_iSup.mp hmem
  -- order `0` at `a` in `a`'s own chart (the coefficient value there is `localRep α a a ≠ 0`)
  have hself : a ∈ (chartAt ℂ a).source := mem_chart_source ℂ a
  have htgt_a : (chartAt ℂ a) a ∈ (chartAt ℂ a).target := (chartAt ℂ a).map_source hself
  have han_a : AnalyticAt ℂ (coeffAt α a) ((chartAt ℂ a) a) := coeffAt_analyticAt α a htgt_a
  have hval : coeffAt α a ((chartAt ℂ a) a) ≠ 0 := by
    show Jacobians.Montel.localRep α a ((chartAt ℂ a).symm ((chartAt ℂ a) a)) ≠ 0
    rw [(chartAt ℂ a).left_inv hself]
    exact ha
  have hmero_a : meromorphicOrderAt (coeffAt α a) ((chartAt ℂ a) a) = ((0 : ℤ) : WithTop ℤ) := by
    rw [han_a.meromorphicOrderAt_eq, han_a.analyticOrderAt_eq_zero.mpr hval]
    rfl
  have hord_a : (holToMero α).formOrderW a = ((0 : ℤ) : WithTop ℤ) := by
    have h := formOrderW_chart_invariant (holToMero α) a a hself
    have hcoeff : formCoeff (holToMero α).toFun a = coeffAt α a := formCoeff_holToSection α a
    rw [hcoeff] at h
    rw [h, hmero_a]
  -- transfer to the covering chart: order `0` there, hence value `≠ 0`
  have hsrc : a ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 haU
  have htgt : chartMap 𝔇 j₀ a ∈ (chartAt ℂ (𝔇.center j₀)).target :=
    (chartAt ℂ (𝔇.center j₀)).map_source hsrc
  have han : AnalyticAt ℂ (coeffAt α (𝔇.center j₀)) (chartMap 𝔇 j₀ a) :=
    coeffAt_analyticAt α (𝔇.center j₀) htgt
  have hmero : meromorphicOrderAt (coeffAt α (𝔇.center j₀)) (chartMap 𝔇 j₀ a)
      = ((0 : ℤ) : WithTop ℤ) := by
    have h := formOrderW_chart_invariant (holToMero α) (𝔇.center j₀) a hsrc
    have hcoeff : formCoeff (holToMero α).toFun (𝔇.center j₀) = coeffAt α (𝔇.center j₀) :=
      formCoeff_holToSection α (𝔇.center j₀)
    rw [hcoeff, hord_a] at h
    exact h.symm
  have hord : analyticOrderAt (coeffAt α (𝔇.center j₀)) (chartMap 𝔇 j₀ a) = 0 := by
    rw [han.meromorphicOrderAt_eq] at hmero
    cases hcase : analyticOrderAt (coeffAt α (𝔇.center j₀)) (chartMap 𝔇 j₀ a) with
    | top =>
      rw [hcase, ENat.map_top] at hmero
      exact absurd hmero.symm WithTop.coe_ne_top
    | coe n =>
      rw [hcase, ENat.map_coe] at hmero
      have hn : (n : ℤ) = 0 := WithTop.coe_inj.mp hmero
      exact_mod_cast hn
  exact ⟨j₀, a, haU, by simpa [omegaCoeff] using han.analyticOrderAt_eq_zero.mp hord⟩

/-- A point of the coordinate disk pulls back into the cover set. -/
theorem symm_mem_U_of_mem_ball {j : 𝔇.toFiniteCover.ι} {w : ℂ}
    (hw : w ∈ Metric.ball (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j) (𝔇.center j)) (𝔇.radius j)) :
    (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).symm w ∈ (𝔇.U j : Set X) := by
  have hwt : w ∈ (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).target :=
    𝔇.closedBall_subset_target j (Metric.ball_subset_closedBall hw)
  rw [𝔇.isDisk j]
  refine ⟨?_, (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).map_target hwt⟩
  rw [Set.mem_preimage, (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).right_inv hwt]
  exact hw

/-- **P5 nondegeneracy (positive-real form) — every nonzero holomorphic 1-form pairs to a
positive real against some smooth `(0,1)`-form.**  The witness is the one-chart bump form
`σ = h·∂̄w` (with `h, w` chart lifts of `χ₂·conj f` and `χ₁·conj z`): its pairing against `α`
collapses to the single planar integral `∫ χ₂·|f|² > 0` at a disk where the coefficient `f` of
`α` does not vanish.  The positive-real (not merely nonzero) value is what defeats arbitrary
`ℝ`-linear annihilators in the Gram-surjectivity argument (`pairPeriodL_surjective`). -/
theorem exists_pairOmega_pos (α : HolomorphicOneForms X) (hα : α ≠ 0) :
    ∃ σ : ↥(OneFormsZeroOne X), ∃ r : ℝ, 0 < r ∧ pairOmega 𝔇 σ α = (r : ℂ) := by
  classical
  obtain ⟨j₀, a, haU, hf0⟩ := exists_omegaCoeff_ne_zero_of_ne_zero 𝔇 α hα
  set f : ℂ → ℂ := omegaCoeff 𝔇 α j₀ with hf
  set e := extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀) with he
  set za := chartMap 𝔇 j₀ a with hza
  set ballc := Metric.ball (e (𝔇.center j₀)) (𝔇.radius j₀) with hballc
  -- conjugation is real-smooth
  have hconjfun : (fun w : ℂ => (starRingEnd ℂ) w) = ⇑Complex.conjCLE :=
    funext fun w => (Complex.conjCLE_apply w).symm
  have hconj : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ => (starRingEnd ℂ) w) := by
    rw [hconjfun]
    exact Complex.conjCLE.contDiff
  -- the chart target membership of disk points, and analyticity of `f` there
  have hball_tgt : ∀ {w : ℂ}, w ∈ ballc → w ∈ e.target := fun {w} hw =>
    𝔇.closedBall_subset_target j₀ (Metric.ball_subset_closedBall hw)
  have hchart_tgt : ∀ {w : ℂ}, w ∈ ballc → w ∈ (chartAt ℂ (𝔇.center j₀)).target := by
    intro w hw
    have hyU : e.symm w ∈ (𝔇.U j₀ : Set X) := symm_mem_U_of_mem_ball 𝔇 hw
    have h := (chartAt ℂ (𝔇.center j₀)).map_source (mem_chartSource_of_mem_U 𝔇 hyU)
    rwa [show (chartAt ℂ (𝔇.center j₀)) (e.symm w) = w from e.right_inv (hball_tgt hw)] at h
  have hfan : ∀ {w : ℂ}, w ∈ ballc → AnalyticAt ℂ f w := fun {w} hw =>
    coeffAt_analyticAt α (𝔇.center j₀) (hchart_tgt hw)
  -- the working disk: inside the coordinate disk AND inside `{f ≠ 0}`
  have hza_ball : za ∈ ballc := by
    have h := haU
    rw [𝔇.isDisk j₀] at h
    exact h.1
  have hOopen : IsOpen (ballc ∩ f ⁻¹' {0}ᶜ) := by
    refine ContinuousOn.isOpen_inter_preimage ?_ Metric.isOpen_ball isOpen_compl_singleton
    intro w hw
    exact (hfan hw).continuousAt.continuousWithinAt
  have hzaO : za ∈ ballc ∩ f ⁻¹' {0}ᶜ := ⟨hza_ball, hf0⟩
  obtain ⟨ε, hε, hball_sub⟩ := Metric.isOpen_iff.mp hOopen za hzaO
  -- the two planar bumps and the planar data
  set χ₂ : ContDiffBump za := ⟨ε / 8, ε / 4, by positivity, by linarith⟩ with hχ₂
  set χ₁ : ContDiffBump za := ⟨ε / 4, ε / 2, by positivity, by linarith⟩ with hχ₁
  set W : ℂ → ℂ := fun w => (χ₁ w : ℝ) • (starRingEnd ℂ) w with hW
  set H : ℂ → ℂ := fun w => (χ₂ w : ℝ) • (starRingEnd ℂ) (f w) with hH
  have hsub₄ : Metric.ball za (ε / 4) ⊆ Metric.ball za ε := Metric.ball_subset_ball (by linarith)
  have hsub₄c : Metric.closedBall za (ε / 4) ⊆ Metric.ball za ε :=
    Metric.closedBall_subset_ball (by linarith)
  have hWsm : ContDiff ℝ (⊤ : ℕ∞) W := χ₁.contDiff.smul hconj
  have hHsm : ContDiff ℝ (⊤ : ℕ∞) H := by
    rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hw : w ∈ Metric.ball za ε
    · have hwc : w ∈ ballc := (hball_sub hw).1
      exact χ₂.contDiff.contDiffAt.smul (hconj.contDiffAt.comp w
        (((hfan hwc).restrictScalars (𝕜 := ℝ)).contDiffAt))
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      have hw4 : w ∉ Metric.closedBall za (ε / 4) := fun hc => hw (hsub₄c hc)
      filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hw4] with w' hw'
      have hχ0 : χ₂ w' = 0 := by
        rw [← Function.notMem_support, χ₂.support_eq]
        exact fun hc => hw' (Metric.ball_subset_closedBall hc)
      rw [hH]
      dsimp only
      rw [hχ0]
      simp
  -- the global witness `(0,1)`-form
  set wfn := chartLift 𝔇 j₀ W hWsm with hwfn
  set hfn := chartLift 𝔇 j₀ H hHsm with hhfn
  set σ₀ : SmoothCOneForms X := cSmulForm hfn (dbarL wfn) with hσ₀
  have hσ₀mem : σ₀ ∈ OneFormsZeroOne X := cSmulForm_mem_zeroOne hfn (dbarL_mem_zeroOne wfn)
  -- the support control: `σ₀` lives over the closed `ε/4`-disk inside `U j₀`
  have hsupp_gen : ∀ y, σ₀ y ≠ 0 → ∃ w' ∈ Metric.ball za (ε / 4), y = e.symm w' := by
    intro y hy
    have hfny : hfn y ≠ 0 := by
      intro h0
      refine hy ?_
      rw [hσ₀, cSmulForm_apply, h0]
      exact zero_smul ℂ ((dbarL wfn) y)
    obtain ⟨hysrc, hHy⟩ := chartLift_ne_zero 𝔇 hfny
    have hχ2y : χ₂ (e y) ≠ 0 := by
      intro h0
      refine hHy ?_
      show H (e y) = 0
      rw [hH]
      dsimp only
      rw [h0]
      simp
    have hyball : e y ∈ Metric.ball za (ε / 4) := by
      rw [← χ₂.support_eq]
      exact Function.mem_support.mpr hχ2y
    refine ⟨e y, hyball, ?_⟩
    have hysrc' : y ∈ e.source := by
      rw [he, extChartAt_source]
      exact hysrc
    exact (e.left_inv hysrc').symm
  set S : Set X := e.symm '' Metric.closedBall za (ε / 4) with hSdef
  have hScl : IsClosed S := by
    refine IsCompact.isClosed ?_
    refine (isCompact_closedBall za (ε / 4)).image_of_continuousOn ?_
    exact (continuousOn_extChartAt_symm (𝔇.center j₀)).mono fun w hw =>
      hball_tgt ((hball_sub (hsub₄c hw)).1)
  have hSU : S ⊆ (𝔇.U j₀ : Set X) := by
    rintro y ⟨w', hw', rfl⟩
    exact symm_mem_U_of_mem_ball 𝔇 ((hball_sub (hsub₄c hw')).1)
  have hsupp : ∀ y, y ∉ S → σ₀ y = 0 := by
    intro y hyS
    by_contra hy
    obtain ⟨w', hw', rfl⟩ := hsupp_gen y hy
    exact hyS ⟨w', Metric.ball_subset_closedBall hw', rfl⟩
  -- pointwise: the single-chart integrand is `χ₂·|f|²`
  have hpt : ∀ z, pairCoeff 𝔇 σ₀ (omegaCoeff 𝔇 α) j₀ z
      = ((χ₂ z * normSq (f z) : ℝ) : ℂ) := by
    intro z
    by_cases hzc : z ∈ ballc
    · -- inside the coordinate disk: read everything back through the chart
      have hcut : 𝔇.cutoffPullback j₀ σ₀ z = H z * 𝔇.cutoffPullback j₀ (dbarL wfn) z := by
        rw [hσ₀, cutoffPullback_cSmulForm]
        congr 1
        exact chartLift_symm_read 𝔇 j₀ hzc
      by_cases hz4 : z ∈ Metric.ball za (ε / 4)
      · -- the bump core: `∂̄w` reads `∂̄(conj) = 1`
        have hyU : e.symm z ∈ (𝔇.U j₀ : Set X) := symm_mem_U_of_mem_ball 𝔇 hzc
        have hzx' : chartMap 𝔇 j₀ (e.symm z) = z := e.right_inv (hball_tgt hzc)
        have hcdb : 𝔇.cutoffPullback j₀ (dbarL wfn) z = 1 := by
          have h1 := cutoffPullback_dbarL 𝔇 (u := wfn) hyU
          rw [hzx'] at h1
          rw [h1]
          have hev : (fun ζ => wfn ((chartAt ℂ (𝔇.center j₀)).symm ζ))
              =ᶠ[𝓝 z] fun w => (starRingEnd ℂ) w := by
            filter_upwards [Metric.isOpen_ball.mem_nhds hzc,
              Metric.isOpen_ball.mem_nhds hz4] with ζ hζc hζ4
            have hread : wfn ((chartAt ℂ (𝔇.center j₀)).symm ζ) = W ζ :=
              chartLift_symm_read 𝔇 j₀ hζc
            rw [hread, hW]
            dsimp only
            rw [χ₁.one_of_mem_closedBall (Metric.ball_subset_closedBall hζ4)]
            simp
          rw [dbar_congr_of_eventuallyEq hev, dbar_conj]
        rw [pairCoeff_apply, hcut, hcdb, mul_one, hH]
        dsimp only
        calc ((χ₂ z : ℝ) • (starRingEnd ℂ) (f z)) * f z
            = (χ₂ z : ℂ) * (f z * (starRingEnd ℂ) (f z)) := by
              rw [Complex.real_smul]
              ring
          _ = (χ₂ z : ℂ) * ((normSq (f z) : ℝ) : ℂ) := by rw [Complex.mul_conj]
          _ = ((χ₂ z * normSq (f z) : ℝ) : ℂ) := by
              push_cast
              ring
      · -- inside the disk but outside the bump: both sides vanish
        have hχ0 : χ₂ z = 0 := by
          rw [← Function.notMem_support, χ₂.support_eq]
          exact hz4
        rw [pairCoeff_apply, hcut, hH]
        dsimp only
        rw [hχ0]
        simp
    · -- outside the coordinate disk: the section support forces the cutoff to vanish
      have hz4 : z ∉ Metric.ball za (ε / 4) := fun hc => hzc ((hball_sub (hsub₄ hc)).1)
      have hχ0 : χ₂ z = 0 := by
        rw [← Function.notMem_support, χ₂.support_eq]
        exact hz4
      have hcut0 : 𝔇.cutoffPullback j₀ σ₀ z = 0 := by
        by_contra hne
        obtain ⟨hztgt, hzS⟩ := cutoffPullback_ne_zero 𝔇 hsupp hne
        obtain ⟨w', hw', heq⟩ := hzS
        have hw't : w' ∈ e.target := hball_tgt ((hball_sub (hsub₄c hw')).1)
        have : z = w' := by
          have h1 : e (e.symm z) = z := e.right_inv hztgt
          have h2 : e (e.symm w') = w' := e.right_inv hw't
          rw [← h1, ← heq]
          exact h2
        exact hzc (this ▸ (hball_sub (hsub₄c hw')).1)
      rw [pairCoeff_apply, hcut0, zero_mul, hχ0]
      simp
  -- positivity of the planar integral `∫ χ₂·|f|²`
  set G : ℂ → ℝ := fun z => χ₂ z * normSq (f z) with hG
  have hGnn : ∀ z, 0 ≤ G z := fun z => mul_nonneg χ₂.nonneg (normSq_nonneg _)
  have hGcont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro w
    by_cases hw : w ∈ Metric.closedBall za (ε / 4)
    · have hwc : w ∈ ballc := (hball_sub (hsub₄c hw)).1
      exact (χ₂.continuous.continuousAt).mul
        (Complex.continuous_normSq.continuousAt.comp (hfan hwc).continuousAt)
    · have hev : G =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hw] with w' hw'
        have hχ0 : χ₂ w' = 0 := by
          rw [← Function.notMem_support, χ₂.support_eq]
          exact fun hc => hw' (Metric.ball_subset_closedBall hc)
        rw [hG]
        dsimp only
        rw [hχ0, zero_mul]
      exact continuousAt_const.congr hev.symm
  have hGsupp : HasCompactSupport G := χ₂.hasCompactSupport.mul_right
  have hGint : Integrable G := hGcont.integrable_of_hasCompactSupport hGsupp
  have hsupport_sub : Metric.ball za (ε / 8) ⊆ Function.support G := by
    intro z hz
    have hχpos : 0 < χ₂ z := χ₂.pos_of_mem_ball
      (Metric.ball_subset_ball (show ε / 8 ≤ χ₂.rOut from by rw [hχ₂]; linarith) hz)
    have hfz : f z ≠ 0 := (hball_sub (Metric.ball_subset_ball (by linarith) hz)).2
    exact Function.mem_support.mpr (ne_of_gt (mul_pos hχpos (normSq_pos.mpr hfz)))
  have hpos : 0 < ∫ z, G z :=
    (integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hGnn) hGint).mpr
      (lt_of_lt_of_le (Metric.measure_ball_pos volume za (by positivity))
        (measure_mono hsupport_sub))
  refine ⟨⟨σ₀, hσ₀mem⟩, ∫ z, G z, hpos, ?_⟩
  rw [pairOmega_apply,
    resIntegral_pairElem_of_support 𝔇 hσ₀mem (isOneZeroCoeff_omegaCoeff 𝔇 α) hScl hSU hsupp,
    integral_congr_ae (Eventually.of_forall hpt), integral_complex_ofReal]

/-- **P5 nondegeneracy — every nonzero holomorphic 1-form pairs nontrivially against some
smooth `(0,1)`-form** (the `≠ 0` corollary of the positive-real form). -/
theorem exists_pairOmega_ne_zero (α : HolomorphicOneForms X) (hα : α ≠ 0) :
    ∃ σ : ↥(OneFormsZeroOne X), pairOmega 𝔇 σ α ≠ 0 := by
  obtain ⟨σ, r, hr, hval⟩ := exists_pairOmega_pos 𝔇 α hα
  exact ⟨σ, by rw [hval]; exact_mod_cast ne_of_gt hr⟩

/-! ## P5d — slot linearity, the period functional, and Gram surjectivity -/

/-- `coeffAt` is additive in the form (the `Montel.localRep` layer is). -/
theorem coeffAt_add (α β : HolomorphicOneForms X) (a : X) (z : ℂ) :
    coeffAt (α + β) a z = coeffAt α a z + coeffAt β a z :=
  Jacobians.Montel.localRep_add α β a ((chartAt ℂ a).symm z)

/-- `coeffAt` is `ℂ`-homogeneous in the form (the `Montel.localRep` layer is). -/
theorem coeffAt_smul (c : ℂ) (α : HolomorphicOneForms X) (a : X) (z : ℂ) :
    coeffAt (c • α) a z = c * coeffAt α a z :=
  Jacobians.Montel.localRep_smul c α a ((chartAt ℂ a).symm z)

/-- **Slot additivity**: `∫_X σ∧(α+β) = ∫_X σ∧α + ∫_X σ∧β`. -/
theorem pairOmega_slot_add (σ : ↥(OneFormsZeroOne X)) (α β : HolomorphicOneForms X) :
    pairOmega 𝔇 σ (α + β) = pairOmega 𝔇 σ α + pairOmega 𝔇 σ β := by
  have helem : pairElem 𝔇 σ.2 (isOneZeroCoeff_omegaCoeff 𝔇 (α + β))
      = pairElem 𝔇 σ.2 (isOneZeroCoeff_omegaCoeff 𝔇 α)
        + pairElem 𝔇 σ.2 (isOneZeroCoeff_omegaCoeff 𝔇 β) := by
    apply Subtype.ext
    show pairCoeff 𝔇 (σ : SmoothCOneForms X) (omegaCoeff 𝔇 (α + β))
        = pairCoeff 𝔇 (σ : SmoothCOneForms X) (omegaCoeff 𝔇 α)
          + pairCoeff 𝔇 (σ : SmoothCOneForms X) (omegaCoeff 𝔇 β)
    funext j z
    show 𝔇.cutoffPullback j σ z * coeffAt (α + β) (𝔇.center j) z
        = 𝔇.cutoffPullback j σ z * coeffAt α (𝔇.center j) z
          + 𝔇.cutoffPullback j σ z * coeffAt β (𝔇.center j) z
    rw [coeffAt_add]
    ring
  rw [pairOmega_apply, pairOmega_apply, pairOmega_apply, helem, map_add]

/-- **Slot `ℂ`-homogeneity**: `∫_X σ∧(c•α) = c·∫_X σ∧α`. -/
theorem pairOmega_slot_smul (σ : ↥(OneFormsZeroOne X)) (c : ℂ) (α : HolomorphicOneForms X) :
    pairOmega 𝔇 σ (c • α) = c * pairOmega 𝔇 σ α := by
  have helem : pairElem 𝔇 σ.2 (isOneZeroCoeff_omegaCoeff 𝔇 (c • α))
      = c • pairElem 𝔇 σ.2 (isOneZeroCoeff_omegaCoeff 𝔇 α) := by
    apply Subtype.ext
    show pairCoeff 𝔇 (σ : SmoothCOneForms X) (omegaCoeff 𝔇 (c • α))
        = c • pairCoeff 𝔇 (σ : SmoothCOneForms X) (omegaCoeff 𝔇 α)
    funext j z
    show 𝔇.cutoffPullback j σ z * coeffAt (c • α) (𝔇.center j) z
        = c * (𝔇.cutoffPullback j σ z * coeffAt α (𝔇.center j) z)
    rw [coeffAt_smul]
    ring
  rw [pairOmega_apply, pairOmega_apply, helem, map_smul, smul_eq_mul]

/-- **P3′ — the pairing as a `ℂ`-linear functional in the holomorphic slot.** -/
noncomputable def pairOmegaSlotL (σ : ↥(OneFormsZeroOne X)) :
    HolomorphicOneForms X →ₗ[ℂ] ℂ where
  toFun α := pairOmega 𝔇 σ α
  map_add' := pairOmega_slot_add 𝔇 σ
  map_smul' c α := by rw [pairOmega_slot_smul 𝔇 σ c α, RingHom.id_apply, smul_eq_mul]

@[simp] theorem pairOmegaSlotL_apply (σ : ↥(OneFormsZeroOne X)) (α : HolomorphicOneForms X) :
    pairOmegaSlotL 𝔇 σ α = pairOmega 𝔇 σ α := rfl

/-- **P5 — the concrete period functional** `Λ = (σ ↦ ∫_X σ∧ωᵢ)ᵢ` against a finite family of
holomorphic 1-forms: the `LinearMap.pi` bundle of `pairFormL` at the chart-coefficient
families `omegaCoeff 𝔇 (b i)`. -/
noncomputable def pairPeriodL {n : ℕ} (b : Fin n → HolomorphicOneForms X) :
    ↥(OneFormsZeroOne X) →ₗ[ℝ] (Fin n → ℂ) :=
  LinearMap.pi fun i => pairFormL 𝔇 (isOneZeroCoeff_omegaCoeff 𝔇 (b i))

@[simp] theorem pairPeriodL_apply {n : ℕ} (b : Fin n → HolomorphicOneForms X)
    (σ : ↥(OneFormsZeroOne X)) (i : Fin n) :
    pairPeriodL 𝔇 b σ i = pairOmega 𝔇 σ (b i) := rfl

/-- **P5 — Gram surjectivity of the period functional** at a basis of `H⁰(X, Ω¹)`.

If `Λ = (pairOmega · (b i))ᵢ` missed a vector, a nonzero `ℝ`-linear functional `ℓ` would
annihilate its range.  Reading `ℓ` as `v ↦ (∑ᵢ cᵢvᵢ).re` and folding the sum through slot
linearity, `ℓ∘Λ = σ ↦ (pairOmega σ ω).re` with `α₀ = ∑ᵢ cᵢ•(b i) ≠ 0` — but the bump witness
of `exists_pairOmega_pos` pairs against `α₀` to a **positive real**, contradiction. -/
theorem pairPeriodL_surjective (b : Module.Basis (Fin (kirovGenus X)) ℂ (HolomorphicOneForms X)) :
    Function.Surjective (pairPeriodL 𝔇 (⇑b)) := by
  classical
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨ℓ, hℓne, hℓmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr hne) inferInstance
  -- `ℓ` annihilates every period vector
  have hann : ∀ τ : ↥(OneFormsZeroOne X), ℓ (pairPeriodL 𝔇 (⇑b) τ) = 0 := by
    intro τ
    have hmem : ℓ (pairPeriodL 𝔇 (⇑b) τ)
        ∈ (LinearMap.range (pairPeriodL 𝔇 (⇑b))).map ℓ :=
      Submodule.mem_map_of_mem (LinearMap.mem_range_self _ τ)
    rw [hℓmap] at hmem
    exact (Submodule.mem_bot ℝ).mp hmem
  -- read `ℓ` as `v ↦ (∑ᵢ cᵢvᵢ).re`
  set c : Fin (kirovGenus X) → ℂ := fun i =>
    ((ℓ (Pi.single i 1) : ℝ) : ℂ) - ((ℓ (Pi.single i Complex.I) : ℝ) : ℂ) * Complex.I with hc
  have hsingle : ∀ (i : Fin (kirovGenus X)) (w : ℂ), ℓ (Pi.single i w) = (c i * w).re := by
    intro i w
    have hw : (Pi.single i w : Fin (kirovGenus X) → ℂ)
        = w.re • (Pi.single i (1 : ℂ) : Fin (kirovGenus X) → ℂ)
          + w.im • (Pi.single i Complex.I : Fin (kirovGenus X) → ℂ) := by
      rw [← Pi.single_smul, ← Pi.single_smul, ← Pi.single_add]
      congr 1
      rw [Complex.real_smul, Complex.real_smul, mul_one]
      exact (Complex.re_add_im w).symm
    rw [hw, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp only [hc, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_im,
      Complex.sub_im, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hdecomp : ∀ v : Fin (kirovGenus X) → ℂ, ℓ v = (∑ i, c i * v i).re := by
    intro v
    rw [Complex.re_sum]
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hsingle i (v i)
  -- the annihilating holomorphic form is nonzero …
  set α₀ : HolomorphicOneForms X := ∑ i, c i • b i with hα₀
  have hα₀ne : α₀ ≠ 0 := by
    intro h0
    have hc0 : ∀ i, c i = 0 :=
      Fintype.linearIndependent_iff.mp b.linearIndependent c (hα₀.symm.trans h0)
    apply hℓne
    apply LinearMap.ext
    intro v
    rw [hdecomp v]
    simp [hc0]
  -- … so the positive-real bump witness contradicts the annihilation
  obtain ⟨σ, r, hr, hval⟩ := exists_pairOmega_pos 𝔇 α₀ hα₀ne
  have hfold : ∑ i, c i * pairPeriodL 𝔇 (⇑b) σ i = pairOmega 𝔇 σ α₀ := by
    calc ∑ i, c i * pairPeriodL 𝔇 (⇑b) σ i
        = ∑ i, pairOmegaSlotL 𝔇 σ (c i • b i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul, smul_eq_mul]
          rfl
      _ = pairOmegaSlotL 𝔇 σ (∑ i, c i • b i) :=
          (map_sum (pairOmegaSlotL 𝔇 σ) (fun i => c i • b i) Finset.univ).symm
      _ = pairOmega 𝔇 σ α₀ := by rw [← hα₀, pairOmegaSlotL_apply]
  have hcontr : ℓ (pairPeriodL 𝔇 (⇑b) σ) = r := by
    rw [hdecomp, hfold, hval, Complex.ofReal_re]
  rw [hann σ] at hcontr
  exact absurd hcontr.symm (ne_of_gt hr)

/-- **P6 — THE `∂̄`-SOLVABILITY THEOREM** (Forster 19.10): a smooth `(0,1)`-form whose period
pairing `∫_X σ∧α` vanishes against **every** global holomorphic 1-form is `∂̄`-exact.

Composition of the S-block's abstract dimension-count criterion
(`mem_dbarImage_of_periodFunctional`, S4) with the Stokes kill (`pairOmega_dbarL`, P4) and
Gram surjectivity (`pairPeriodL_surjective`, P5) at a finite basis of `H⁰(X, Ω¹)`
(`Module.finBasis`, dimension `kirovGenus X` by definition). -/
theorem dbar_solvable_of_pairOmega_eq_zero (σ : ↥(OneFormsZeroOne X))
    (hσ : ∀ α : HolomorphicOneForms X, pairOmega 𝔇 σ α = 0) :
    ∃ u : SmoothCFunctions X, dbarL u = (σ : SmoothCOneForms X) := by
  let b : Module.Basis (Fin (kirovGenus X)) ℂ (HolomorphicOneForms X) :=
    Module.finBasis ℂ (HolomorphicOneForms X)
  exact mem_dbarImage_of_periodFunctional (pairPeriodL 𝔇 (⇑b))
    (fun u => funext fun i => pairOmega_dbarL 𝔇 u (b i))
    (pairPeriodL_surjective 𝔇 b) σ (funext fun i => hσ (b i))

end Jacobians.Dolbeault.FineResidue
