/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FineResidue.Descent
import KirovDolbeault.Dolbeault.FineResidue.MeroVanish

/-!
# R7b — `vanish_coboundary` at general `K`: the K-point coboundary leg closed

This file closes gap §1 of `docs/planning/R7_BLOCKER.md`: the residue functional kills **every**
`B¹(𝒪_K)`-coboundary, for any divisor `K` whose poles the cover isolates (`SeparatesPoles` +
covering) and whose positive part the `dz`-slot matches (`g j₀` vanishes to order `≥ K a` at
each K-point — true for the chart coefficients of `ω₀` with `K = div ω₀`).  Together with the
R6 bridge (`r6Outputs_holds`, instantiating `Descent.R6Outputs` from the landed `MLTie`), the
port's isolated Cousin interface `CousinResidueData 𝔇.toFiniteCover K` now assembles from the
**single** remaining hypothesis `CupMLWitness` (`cousinResidueData_of_slotMatches`).

## The principal-part decomposition, avoided

`R7_BLOCKER.md` §1 sketches a Laurent principal-part split of `sections0 K` cochains.  We avoid
it entirely: restrict each 0-cochain germ `f i` to `U i` minus the K-points (`offPos K`), where
it is an honest `𝒪`-class, and `holoFn`-extract (`vanishFn`).  The extraction is a coboundary
representative of the cocycle off the K-points (`SeparatesPoles` keeps the K-points off the
overlaps), smooth/holomorphic off the K-points — exactly the bad-point shape of the R6b engine
`resFunctional_eq_zero_of_mero_coboundary`.  The engine's `SlotProductExtendsAt` input is the
**product-germ trick**: with `F` a representative of `f j₀` and `Gp` the slot pullback
`g j₀ ∘ chartMap`, the product `F·Gp` has order `≥ −K a + K a = 0` at the K-point `a` (the slot
zero cancels the pole), so it is an `𝒪`-class on `U j₀` minus the *other* K-points, and its
`holoFn` **is** the analytic extension `q` — no Laurent coefficients anywhere.

## Main declarations

* `r6Outputs_holds` — the two-line R6 bridge: `MLTie` inhabits `Descent.R6Outputs`.
* `posSupp K` / `offPos K` — the K-points and their open complement.
* `exists_isolated_of_separatesPoles` — pole separation + covering isolate every K-point.
* `vanishFn` — the off-K-points `holoFn` extraction of a `sections0 K` 0-cochain.
* `slotProductExtendsAt_vanishFn` — the product-germ trick supplies the engine input.
* `resCocycle_vanish_coboundary` — **the headline**: full coboundary vanishing at general `K`.
* `resH1_of_slotMatches` — the unconditional `liftQ` descent to `cechH1 K`.
* `cousinResidueData_of_slotMatches` — `CousinResidueData` from `CupMLWitness` alone.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.2–17.6.
-/

open Complex Filter MeasureTheory
open scoped Manifold ContDiff Topology Classical
open TopologicalSpace (Opens)

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable (𝔇 : ChartDiskCover X)

/-! ### A. The R6 bridge: `MLTie` inhabits `Descent.R6Outputs` -/

/-- **The R6 bridge** — the landed `MLTie` outputs inhabit the `Descent` hypothesis structure
(the statement shapes were copied verbatim, so the bridge is `Subtype.ext` on the glued
element). -/
theorem r6Outputs_holds : R6Outputs 𝔇 := by
  constructor
  · intro j₀ a r g hiso hg t htc
    have hiso' : MLIsolated 𝔇 j₀ a := hiso
    have hC : R6Shape.mlCocycle 𝔇 j₀ a r = mlCocycle 𝔇 j₀ a r := rfl
    rw [hC] at htc
    have ht' : t = ⟨glueCoeff 𝔇 (mlCocycle 𝔇 j₀ a r) g, mlGlue_mem_oneOneCoeff hiso' hg⟩ :=
      Subtype.ext htc
    rw [ht']
    exact resFunctional_mlGlue hiso' hg
  · intro j₀ a g hiso hg hnorm t htc
    have hiso' : MLIsolated 𝔇 j₀ a := hiso
    have hC : R6Shape.mlCocycle 𝔇 j₀ a (1 : ℂ) = mlCocycle 𝔇 j₀ a (1 : ℂ) := rfl
    rw [hC] at htc
    have ht' : t = ⟨glueCoeff 𝔇 (mlCocycle 𝔇 j₀ a (1 : ℂ)) g,
        mlGlue_mem_oneOneCoeff hiso' hg⟩ :=
      Subtype.ext htc
    rw [ht']
    exact resFunctional_mlCocycle_residue_one hiso' hg hnorm

/-! ### B. The K-points and their complement -/

/-- The **K-points**: the finite set where the divisor is positive (the pole locus of `𝒪_K`
scalars). -/
noncomputable def posSupp (K : Divisor X) : Finset X :=
  K.support.filter fun x => 0 < K x

theorem mem_posSupp_iff {K : Divisor X} {x : X} : x ∈ posSupp K ↔ 0 < K x := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by omega), h⟩

/-- The open complement of the K-points. -/
noncomputable def offPos (K : Divisor X) : Opens X :=
  ⟨((posSupp K : Finset X) : Set X)ᶜ, (posSupp K).finite_toSet.isClosed.isOpen_compl⟩

theorem mem_offPos_iff {K : Divisor X} {x : X} : x ∈ offPos K ↔ K x ≤ 0 := by
  show x ∉ ((posSupp K : Finset X) : Set X) ↔ K x ≤ 0
  rw [Finset.mem_coe, mem_posSupp_iff]
  omega

/-- **Pole separation + covering isolate every K-point**: each `a` with `K a > 0` lies in a
single cover set. -/
theorem exists_isolated_of_separatesPoles {K : Divisor X} (hsep : SeparatesPoles 𝔇 K)
    {a : X} (ha : 0 < K a) : ∃ j₀, MLIsolated 𝔇 j₀ a := by
  have hmem : a ∈ ⨆ i, 𝔇.toFiniteCover.U i := by
    rw [𝔇.toFiniteCover.covers]
    trivial
  obtain ⟨j₀, hj₀⟩ := Opens.mem_iSup.1 hmem
  refine ⟨j₀, hj₀, fun i hi hai => ?_⟩
  have h := hsep i j₀ hi a ⟨hai, hj₀⟩
  omega

/-! ### C. Germ multiplicativity -/

omit [Nonempty X] in
private theorem toGerm_mul' {U : Opens X} (f f' : U → ℂ) :
    toGerm U (fun v => f v * f' v) = toGerm U f * toGerm U f' := rfl

/-! ### D. Planar order bookkeeping: pole order under analytic substitution -/

/-- A planar function factoring as `(ψ−α)^m·(u∘ψ)` near `c` (with `ψ` analytic, `ψ c = α`, `u`
analytic) has meromorphic order `≥ m` at `c` — the `dslope` factorization
`ψ ζ − α = (ζ−c)·dslope ψ c ζ` peels off the `m`-fold zero. -/
private theorem le_meromorphicOrderAt_of_pow_factor {F ψ u : ℂ → ℂ} {c α : ℂ} {m : ℕ}
    (hψ : AnalyticAt ℂ ψ c) (hψc : ψ c = α) (hu : AnalyticAt ℂ u α)
    (hfac : ∀ᶠ ζ in 𝓝 c, F ζ = (ψ ζ - α) ^ m * u (ψ ζ)) :
    ((m : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c := by
  have hd : AnalyticAt ℂ (dslope ψ c) c := by
    obtain ⟨p, hp⟩ := hψ
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  have huψ : AnalyticAt ℂ (fun ζ => u (ψ ζ)) c := by
    have hu' : AnalyticAt ℂ u (ψ c) := by
      rw [hψc]
      exact hu
    exact hu'.comp hψ
  have hwan : AnalyticAt ℂ (fun ζ => dslope ψ c ζ ^ m * u (ψ ζ)) c := (hd.pow m).mul huψ
  have hfac2 : F =ᶠ[𝓝 c] fun ζ => (ζ - c) ^ m * (dslope ψ c ζ ^ m * u (ψ ζ)) := by
    filter_upwards [hfac] with ζ hζ
    have hsub : ψ ζ - α = (ζ - c) * dslope ψ c ζ := by
      have h1 := sub_smul_dslope ψ c ζ
      rw [smul_eq_mul] at h1
      rw [← hψc, ← h1]
    rw [hζ, hsub, mul_pow]
    ring
  have hcongr : meromorphicOrderAt F c
      = meromorphicOrderAt (fun ζ => (ζ - c) ^ m * (dslope ψ c ζ ^ m * u (ψ ζ))) c :=
    meromorphicOrderAt_congr (hfac2.filter_mono nhdsWithin_le_nhds)
  have hmulord : meromorphicOrderAt (fun ζ => (ζ - c) ^ m * (dslope ψ c ζ ^ m * u (ψ ζ))) c
      = meromorphicOrderAt ((· - c) ^ m) c
        + meromorphicOrderAt (fun ζ => dslope ψ c ζ ^ m * u (ψ ζ)) c :=
    meromorphicOrderAt_mul (((analyticAt_id.sub analyticAt_const).pow m).meromorphicAt)
      hwan.meromorphicAt
  rw [hcongr, hmulord, meromorphicOrderAt_pow_id_sub_const]
  exact_mod_cast le_add_of_nonneg_right hwan.meromorphicOrderAt_nonneg

/-! ### E. The slot pullback on a sub-open of a cover set -/

section SlotPullback

variable {𝔇} {K : Divisor X} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}

/-- The chart-read of the slot pullback `g j₀ ∘ chartMap j₀` on a sub-open of `U j₀` is
analytic at every point (through the `Gext` bridge and the chart transition). -/
private theorem analyticAt_slotPullback_read {j₀ : 𝔇.toFiniteCover.ι} {W : Opens X}
    (hWU : W ≤ 𝔇.U j₀) (hg1 : ∀ x ∈ (𝔇.U j₀ : Set X), AnalyticAt ℂ (g j₀) (chartMap 𝔇 j₀ x))
    (v : W) :
    AnalyticAt ℂ ((fun w : W => g j₀ (chartMap 𝔇 j₀ w.1)) ∘ (chartAt (H := ℂ) v).symm)
      ((chartAt (H := ℂ) v) v) := by
  set Gp : W → ℂ := fun w => g j₀ (chartMap 𝔇 j₀ w.1) with hGp
  obtain ⟨hbase, hev⟩ := Gext_chart_bridge Gp v.2
  -- the ambient read near the ambient chart point
  have hψ : AnalyticAt ℂ ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt (H := ℂ) (v : X)).symm)
      ((chartAt (H := ℂ) (v : X)) (v : X)) :=
    transition_analyticAt_of_mem (mem_chart_source ℂ (v : X))
      (mem_chartSource_of_mem_U 𝔇 (hWU v.2))
  have hψpt : ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt (H := ℂ) (v : X)).symm)
      ((chartAt (H := ℂ) (v : X)) (v : X)) = chartMap 𝔇 j₀ (v : X) := by
    simp only [Function.comp_apply,
      (chartAt (H := ℂ) (v : X)).left_inv (mem_chart_source ℂ (v : X))]
    rfl
  have hgψ : AnalyticAt ℂ ((g j₀) ∘ ((chartAt ℂ (𝔇.center j₀))
      ∘ (chartAt (H := ℂ) (v : X)).symm)) ((chartAt (H := ℂ) (v : X)) (v : X)) := by
    refine AnalyticAt.comp ?_ hψ
    rw [hψpt]
    exact hg1 (v : X) (hWU v.2)
  -- the ambient read of `Gext Gp` agrees with `g j₀ ∘ ψ` near the chart point
  have hcont : ContinuousAt (chartAt (H := ℂ) (v : X)).symm
      ((chartAt (H := ℂ) (v : X)) (v : X)) :=
    (chartAt (H := ℂ) (v : X)).continuousAt_symm
      ((chartAt (H := ℂ) (v : X)).map_source (mem_chart_source ℂ (v : X)))
  have hWnhds : (W : Set X) ∈ 𝓝 ((chartAt (H := ℂ) (v : X)).symm
      ((chartAt (H := ℂ) (v : X)) (v : X))) := by
    rw [(chartAt (H := ℂ) (v : X)).left_inv (mem_chart_source ℂ (v : X))]
    exact W.isOpen.mem_nhds v.2
  have hagree : (Gext Gp ∘ (chartAt (H := ℂ) (v : X)).symm)
      =ᶠ[𝓝 ((chartAt (H := ℂ) (v : X)) (v : X))]
        ((g j₀) ∘ ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt (H := ℂ) (v : X)).symm)) := by
    filter_upwards [hcont.preimage_mem_nhds hWnhds] with w hw
    show Gext Gp ((chartAt (H := ℂ) (v : X)).symm w)
        = g j₀ (chartMap 𝔇 j₀ ((chartAt (H := ℂ) (v : X)).symm w))
    rw [Gext_apply_mem Gp hw]
  -- transport back through the subtype/ambient bridge
  have hambient : AnalyticAt ℂ (Gext Gp ∘ (chartAt (H := ℂ) (v : X)).symm)
      ((chartAt (H := ℂ) (v : X)) (v : X)) := hgψ.congr hagree.symm
  rw [hbase]
  exact hambient.congr hev.symm

end SlotPullback

/-! ### F. The off-K-points extraction of a `sections0 K` cochain -/

section VanishFn

variable {𝔇} {K : Divisor X}

omit [Nonempty X] in
/-- The restriction of a `sections0 K` component to `U i` minus the K-points is an
`𝒪`-class. -/
theorem restrict_mem_omegaDGerm_zero {f : 𝔇.toFiniteCover.toFiniteFamily.Cochain0}
    (hf : f ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 K) (i : 𝔇.toFiniteCover.ι) :
    rawRestrictG (inf_le_left : (𝔇.U i ⊓ offPos K : Opens X) ≤ 𝔇.U i) (f i)
      ∈ OmegaDGerm (0 : Divisor X) (𝔇.U i ⊓ offPos K) := by
  refine OmegaDGerm_le_zero_of_nonpos (fun x hx => ?_)
    (rawRestrictG_omegaDGerm _ (hf i))
  exact mem_offPos_iff.mp hx.2

/-- **The off-K-points extraction**: the analytic representative of each `sections0 K`
component on its cover set minus the K-points (junk at the K-points and off the set). -/
noncomputable def vanishFn (f : 𝔇.toFiniteCover.toFiniteFamily.Cochain0)
    (hf : f ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 K) : 𝔇.toFiniteCover.ι → X → ℂ :=
  fun i => holoFn (restrict_mem_omegaDGerm_zero hf i)

omit [Nonempty X] in
theorem smoothOnSetsOff_vanishFn {f : 𝔇.toFiniteCover.toFiniteFamily.Cochain0}
    (hf : f ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 K) :
    SmoothOnSetsOff 𝔇 ((posSupp K : Finset X) : Set X) (vanishFn f hf) := by
  intro j x hx hxS
  exact holoFn_contMDiffAt _ ⟨hx, hxS⟩

omit [Nonempty X] in
theorem holomorphicOnSetsOff_vanishFn {f : 𝔇.toFiniteCover.toFiniteFamily.Cochain0}
    (hf : f ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 K) :
    HolomorphicOnSetsOff 𝔇 ((posSupp K : Finset X) : Set X) (vanishFn f hf) := by
  intro j x hx hxS
  have ha := holoFn_chart_analyticAt (restrict_mem_omegaDGerm_zero hf j)
    (⟨hx, hxS⟩ : x ∈ (𝔇.U j ⊓ offPos K : Opens X))
  exact (analyticAt_chart_change_to (mem_chartSource_of_mem_U 𝔇 hx) ha).differentiableAt

omit [Nonempty X] in
/-- The extraction of a coboundary cocycle is the coboundary of the off-K-points extraction,
pointwise on overlaps (overlaps avoid the K-points by `SeparatesPoles`). -/
theorem isCoboundaryOn_cocycleFn_vanishFn (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K))
    {f : 𝔇.toFiniteCover.toFiniteFamily.Cochain0}
    (hf : f ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 K)
    (hcb : (c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1)
      = 𝔇.toFiniteCover.toFiniteFamily.cechDelta0 f) :
    IsCoboundaryOn 𝔇 (cocycleFn 𝔇 hsep c) (vanishFn f hf) := by
  intro i j x hx
  by_cases h : i = j
  · subst h
    rw [cocycleFn_diag]
    simp
  · -- the overlap avoids the K-points
    have hovK : ∀ y ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X), y ∈ offPos K := fun y hy =>
      mem_offPos_iff.mpr (hsep i j h y hy)
    have hle_i : (𝔇.U i ⊓ 𝔇.U j : Opens X) ≤ 𝔇.U i ⊓ offPos K :=
      le_inf inf_le_left fun y hy => hovK y hy
    have hle_j : (𝔇.U i ⊓ 𝔇.U j : Opens X) ≤ 𝔇.U j ⊓ offPos K :=
      le_inf inf_le_right fun y hy => hovK y hy
    have hxi : x ∈ (𝔇.U i ⊓ offPos K : Opens X) := hle_i hx
    have hxj : x ∈ (𝔇.U j ⊓ offPos K : Opens X) := hle_j hx
    refine eq_at_of_toGerm_eq ?_ hx (continuousAt_cocycleFn 𝔇 hsep c hx)
      (((holoFn_contMDiffAt (restrict_mem_omegaDGerm_zero hf j) hxj).continuousAt).sub
        ((holoFn_contMDiffAt (restrict_mem_omegaDGerm_zero hf i) hxi).continuousAt))
    show toGerm (𝔇.U i ⊓ 𝔇.U j) (fun v => cocycleFn 𝔇 hsep c i j v.1)
        = toGerm (𝔇.U i ⊓ 𝔇.U j)
            ((fun v : ↥(𝔇.U i ⊓ 𝔇.U j) => vanishFn f hf j v.1)
              - fun v => vanishFn f hf i v.1)
    have hj' : toGerm (𝔇.U i ⊓ 𝔇.U j) (fun v => vanishFn f hf j v.1)
        = rawRestrictG inf_le_right (f j) := by
      have h1 : rawRestrictG hle_j
            (toGerm (𝔇.U j ⊓ offPos K) (fun v => vanishFn f hf j v.1))
          = toGerm (𝔇.U i ⊓ 𝔇.U j) (fun v => vanishFn f hf j v.1) := rfl
      rw [← h1, vanishFn, toGerm_holoFn (restrict_mem_omegaDGerm_zero hf j),
        FiniteFamily.rawRestrictG_comp_apply]
    have hi' : toGerm (𝔇.U i ⊓ 𝔇.U j) (fun v => vanishFn f hf i v.1)
        = rawRestrictG inf_le_left (f i) := by
      have h1 : rawRestrictG hle_i
            (toGerm (𝔇.U i ⊓ offPos K) (fun v => vanishFn f hf i v.1))
          = toGerm (𝔇.U i ⊓ 𝔇.U j) (fun v => vanishFn f hf i v.1) := rfl
      rw [← h1, vanishFn, toGerm_holoFn (restrict_mem_omegaDGerm_zero hf i),
        FiniteFamily.rawRestrictG_comp_apply]
    rw [map_sub, toGerm_cocycleFn 𝔇 hsep c h, hcb, hj', hi']
    simp only [FiniteFamily.cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]

end VanishFn

/-! ### G. The product-germ trick: the engine's slot-product extension at a K-point -/

section ProductTrick

variable {𝔇} {K : Divisor X} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}

/-- **The product-germ trick**: at a K-point `a` (isolated in `U j₀`) where the slot vanishes
to order `≥ K a`, the product of the meromorphic 0-cochain component with the slot pullback is
an `𝒪`-class near `a`, and its `holoFn` is the analytic extension demanded by the R6b engine:
`SlotProductExtendsAt` holds for the off-K-points extraction.  (No pole-separation
hypothesis: the proof only erases the OTHER K-points from the distinguished set.) -/
theorem slotProductExtendsAt_vanishFn
    {f : 𝔇.toFiniteCover.toFiniteFamily.Cochain0}
    (hf : f ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 K) (hg : IsOneZeroCoeff 𝔇 g)
    {a : X} (haK : 0 < K a) {j₀ : 𝔇.toFiniteCover.ι} (hiso : MLIsolated 𝔇 j₀ a)
    {u : ℂ → ℂ} (hu : AnalyticAt ℂ u (chartMap 𝔇 j₀ a))
    (hgv : ∀ᶠ ζ in 𝓝 (chartMap 𝔇 j₀ a),
      g j₀ ζ = (ζ - chartMap 𝔇 j₀ a) ^ (K a).toNat * u ζ) :
    SlotProductExtendsAt 𝔇 (vanishFn f hf) g j₀ a := by
  classical
  set α := chartMap 𝔇 j₀ a with hαdef
  set m := (K a).toNat with hmdef
  -- the cover set minus the OTHER K-points: an open neighbourhood of `a`
  set T : Finset X := (posSupp K).erase a with hTdef
  have hTcl : IsClosed ((T : Finset X) : Set X) := T.finite_toSet.isClosed
  set U' : Opens X := 𝔇.U j₀ ⊓ ⟨((T : Finset X) : Set X)ᶜ, hTcl.isOpen_compl⟩ with hU'def
  have haT : a ∉ ((T : Finset X) : Set X) := by
    simp [hTdef]
  have haU' : a ∈ U' := ⟨hiso.1, haT⟩
  have hU'U : U' ≤ 𝔇.U j₀ := inf_le_left
  -- a representative of the meromorphic 0-cochain component
  obtain ⟨F, hF, hFg⟩ := Submodule.mem_map.mp (hf j₀)
  -- the slot pullback on `U'`
  set Gp : ↥U' → ℂ := fun v => g j₀ (chartMap 𝔇 j₀ v.1) with hGpdef
  have hGpread : ∀ v : ↥U', AnalyticAt ℂ (Gp ∘ (chartAt (H := ℂ) v).symm)
      ((chartAt (H := ℂ) v) v) :=
    fun v => analyticAt_slotPullback_read hU'U (fun x hx => hg.1 j₀ x hx) v
  have hGpmer : IsMeromorphic (U' : Type _) Gp := fun v => (hGpread v).meromorphicAt
  have hFmer : IsMeromorphic (U' : Type _) ((F : ↥(𝔇.U j₀) → ℂ) ∘ openIncl hU'U) :=
    isMeromorphic_comp_openIncl hU'U hF.1
  -- the product section and its membership in `𝒪(U')`
  set prod : ↥U' → ℂ := fun v => F (openIncl hU'U v) * Gp v with hproddef
  have hprodmer : IsMeromorphic (U' : Type _) prod :=
    fun v => (hFmer v).mul (hGpmer v)
  -- the slot pullback order at the K-point
  have hGp_ord_a : ((m : ℤ) : WithTop ℤ) ≤ ordU Gp ⟨a, haU'⟩ := by
    rw [ordU_eq_orderAt_Gext Gp haU']
    -- the ambient read factors through the chart transition `ψ`
    set ψ : ℂ → ℂ := (chartAt ℂ (𝔇.center j₀)) ∘ (chartAt (H := ℂ) a).symm with hψdef
    have hψa : AnalyticAt ℂ ψ ((chartAt (H := ℂ) a) a) :=
      transition_analyticAt_of_mem (mem_chart_source ℂ a)
        (mem_chartSource_of_mem_U 𝔇 hiso.1)
    have hψpt : ψ ((chartAt (H := ℂ) a) a) = α := by
      simp only [hψdef, Function.comp_apply,
        (chartAt (H := ℂ) a).left_inv (mem_chart_source ℂ a)]
      rfl
    have hψtend : Tendsto ψ (𝓝 ((chartAt (H := ℂ) a) a)) (𝓝 α) := by
      have hψc := hψa.continuousAt
      rwa [ContinuousAt, hψpt] at hψc
    have hcont : ContinuousAt (chartAt (H := ℂ) a).symm ((chartAt (H := ℂ) a) a) :=
      (chartAt (H := ℂ) a).continuousAt_symm
        ((chartAt (H := ℂ) a).map_source (mem_chart_source ℂ a))
    have hU'nhds : (U' : Set X) ∈ 𝓝 ((chartAt (H := ℂ) a).symm ((chartAt (H := ℂ) a) a)) := by
      rw [(chartAt (H := ℂ) a).left_inv (mem_chart_source ℂ a)]
      exact U'.isOpen.mem_nhds haU'
    -- the read agrees with `g j₀ ∘ ψ` near the chart point
    have hagree : (Gext Gp ∘ (chartAt (H := ℂ) a).symm)
        =ᶠ[𝓝 ((chartAt (H := ℂ) a) a)] fun ζ' => g j₀ (ψ ζ') := by
      filter_upwards [hcont.preimage_mem_nhds hU'nhds] with w hw
      show Gext Gp ((chartAt (H := ℂ) a).symm w)
          = g j₀ ((chartAt ℂ (𝔇.center j₀)) ((chartAt (H := ℂ) a).symm w))
      rw [Gext_apply_mem Gp hw]
      rfl
    rw [meromorphicOrderAt_congr (hagree.filter_mono nhdsWithin_le_nhds)]
    -- the factor form, pulled back through `ψ`
    have hfac : ∀ᶠ ζ' in 𝓝 ((chartAt (H := ℂ) a) a),
        g j₀ (ψ ζ') = (ψ ζ' - α) ^ m * u (ψ ζ') :=
      hψtend.eventually hgv
    exact le_meromorphicOrderAt_of_pow_factor hψa hψpt hu hfac
  -- the order bound: the product is an `𝒪`-class on `U'`
  have hord : ∀ v : ↥U', (0 : WithTop ℤ) ≤ ordU prod v := by
    intro v
    have hmul : ordU prod v = ordU ((F : ↥(𝔇.U j₀) → ℂ) ∘ openIncl hU'U) v + ordU Gp v := by
      unfold ordU
      exact meromorphicOrderAt_mul (hFmer v) (hGpmer v)
    have hF_ord : (-(K v.1 : ℤ) : WithTop ℤ) ≤ ordU ((F : ↥(𝔇.U j₀) → ℂ) ∘ openIncl hU'U) v := by
      rw [ordU_comp_openIncl]
      exact hF.2 (openIncl hU'U v)
    by_cases hva : v.1 = a
    · -- at the K-point: `−K a + K a = 0`
      have hv : v = ⟨a, haU'⟩ := Subtype.ext hva
      subst hv
      have hF_ord' : (-(K a : ℤ) : WithTop ℤ)
          ≤ ordU ((F : ↥(𝔇.U j₀) → ℂ) ∘ openIncl hU'U) ⟨a, haU'⟩ := by
        simpa using hF_ord
      have hsum := add_le_add hF_ord' hGp_ord_a
      rw [hmul]
      refine le_trans (le_of_eq ?_) hsum
      norm_cast
      omega
    · -- off the K-point: `K v ≤ 0` and the slot read is analytic
      have hvK : K v.1 ≤ 0 := by
        by_contra hpos
        push Not at hpos
        have hvS : v.1 ∈ posSupp K := mem_posSupp_iff.mpr hpos
        have hvT : v.1 ∈ T := Finset.mem_erase.mpr ⟨hva, hvS⟩
        exact v.2.2 hvT
      have hGp_nonneg : (0 : WithTop ℤ) ≤ ordU Gp v := by
        unfold ordU
        exact (hGpread v).meromorphicOrderAt_nonneg
      have hF_nonneg : (0 : WithTop ℤ) ≤ ordU ((F : ↥(𝔇.U j₀) → ℂ) ∘ openIncl hU'U) v := by
        refine le_trans ?_ hF_ord
        exact_mod_cast neg_nonneg.mpr hvK
      rw [hmul]
      exact add_nonneg hF_nonneg hGp_nonneg
  have hprodmem : toGerm U' prod ∈ OmegaDGerm (0 : Divisor X) U' := by
    refine ⟨prod, ⟨hprodmer, fun v => ?_⟩, rfl⟩
    have h0 : ((0 : Divisor X) v.1 : ℤ) = 0 := rfl
    have e1 : -(((0 : Divisor X) v.1 : ℤ) : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by
      rw [h0]
      simp
    rw [e1]
    exact_mod_cast hord v
  -- the analytic extension is the `holoFn` of the product germ
  set Q : X → ℂ := holoFn hprodmem with hQdef
  have hQa : AnalyticAt ℂ (Q ∘ (chartAt (H := ℂ) a).symm) ((chartAt (H := ℂ) a) a) :=
    holoFn_chart_analyticAt hprodmem haU'
  have hq : AnalyticAt ℂ (fun ζ => Q ((chartAt ℂ (𝔇.center j₀)).symm ζ)) α :=
    analyticAt_chart_change_to (mem_chartSource_of_mem_U 𝔇 hiso.1) hQa
  -- the pointwise identification on `U j₀` minus the K-points
  set W : Opens X := 𝔇.U j₀ ⊓ offPos K with hWdef
  have hWU : W ≤ 𝔇.U j₀ := inf_le_left
  have hWU' : W ≤ U' := by
    refine le_inf inf_le_left fun y hy hyT => ?_
    have h1 := mem_offPos_iff.mp hy.2
    have h2 := mem_posSupp_iff.mp (Finset.mem_of_mem_erase hyT)
    omega
  have hpt : ∀ x ∈ W, vanishFn f hf j₀ x * g j₀ (chartMap 𝔇 j₀ x) = Q x := by
    intro x hxW
    -- germ identity on `W`
    have hgerm : toGerm W (fun v => vanishFn f hf j₀ v.1 * g j₀ (chartMap 𝔇 j₀ v.1))
        = toGerm W (fun v => Q v.1) := by
      have hL : toGerm W (fun v => vanishFn f hf j₀ v.1)
          = rawRestrictG hWU (f j₀) := by
        have h1 := toGerm_holoFn (restrict_mem_omegaDGerm_zero hf j₀)
        exact h1
      have hR1 : toGerm U' (fun v => Q v.1) = toGerm U' prod :=
        toGerm_holoFn hprodmem
      have hR2 : toGerm W (fun v => Q v.1)
          = rawRestrictG hWU' (toGerm U' (fun v => Q v.1)) := rfl
      have hR3 : rawRestrictG hWU' (toGerm U' prod)
          = toGerm W (fun v : ↥W => F (openIncl hWU v) * g j₀ (chartMap 𝔇 j₀ v.1)) := rfl
      have hFW : toGerm W ((F : ↥(𝔇.U j₀) → ℂ) ∘ openIncl hWU)
          = rawRestrictG hWU (f j₀) := by
        rw [← hFg]
        rfl
      calc toGerm W (fun v => vanishFn f hf j₀ v.1 * g j₀ (chartMap 𝔇 j₀ v.1))
          = toGerm W (fun v => vanishFn f hf j₀ v.1)
            * toGerm W (fun v : ↥W => g j₀ (chartMap 𝔇 j₀ v.1)) := rfl
        _ = rawRestrictG hWU (f j₀)
            * toGerm W (fun v : ↥W => g j₀ (chartMap 𝔇 j₀ v.1)) := by rw [hL]
        _ = toGerm W ((F : ↥(𝔇.U j₀) → ℂ) ∘ openIncl hWU)
            * toGerm W (fun v : ↥W => g j₀ (chartMap 𝔇 j₀ v.1)) := by rw [hFW]
        _ = toGerm W (fun v : ↥W => F (openIncl hWU v) * g j₀ (chartMap 𝔇 j₀ v.1)) := rfl
        _ = rawRestrictG hWU' (toGerm U' prod) := hR3.symm
        _ = toGerm W (fun v => Q v.1) := by rw [← hR1, ← hR2]
    -- continuity of both sides at `x`
    have hxU : x ∈ (𝔇.U j₀ : Set X) := hxW.1
    have hcontL : ContinuousAt (fun y => vanishFn f hf j₀ y * g j₀ (chartMap 𝔇 j₀ y)) x := by
      refine ContinuousAt.mul ((holoFn_contMDiffAt
        (restrict_mem_omegaDGerm_zero hf j₀) hxW).continuousAt) ?_
      have hchart : ContinuousAt (chartMap 𝔇 j₀) x :=
        (chartAt ℂ (𝔇.center j₀)).continuousAt (mem_chartSource_of_mem_U 𝔇 hxU)
      exact ((hg.1 j₀ x hxU).continuousAt).comp hchart
    have hcontR : ContinuousAt Q x :=
      (holoFn_contMDiffAt hprodmem (hWU' hxW)).continuousAt
    exact eq_at_of_toGerm_eq hgerm hxW hcontL hcontR
  -- assemble the punctured-neighbourhood extension
  refine ⟨fun ζ => Q ((chartAt ℂ (𝔇.center j₀)).symm ζ), hq, ?_⟩
  have hsrc : a ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 hiso.1
  have hzt : α ∈ (chartAt ℂ (𝔇.center j₀)).target := (chartAt ℂ (𝔇.center j₀)).map_source hsrc
  have hcont : ContinuousAt (chartAt ℂ (𝔇.center j₀)).symm α :=
    (chartAt ℂ (𝔇.center j₀)).continuousAt_symm hzt
  have hUnhds : (𝔇.U j₀ : Set X) ∈ 𝓝 ((chartAt ℂ (𝔇.center j₀)).symm α) := by
    rw [show (chartAt ℂ (𝔇.center j₀)).symm α = a from (chartAt ℂ (𝔇.center j₀)).left_inv hsrc]
    exact (𝔇.U j₀).isOpen.mem_nhds hiso.1
  have hTnhds : (((T : Finset X) : Set X))ᶜ ∈ 𝓝 ((chartAt ℂ (𝔇.center j₀)).symm α) := by
    rw [show (chartAt ℂ (𝔇.center j₀)).symm α = a from (chartAt ℂ (𝔇.center j₀)).left_inv hsrc]
    exact hTcl.isOpen_compl.mem_nhds haT
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      ((chartAt ℂ (𝔇.center j₀)).open_target.mem_nhds hzt),
    eventually_nhdsWithin_of_eventually_nhds (hcont.preimage_mem_nhds hUnhds),
    eventually_nhdsWithin_of_eventually_nhds (hcont.preimage_mem_nhds hTnhds),
    eventually_mem_nhdsWithin] with ζ hζt hζU hζT hζne
  set x' : X := (chartAt ℂ (𝔇.center j₀)).symm ζ with hx'def
  have hζne' : ζ ≠ α := hζne
  have hx'chart : chartMap 𝔇 j₀ x' = ζ := (chartAt ℂ (𝔇.center j₀)).right_inv hζt
  have hx'a : x' ≠ a := by
    intro hcontra
    apply hζne'
    rw [← hx'chart, hcontra]
  have hx'K : x' ∉ posSupp K := by
    intro hx'S
    exact hζT (Finset.mem_erase.mpr ⟨hx'a, hx'S⟩)
  have hx'W : x' ∈ W := ⟨hζU, hx'K⟩
  show vanishFn f hf j₀ x' * g j₀ ζ = Q x'
  rw [← hx'chart]
  exact hpt x' hx'W

end ProductTrick

/-! ### H. The headline: `vanish_coboundary` at general `K` -/

section Headline

/-- **The `dz`-slot matches the divisor**: at each K-point and its (unique) cover chart, the
slot vanishes to order `≥ K a`.  For the chart coefficients of the canonical form `ω₀` with
`K = div ω₀` this is the definition of the divisor of a holomorphic form. -/
def SlotMatchesK (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (K : Divisor X) : Prop :=
  ∀ a, 0 < K a → ∀ j₀ : 𝔇.toFiniteCover.ι, a ∈ (𝔇.U j₀ : Set X) →
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u (chartMap 𝔇 j₀ a) ∧
      ∀ᶠ ζ in 𝓝 (chartMap 𝔇 j₀ a), g j₀ ζ = (ζ - chartMap 𝔇 j₀ a) ^ (K a).toNat * u ζ

variable {𝔇} {K : Divisor X} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}

/-- **THE R7-GAP-1 HEADLINE — full coboundary vanishing at general `K`** (replacing the `K ≤ 0`
restriction of `resCocycle_vanish_coboundary_of_nonpos`): under pole separation and the slot
matching `K`, the fine-sheaf residue functional kills every `B¹(𝒪_K)`-coboundary.  The K-point
scalar poles of `sections0 K` cochains are cancelled by the slot zeros (product-germ trick),
so the R6b engine's Stokes kill applies — Forster §17.3 step 5 at arbitrary genus. -/
theorem resCocycle_vanish_coboundary (hsep : SeparatesPoles 𝔇 K)
    (hg : IsOneZeroCoeff 𝔇 g) (hslot : SlotMatchesK 𝔇 g K) :
    ∀ c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K),
      c ∈ (𝔇.toFiniteCover.toFiniteFamily.coboundaries1 K).submoduleOf
        (𝔇.toFiniteCover.toFiniteFamily.cocycles1 K) →
      resCocycle 𝔇 hsep g hg c = 0 := by
  intro c hc
  have hc' : (c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1)
      ∈ 𝔇.toFiniteCover.toFiniteFamily.coboundaries1 K := hc
  obtain ⟨f, hfK, hcb⟩ := hc'
  rw [resCocycle_apply]
  refine resFunctional_eq_zero_of_mero_coboundary (S := posSupp K)
    (h := vanishFn f hfK) (w := cocycleFn 𝔇 hsep c) _ rfl hg ?_
    (smoothOnSetsOff_vanishFn hfK) (holomorphicOnSetsOff_vanishFn hfK)
    (isCoboundaryOn_cocycleFn_vanishFn hsep c hfK hcb.symm) ?_
  · intro a haS
    exact exists_isolated_of_separatesPoles 𝔇 hsep (mem_posSupp_iff.mp haS)
  · intro a haS j₀ hiso
    have haK : 0 < K a := mem_posSupp_iff.mp haS
    obtain ⟨u, hu, hgv⟩ := hslot a haK j₀ hiso.1
    exact slotProductExtendsAt_vanishFn hfK hg haK hiso hu hgv

/-- **The unconditional `liftQ` descent at general `K`**: the fine-sheaf residue functional on
`cechH1 K`, with the coboundary-vanishing leg PROVEN (no `K ≤ 0` restriction). -/
noncomputable def resH1_of_slotMatches (hsep : SeparatesPoles 𝔇 K)
    (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (hg : IsOneZeroCoeff 𝔇 g) (hslot : SlotMatchesK 𝔇 g K) :
    𝔇.toFiniteCover.toFiniteFamily.cechH1 K →ₗ[ℂ] ℂ :=
  resH1 𝔇 hsep g hg (resCocycle_vanish_coboundary hsep hg hslot)

/-- **`CousinResidueData` from `CupMLWitness` alone** — the R7 assembly with BOTH analytic
legs discharged: `vanish_coboundary` by the general-`K` headline above, `R6Outputs` by the
landed `MLTie` bridge.  The §17.6 witness transport (`CupMLWitness`, R7 blocker §2) is the
single remaining hypothesis. -/
noncomputable def cousinResidueData_of_slotMatches (hsep : SeparatesPoles 𝔇 K)
    (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (hg : IsOneZeroCoeff 𝔇 g) (hslot : SlotMatchesK 𝔇 g K)
    (hwit : CupMLWitness 𝔇 hsep g) :
    CousinResidueData 𝔇.toFiniteCover K :=
  cousinResidueData_of_r6 𝔇 hsep g hg (r6Outputs_holds 𝔇) hwit
    (resCocycle_vanish_coboundary hsep hg hslot)

end Headline

/-! ### I. The corrected §17.6 witness interface (D2d)

`Descent.CupMLWitness` demands the transported `dz/z` cocycle have residue `1` AND slot value
exactly `1` at the pole (`g j₀ (chartMap 𝔇 j₀ a) = 1`).  For a FIXED slot family the level set
`{g = 1}` can be empty (rescale `ω₀`), so that normalization is generally unsatisfiable; the
duality pairing only needs `r · g j₀ (α) = 1` with the transported residue `r` free — which the
witness can always arrange by scaling `ξ`.  `CupMLWitnessR` is the corrected interface; the
membership conjunct of the original is dropped (now PROVEN, `mlGlue_mem_oneOneCoeff`). -/

section WitnessR

variable {K : Divisor X}

/-- **The corrected §17.6 cup–ML witness** (R7 blocker §2, satisfiable normalization): for
every nonzero `v ∈ L(K−D)` there are `ξ ∈ H¹(𝒪_D)` and a residue `r` with `r·g(α) = 1` such
that `cup v ξ` is represented by a cocycle whose extraction agrees on overlaps with the
isolated ML cocycle of residue `r`. -/
def CupMLWitnessR (𝔇 : ChartDiskCover X) {K : Divisor X} (hsep : SeparatesPoles 𝔇 K)
    (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) : Prop :=
  ∀ (D : Divisor X) (v : lSysModule (K - D)), v ≠ 0 →
    ∃ (ξ : 𝔇.toFiniteCover.toFiniteFamily.cechH1 D)
      (z : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K))
      (j₀ : 𝔇.toFiniteCover.ι) (a : X) (r : ℂ),
      MLIsolated 𝔇 j₀ a ∧ r * g j₀ (chartMap 𝔇 j₀ a) = 1 ∧
      cup (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) D K v ξ = Submodule.Quotient.mk z ∧
      ∀ i j, ∀ x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X),
        cocycleFn 𝔇 hsep z i j x = mlCocycle 𝔇 j₀ a r i j x

variable {𝔇}

/-- **The `nondegenerate` field from the corrected witness**: evaluate the descended residue
on the transported cocycle by extraction-congruence against the ML representative; the landed
R6 tie (`resFunctional_mlGlue`) gives `r·g(α) = 1`. -/
theorem nondegenerate_of_witnessR (hsep : SeparatesPoles 𝔇 K)
    (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (hg : IsOneZeroCoeff 𝔇 g)
    (hvanish : ∀ c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K),
      c ∈ (𝔇.toFiniteCover.toFiniteFamily.coboundaries1 K).submoduleOf
        (𝔇.toFiniteCover.toFiniteFamily.cocycles1 K) →
      resCocycle 𝔇 hsep g hg c = 0)
    (hwit : CupMLWitnessR 𝔇 hsep g) :
    ∀ (D : Divisor X) (v : lSysModule (K - D)), v ≠ 0 →
      ∃ ξ : 𝔇.toFiniteCover.toFiniteFamily.cechH1 D,
        (Submodule.liftQ _ (resCocycle 𝔇 hsep g hg) hvanish)
          (cup (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) D K v ξ) = 1 := by
  intro D v hv
  obtain ⟨ξ, z, j₀, a, r, hiso, hnorm, hcup, hov⟩ := hwit D v hv
  refine ⟨ξ, ?_⟩
  rw [hcup]
  have h1 : (Submodule.liftQ _ (resCocycle 𝔇 hsep g hg) hvanish)
      (Submodule.Quotient.mk z) = resCocycle 𝔇 hsep g hg z := rfl
  rw [h1, resCocycle_apply]
  rw [resFunctional_glueCoeff_congr 𝔇 hov
    (⟨_, glueCoeff_cocycleFn_mem 𝔇 hsep z hg⟩ : oneOneCoeff 𝔇)
    (⟨_, mlGlue_mem_oneOneCoeff hiso hg⟩ : oneOneCoeff 𝔇) rfl rfl]
  rw [resFunctional_mlGlue hiso hg]
  exact hnorm

/-- **`CousinResidueData` from `SlotMatchesK` + the corrected witness** — the preferred R7
assembly: `resCocycle` proven, `vanish_coboundary` proven at general `K` (this file),
`nondegenerate` from the corrected, satisfiable §17.6 witness via the landed R6 tie. -/
noncomputable def cousinResidueData_of_witnessR (hsep : SeparatesPoles 𝔇 K)
    (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (hg : IsOneZeroCoeff 𝔇 g) (hslot : SlotMatchesK 𝔇 g K)
    (hwit : CupMLWitnessR 𝔇 hsep g) :
    CousinResidueData 𝔇.toFiniteCover K :=
  cousinResidueData_of_descent 𝔇 hsep g hg
    (resCocycle_vanish_coboundary hsep hg hslot)
    (nondegenerate_of_witnessR hsep g hg (resCocycle_vanish_coboundary hsep hg hslot) hwit)

end WitnessR

end Jacobians.Dolbeault.FineResidue
