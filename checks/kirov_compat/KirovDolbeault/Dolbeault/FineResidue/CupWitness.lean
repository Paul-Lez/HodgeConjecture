/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FineResidue.SlotMatch
import KirovDolbeault.Dolbeault.SerrePsiAction
import KirovDolbeault.Dolbeault.SeparatingCover
import KirovDolbeault.Dolbeault.ChartDiskCoverGeneric

/-!
# R7d — `CupMLWitnessR` inhabited: the one-point cocycle over the reserved disk

This file closes the §17.6 witness-transport gap (`R7_BLOCKER.md` §2 / `R6D2_BLOCKER.md` §2):
the corrected cup–Mittag-Leffler witness `CupMLWitnessR` is **inhabited** whenever the cover has
an isolated point `a` at which the `dz`-slot does not vanish.

## The dissolution by cup surjectivity

The original plan tried to *transport* the cup class `cup v ξ` to an explicit ML representative
— the hard direction.  The landed `cup_surjective_of_ne_zero` (`SerrePsiAction`, Forster 17.8 via
iterated skyscrapers) dissolves it: multiplication by a nonzero `v ∈ L(K−D)` is **surjective**
on `H¹`, so for the explicit germ-level one-point ML cocycle `z` (simple pole at the reserved
point `a`, residue `r = g j₀(α)⁻¹`) there is *some* `ξ ∈ H¹(𝒪_D)` with `cup v ξ = [z]` — no
transport computation at all.  The witness only has to supply:

* `z ∈ Z¹(𝒪_K)` — the germ-level ML cochain `mlCochain` (the `toGerm` image of the proven
  pointwise family `mlCocycle`): the cocycle identity is the pointwise ring identity pushed
  through `toGerm`, and the `𝒪_K`-section bound holds because the pole `a` is isolated
  (`MLIsolated` keeps `a` off every overlap) and `K ≥ 0` (true for `K = div ω₀`);
* the extraction agreement `cocycleFn z = mlCocycle` — germ classes pin continuous
  representatives pointwise (`eq_at_of_toGerm_eq`);
* the normalization `r · g j₀(α) = 1` — `inv_mul_cancel₀`, possible since `g j₀(α) ≠ 0`.

For the canonical-form slot `g = omegaCoeff 𝔇 ω₀` the nonvanishing point comes free from the
**reserved zone** of the separating cover (`SeparatingCover`): `W` avoids `S = (div ω₀).support`
entirely, so the slot has analytic order `0` — value `≠ 0` — at every `a ∈ W`, all of which are
`MLIsolated`.

## Main declarations

* `mlCochain` / `mlCochain_mem_cocycles1` — the germ-level one-point ML cocycle in `Z¹(𝒪_K)`.
* `cupMLWitnessR_of_isolated` — **the witness**: `CupMLWitnessR 𝔇 hsep g` from an isolated
  point with nonvanishing slot (any `g`, any `K ≥ 0`).
* `formDivisor_nonneg` / `omegaCoeff_ne_zero_at` — the `ω₀`-side inputs: `div ω₀ ≥ 0`, and the
  slot is nonvanishing wherever `K = 0`.
* `exists_separating_cousinResidueData` — **the R-lane capstone**: for every finite cover `𝔘`
  and global holomorphic 1-form `α` with divisor `K`, a refining separating chart-disk cover
  carrying a fully proven `CousinResidueData 𝔇.toFiniteCover K` (Leray + locally realizable),
  via `cousinResidueData_omegaCoeff` with **no remaining hypotheses**.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.5–17.8.
-/

open Complex Filter
open scoped Manifold ContDiff Topology Classical
open TopologicalSpace (Opens)

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable (𝔇 : ChartDiskCover X)

/-! ### A. The germ-level one-point ML cochain -/

/-- The **germ-level one-point Mittag-Leffler 1-cochain**: the `toGerm` image of the pointwise
ML overlap family `mlCocycle 𝔇 j₀ a r` (simple pole at `a` with residue `r` in the distinguished
chart `j₀`, orientation `w i j = p_i − p_j`). -/
noncomputable def mlCochain (j₀ : 𝔇.toFiniteCover.ι) (a : X) (r : ℂ) :
    𝔇.toFiniteCover.toFiniteFamily.Cochain1 :=
  fun p => toGerm (𝔇.U p.1 ⊓ 𝔇.U p.2) (fun v => mlCocycle 𝔇 j₀ a r p.1 p.2 v.1)

variable {𝔇} {j₀ : 𝔇.toFiniteCover.ι} {a : X} {r : ℂ} {K : Divisor X}

/-- The ML cochain satisfies the Čech cocycle identity: the pointwise ring identity
`(p_b − p_c) − (p_a − p_c) + (p_a − p_b) = 0` pushed through the (linear) germ projection. -/
theorem mlCochain_delta_eq_zero :
    𝔇.toFiniteCover.toFiniteFamily.cechDelta1 (mlCochain 𝔇 j₀ a r) = 0 := by
  funext t
  obtain ⟨i, j, k⟩ := t
  simp only [FiniteFamily.cechDelta1, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.proj_apply, Pi.zero_apply,
    mlCochain, rawRestrictG_coe]
  rw [← map_sub, ← map_add]
  have hzero : ((fun v => mlCocycle 𝔇 j₀ a r j k v.1) ∘
        openIncl (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      - (fun v => mlCocycle 𝔇 j₀ a r i k v.1) ∘
          openIncl (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      + (fun v => mlCocycle 𝔇 j₀ a r i j v.1) ∘ openIncl inf_le_left)
      = (0 : ↥(𝔇.U i ⊓ 𝔇.U j ⊓ 𝔇.U k) → ℂ) := by
    funext v
    simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, Pi.zero_apply, openIncl,
      mlCocycle]
    ring
  rw [hzero, map_zero]

/-- The restricted one-point principal part is an `𝒪_K`-germ on any open `V ⊆ U j₀` avoiding the
pole, provided `K ≥ 0` on `V`: away from `a` the chart denominator is nonvanishing
(`mlDenom_ne_zero`), so the chart-pullback `F ∘ φ` of the planar `F = r·(·−α)⁻¹` is analytic —
order `≥ 0 ≥ −K`. -/
theorem toGerm_mlPrincipal_mem (hiso : MLIsolated 𝔇 j₀ a) (hK0 : ∀ x, 0 ≤ K x)
    {V : Opens X} (hV : (V : Set X) ⊆ (𝔇.U j₀ : Set X)) (haV : a ∉ (V : Set X)) :
    toGerm V (fun v => mlPrincipal 𝔇 j₀ a r v.1) ∈ OmegaDGerm K V := by
  set F : ℂ → ℂ := fun w => r * (w - chartMap 𝔇 j₀ a)⁻¹ with hF
  have hVsrc : (V : Set X) ⊆ (chartAt (H := ℂ) (𝔇.center j₀)).source := fun x hx =>
    mem_chartSource_of_mem_U 𝔇 (hV hx)
  have heq : (fun v : V => mlPrincipal 𝔇 j₀ a r v.1)
      = fun v : V => F ((chartAt (H := ℂ) (𝔇.center j₀)) v.1) := by
    funext v
    simp only [mlPrincipal, chartMap, hF]
  rw [heq]
  have hFmer : ∀ z : ℂ, MeromorphicAt F z := fun z =>
    (MeromorphicAt.const r z).mul ((analyticAt_id.sub analyticAt_const).meromorphicAt.inv)
  refine ⟨_, mem_OmegaD.mpr ⟨isMeromorphic_comp_chart hVsrc hFmer, fun v => ?_⟩, rfl⟩
  have hvj : v.1 ∈ (𝔇.U j₀ : Set X) := hV v.2
  have hva : v.1 ≠ a := fun h => haV (h ▸ v.2)
  have hden : chartMap 𝔇 j₀ v.1 - chartMap 𝔇 j₀ a ≠ 0 := mlDenom_ne_zero hiso hvj hva
  have hFan : AnalyticAt ℂ F ((chartAt (H := ℂ) (𝔇.center j₀)) v.1) := by
    refine analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv ?_)
    simpa [chartMap] using hden
  have h0 : (0 : WithTop ℤ)
      ≤ ordU (fun w : V => F ((chartAt (H := ℂ) (𝔇.center j₀)) w.1)) v := by
    rw [ordU_comp_chart_eq hVsrc F v.2]
    exact hFan.meromorphicOrderAt_nonneg
  refine le_trans ?_ h0
  have : (-(K v.1) : ℤ) ≤ (0 : ℤ) := neg_nonpos.mpr (hK0 v.1)
  exact_mod_cast this

/-- The ML cochain is a `𝒪_K`-section on every pairwise overlap (`MLIsolated` keeps the pole
off every set but `U j₀`; `K ≥ 0` makes analytic germs `𝒪_K`-germs). -/
theorem mlCochain_mem_sections1 (hiso : MLIsolated 𝔇 j₀ a) (hK0 : ∀ x, 0 ≤ K x) :
    mlCochain 𝔇 j₀ a r ∈ 𝔇.toFiniteCover.toFiniteFamily.sections1 K := by
  intro p
  obtain ⟨i, j⟩ := p
  show toGerm (𝔇.U i ⊓ 𝔇.U j) (fun v => mlCocycle 𝔇 j₀ a r i j v.1)
    ∈ OmegaDGerm K (𝔇.U i ⊓ 𝔇.U j)
  by_cases hi : i = j₀ <;> by_cases hj : j = j₀
  · -- both distinguished: the cocycle vanishes
    have hzero : (fun v : ↥(𝔇.U i ⊓ 𝔇.U j) => mlCocycle 𝔇 j₀ a r i j v.1)
        = (0 : ↥(𝔇.U i ⊓ 𝔇.U j) → ℂ) := by
      funext v
      simp [mlCocycle, hi, hj]
    rw [hzero, map_zero]
    exact Submodule.zero_mem _
  · -- `i = j₀`, `j ≠ j₀`: the cocycle is the principal part; the pole avoids `U j`
    have heq : (fun v : ↥(𝔇.U i ⊓ 𝔇.U j) => mlCocycle 𝔇 j₀ a r i j v.1)
        = fun v : ↥(𝔇.U i ⊓ 𝔇.U j) => mlPrincipal 𝔇 j₀ a r v.1 := by
      funext v
      simp [mlCocycle, mlPart, hi, hj]
    rw [heq]
    refine toGerm_mlPrincipal_mem hiso hK0 (fun x hx => ?_) (fun ha => ?_)
    · exact hi ▸ hx.1
    · exact hiso.2 j hj ha.2
  · -- `i ≠ j₀`, `j = j₀`: minus the principal part
    have heq : (fun v : ↥(𝔇.U i ⊓ 𝔇.U j) => mlCocycle 𝔇 j₀ a r i j v.1)
        = fun v : ↥(𝔇.U i ⊓ 𝔇.U j) => -(mlPrincipal 𝔇 j₀ a r v.1) := by
      funext v
      simp [mlCocycle, mlPart, hi, hj]
    have heq2 : (fun v : ↥(𝔇.U i ⊓ 𝔇.U j) => -(mlPrincipal 𝔇 j₀ a r v.1))
        = -(fun v : ↥(𝔇.U i ⊓ 𝔇.U j) => mlPrincipal 𝔇 j₀ a r v.1) := rfl
    rw [heq, heq2, map_neg]
    refine Submodule.neg_mem _ (toGerm_mlPrincipal_mem hiso hK0 (fun x hx => ?_) (fun ha => ?_))
    · exact hj ▸ hx.2
    · exact hiso.2 i hi ha.1
  · -- neither distinguished: the cocycle vanishes
    have hzero : (fun v : ↥(𝔇.U i ⊓ 𝔇.U j) => mlCocycle 𝔇 j₀ a r i j v.1)
        = (0 : ↥(𝔇.U i ⊓ 𝔇.U j) → ℂ) := by
      funext v
      simp [mlCocycle, mlPart, hi, hj]
    rw [hzero, map_zero]
    exact Submodule.zero_mem _

/-- **The one-point ML cochain is a `Z¹(𝒪_K)`-cocycle.** -/
theorem mlCochain_mem_cocycles1 (hiso : MLIsolated 𝔇 j₀ a) (hK0 : ∀ x, 0 ≤ K x) :
    mlCochain 𝔇 j₀ a r ∈ 𝔇.toFiniteCover.toFiniteFamily.cocycles1 K :=
  Submodule.mem_inf.mpr
    ⟨LinearMap.mem_ker.mpr mlCochain_delta_eq_zero, mlCochain_mem_sections1 hiso hK0⟩

/-! ### B. The extraction reads back the pointwise ML family -/

/-- **The germ→coefficient extraction of the ML cochain is the pointwise ML family**: both are
continuous representatives of the same overlap germ classes, hence agree at every overlap point
(`eq_at_of_toGerm_eq`); the diagonal is `0 = p − p` on both sides. -/
theorem cocycleFn_mlCochain (hsep : SeparatesPoles 𝔇 K) (hiso : MLIsolated 𝔇 j₀ a)
    (hK0 : ∀ x, 0 ≤ K x) :
    ∀ i j, ∀ x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X),
      cocycleFn 𝔇 hsep ⟨mlCochain 𝔇 j₀ a r, mlCochain_mem_cocycles1 hiso hK0⟩ i j x
        = mlCocycle 𝔇 j₀ a r i j x := by
  intro i j x hx
  by_cases hij : i = j
  · subst hij
    rw [cocycleFn_diag]
    simp [mlCocycle]
  · refine eq_at_of_toGerm_eq (V := 𝔇.U i ⊓ 𝔇.U j) ?_ hx
      (continuousAt_cocycleFn 𝔇 hsep _ hx)
      ((smoothOnOverlaps_mlCocycle hiso i j x hx).continuousAt)
    rw [toGerm_cocycleFn 𝔇 hsep _ hij]
    rfl

/-! ### C. The witness: cup surjectivity supplies the class -/

/-- **`CupMLWitnessR` is inhabited from an isolated point with nonvanishing slot** (the §17.6
witness, R7 blocker §2 closed): for any divisor `K ≥ 0` separated by the cover, any slot family
`g`, and any `MLIsolated` point `a` with `g j₀(α) ≠ 0`, the corrected cup–ML witness holds.
The detecting class is supplied by **cup surjectivity** (`cup_surjective_of_ne_zero`, Forster
17.8): the explicit one-point cocycle `mlCochain` with residue `r = g j₀(α)⁻¹` is hit by
`cup v ·` for every nonzero `v` — no transport computation. -/
theorem cupMLWitnessR_of_isolated (hsep : SeparatesPoles 𝔇 K) (hK0 : ∀ x, 0 ≤ K x)
    (hR : 𝔇.toFiniteCover.LocallyRealizable) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ)
    (hiso : MLIsolated 𝔇 j₀ a) (hg0 : g j₀ (chartMap 𝔇 j₀ a) ≠ 0) :
    CupMLWitnessR 𝔇 hsep g := by
  intro D v hv
  set r : ℂ := (g j₀ (chartMap 𝔇 j₀ a))⁻¹ with hr
  obtain ⟨ξ, hξ⟩ := cup_surjective_of_ne_zero 𝔇.toFiniteCover hR D K v hv
    (Submodule.Quotient.mk ⟨mlCochain 𝔇 j₀ a r, mlCochain_mem_cocycles1 hiso hK0⟩)
  exact ⟨ξ, ⟨mlCochain 𝔇 j₀ a r, mlCochain_mem_cocycles1 hiso hK0⟩, j₀, a, r, hiso,
    inv_mul_cancel₀ hg0, hξ, cocycleFn_mlCochain hsep hiso hK0⟩

/-! ### D. The `ω₀`-side inputs: `div ω₀ ≥ 0` and slot nonvanishing off the divisor -/

/-- **The divisor of a global holomorphic 1-form is effective**: its chart coefficient is
analytic (`coeffAt_analyticAt`), so the chart-invariant order is `≥ 0` everywhere. -/
theorem formDivisor_nonneg (α : HolomorphicOneForms X)
    (hK : ∀ x, (holToMero α).formOrderW x = (K x : WithTop ℤ)) (x : X) : 0 ≤ K x := by
  have hsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have h := formOrderW_chart_invariant (holToMero α) x x hsrc
  rw [hK x] at h
  have hcoeff : formCoeff (holToMero α).toFun x = coeffAt α x := formCoeff_holToSection α x
  rw [hcoeff] at h
  have han : AnalyticAt ℂ (coeffAt α x) ((chartAt ℂ x) x) :=
    coeffAt_analyticAt α x ((chartAt ℂ x).map_source hsrc)
  have h0 : (0 : WithTop ℤ) ≤ meromorphicOrderAt (coeffAt α x) ((chartAt ℂ x) x) :=
    han.meromorphicOrderAt_nonneg
  rw [← h] at h0
  exact_mod_cast h0

variable (𝔇) in
/-- **The canonical-form slot is nonvanishing wherever `K = div ω₀` vanishes**: the chart
coefficient is analytic of order `K a = 0` there, and analytic order `0` means value `≠ 0`. -/
theorem omegaCoeff_ne_zero_at (α : HolomorphicOneForms X)
    (hK : ∀ x, (holToMero α).formOrderW x = (K x : WithTop ℤ))
    (haU : a ∈ (𝔇.U j₀ : Set X)) (haK : K a = 0) :
    omegaCoeff 𝔇 α j₀ (chartMap 𝔇 j₀ a) ≠ 0 := by
  have hsrc : a ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 haU
  have htgt : chartMap 𝔇 j₀ a ∈ (chartAt ℂ (𝔇.center j₀)).target :=
    (chartAt ℂ (𝔇.center j₀)).map_source hsrc
  have han : AnalyticAt ℂ (coeffAt α (𝔇.center j₀)) (chartMap 𝔇 j₀ a) :=
    coeffAt_analyticAt α (𝔇.center j₀) htgt
  -- the meromorphic order of the chart coefficient at `a` is `K a = 0`
  have hmero : meromorphicOrderAt (coeffAt α (𝔇.center j₀)) (chartMap 𝔇 j₀ a)
      = ((0 : ℤ) : WithTop ℤ) := by
    have h := formOrderW_chart_invariant (holToMero α) (𝔇.center j₀) a hsrc
    rw [hK a] at h
    have hcoeff : formCoeff (holToMero α).toFun (𝔇.center j₀) = coeffAt α (𝔇.center j₀) :=
      formCoeff_holToSection α (𝔇.center j₀)
    rw [hcoeff, haK] at h
    exact h.symm
  -- hence the analytic order is `0`, and the value is nonzero
  have hord : analyticOrderAt (coeffAt α (𝔇.center j₀)) (chartMap 𝔇 j₀ a) = 0 := by
    rw [han.meromorphicOrderAt_eq] at hmero
    cases hcase : analyticOrderAt (coeffAt α (𝔇.center j₀)) (chartMap 𝔇 j₀ a) with
    | top =>
      rw [hcase, ENat.map_top] at hmero
      exact absurd hmero.symm (WithTop.coe_ne_top)
    | coe n =>
      rw [hcase, ENat.map_coe] at hmero
      have hn : (n : ℤ) = 0 := WithTop.coe_inj.mp hmero
      exact_mod_cast hn
  have := han.analyticOrderAt_eq_zero.mp hord
  simpa [omegaCoeff] using this

/-! ### E. The R-lane capstone: a fully proven `CousinResidueData` on a constructed cover -/

/-- **The R-lane capstone — `CousinResidueData` with no remaining hypotheses**: for every
finite cover `𝔘` and global holomorphic 1-form `α` with divisor `K` (the
`exists_form_divisor` output shape), there is a separating chart-disk cover `𝔇` refining `𝔘`
— Leray and locally realizable — that separates the poles of `K`, carries the inhabited
`CupMLWitnessR` for the canonical-form slot, and hence a **fully proven**
`CousinResidueData 𝔇.toFiniteCover K` (via `cousinResidueData_omegaCoeff`: `resCocycle` R1–R5,
`vanish_coboundary` at general `K` R7b, `nondegenerate` from the one-point cocycle + cup
surjectivity).  The isolated nonvanishing point is any point of the reserved zone `W` of
`exists_separatingChartDiskCover` with `S = K.support`. -/
theorem exists_separating_cousinResidueData (𝔘 : FiniteCover X) (α : HolomorphicOneForms X)
    {K : Divisor X} (hK : ∀ x, (holToMero α).formOrderW x = (K x : WithTop ℤ)) :
    ∃ (𝔇 : ChartDiskCover X) (ρ : 𝔇.ι → 𝔘.ι),
      FiniteCover.IsRefinement 𝔇.toFiniteCover 𝔘 ρ ∧
      𝔇.toFiniteCover.IsLeray ∧ 𝔇.toFiniteCover.LocallyRealizable ∧
      ∃ hsep : SeparatesPoles 𝔇 K,
        CupMLWitnessR 𝔇 hsep (omegaCoeff 𝔇 α) ∧
        Nonempty (CousinResidueData 𝔇.toFiniteCover K) := by
  obtain ⟨𝔇, ρ, j₀, W, href, hsepS, ⟨w, hw⟩, hWU, hpriv, hWS⟩ :=
    exists_separatingChartDiskCover 𝔘 K.support
  have hsep : SeparatesPoles 𝔇 K := by
    intro i j hij x hx
    have hxS : x ∉ (↑K.support : Set X) := hsepS i j hij x hx
    have hx0 : K x = 0 := Finsupp.notMem_support_iff.mp (fun hmem => hxS hmem)
    omega
  have hK0 : ∀ x, 0 ≤ K x := formDivisor_nonneg α hK
  have hiso : MLIsolated 𝔇 j₀ w := ⟨hWU hw, fun i hi => hpriv w hw i hi⟩
  have hKw : K w = 0 := Finsupp.notMem_support_iff.mp (fun hmem => hWS w hw hmem)
  have hg0 : omegaCoeff 𝔇 α j₀ (chartMap 𝔇 j₀ w) ≠ 0 :=
    omegaCoeff_ne_zero_at 𝔇 α hK (hWU hw) hKw
  have hR : 𝔇.toFiniteCover.LocallyRealizable := ChartDiskCover.locallyRealizable 𝔇
  have hwit : CupMLWitnessR 𝔇 hsep (omegaCoeff 𝔇 α) :=
    cupMLWitnessR_of_isolated hsep hK0 hR (omegaCoeff 𝔇 α) hiso hg0
  exact ⟨𝔇, ρ, href, ChartDiskCover.isLeray 𝔇, hR, hsep, hwit,
    ⟨cousinResidueData_omegaCoeff hsep α hK hwit⟩⟩

end Jacobians.Dolbeault.FineResidue
