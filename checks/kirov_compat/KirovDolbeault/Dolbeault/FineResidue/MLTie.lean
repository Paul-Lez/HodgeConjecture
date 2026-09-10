/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FineResidue.Integral
import KirovDolbeault.Dolbeault.FineResidue.OmegaWitness
import KirovDolbeault.Dolbeault.FineResidue.Stokes
import KirovDolbeault.Dolbeault.FineResidue.CoboundaryVanish

/-!
# R6 — the simple-pole Mittag-Leffler tie

The keystone rung of the fine-sheaf residue ladder
(`docs/planning/R6_HANDOFF.md`): on a chart-disk cover where the pole `a`
lies in a single cover set (`MLIsolated`), the residue functional of the
glued `(1,1)` family of the simple-pole Mittag-Leffler cocycle equals the
residue:

  `resFunctional 𝔇 (mlGlue ...) = r · g j₀ (chartMap 𝔇 j₀ a)`

and, normalized (`g j₀ = 1` at the pole), exactly `r` — the END-TO-END SIGN
TEST `resFunctional_mlCocycle_residue_one` demanded by the R0 contract.

## Orientation contract (IMPORTANT for R7)

The ML cocycle here is `mlCocycle i j := mlPart i − mlPart j` (NOT `j − i`).
With this orientation the split is `s_j = B − p_j` (`B = ρ_{j₀}·P` the
smeared pole), `∂̄s_j = ∂̄B̃` off the pole, and the functional evaluates to
`+r` under `resNormalization = −π⁻¹` (R0). The opposite orientation gives
`−r`. R7's descent into the port's Čech `δ` MUST match this orientation;
the sign-test lemma pins it kernel-side.

Sign derivation (R0 cited, never re-derived):
`resIntegralFun = ∫ ∂̄(χ·r/(z−α))·g̃ = r·(−π)·χ(α)·g̃(α)` (Cauchy-Pompeiu via
`integral_dbar_smearedSimplePole`'s mechanism, `χ(α) = 1` since the other
PoU weights vanish near the isolated pole), times `resNormalization = −π⁻¹`
gives `+ r·g̃(α)`.
-/

noncomputable section

open Complex Filter MeasureTheory
open scoped Manifold ContDiff Topology Classical Real
open TopologicalSpace (Opens)

-- Same permissive transparency as `RealForms`/`DolbeaultComparisonInverse`/`CoboundaryVanish`
-- (the `SmoothCFunctions` coercions of `rhoC` below need it).
set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]
    (𝔇 : ChartDiskCover X)

/-- The pole `a` lies in the cover set `U j₀` and in NO other cover set —
the K-point/pole refinement discipline (Glue/OmegaWitness docstrings). -/
def MLIsolated (j₀ : 𝔇.toFiniteCover.ι) (a : X) : Prop :=
  a ∈ (𝔇.U j₀ : Set X) ∧ ∀ i, i ≠ j₀ → a ∉ (𝔇.U i : Set X)

/-- The global principal-part function of a simple pole at `a` with residue
`r`, read through the distinguished chart: `P x = r·(z(x) − z(a))⁻¹`.
Junk-valued off `U j₀`; holomorphic on `U j₀ \ {a}` in the chart. -/
def mlPrincipal (j₀ : 𝔇.toFiniteCover.ι) (a : X) (r : ℂ) : X → ℂ :=
  fun x => r * (chartMap 𝔇 j₀ x - chartMap 𝔇 j₀ a)⁻¹

/-- The one-point ML part family: the principal part on the distinguished
set, `0` elsewhere. -/
def mlPart (j₀ : 𝔇.toFiniteCover.ι) (a : X) (r : ℂ) :
    𝔇.toFiniteCover.ι → X → ℂ :=
  fun i => if i = j₀ then mlPrincipal 𝔇 j₀ a r else 0

/-- The simple-pole ML overlap cocycle, in the ORIENTATION the sign test
pins (see the module docstring): `w i j = p_i − p_j`. -/
def mlCocycle (j₀ : 𝔇.toFiniteCover.ι) (a : X) (r : ℂ) :
    𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ :=
  fun i j x => mlPart 𝔇 j₀ a r i x - mlPart 𝔇 j₀ a r j x

section Hypotheses

variable {𝔇} {j₀ : 𝔇.toFiniteCover.ι} {a : X} {r : ℂ}

omit [Nonempty X] in
/-- Difference families are overlap cocycles (both orientations). -/
theorem isOverlapCocycle_mlCocycle :
    IsOverlapCocycle 𝔇 (mlCocycle 𝔇 j₀ a r) := by
  intro i j k x hx
  simp only [mlCocycle]
  ring

omit [Nonempty X] in
/-- The chart denominator of the principal part is nonvanishing away from
the pole (chart injectivity on the source). -/
theorem mlDenom_ne_zero (hiso : MLIsolated 𝔇 j₀ a) {x : X}
    (hxj : x ∈ (𝔇.U j₀ : Set X)) (hxa : x ≠ a) :
    chartMap 𝔇 j₀ x - chartMap 𝔇 j₀ a ≠ 0 := by
  rw [sub_ne_zero]
  exact fun h => hxa ((chartAt ℂ (𝔇.center j₀)).injOn
    (mem_chartSource_of_mem_U 𝔇 hxj) (mem_chartSource_of_mem_U 𝔇 hiso.1) h)

omit [Nonempty X] in
/-- The principal part is `ℝ`-smooth away from the pole (chart coordinate
smooth via `contMDiffAt_extChartAt'`, denominator nonvanishing). -/
theorem contMDiffAt_mlPrincipal (hiso : MLIsolated 𝔇 j₀ a) {x : X}
    (hxj : x ∈ (𝔇.U j₀ : Set X)) (hxa : x ≠ a) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (mlPrincipal 𝔇 j₀ a r) x := by
  have hchart : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (chartMap 𝔇 j₀) x :=
    contMDiffAt_extChartAt' (I := 𝓘(ℝ, ℂ)) (mem_chartSource_of_mem_U 𝔇 hxj)
  have houter : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : ℂ => r * (z - chartMap 𝔇 j₀ a)⁻¹) (chartMap 𝔇 j₀ x) :=
    contDiffAt_const.mul
      ((contDiffAt_id.sub contDiffAt_const).inv (mlDenom_ne_zero hiso hxj hxa))
  exact (contMDiffAt_iff_contDiffAt.2 houter).comp x hchart

omit [Nonempty X] in
/-- One ML part is `ℝ`-smooth at any non-pole point of its set. -/
theorem contMDiffAt_mlPart (hiso : MLIsolated 𝔇 j₀ a) {k : 𝔇.toFiniteCover.ι}
    {x : X} (hxa : x ≠ a) (hxj : k = j₀ → x ∈ (𝔇.U j₀ : Set X)) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (mlPart 𝔇 j₀ a r k) x := by
  unfold mlPart
  by_cases hk : k = j₀
  · subst hk
    rw [if_pos rfl]
    exact contMDiffAt_mlPrincipal hiso (hxj rfl) hxa
  · rw [if_neg hk]
    exact contMDiffAt_const

omit [Nonempty X] in
/-- Under isolation, every overlap avoids the pole, so the cocycle is
smooth on overlaps. -/
theorem smoothOnOverlaps_mlCocycle (hiso : MLIsolated 𝔇 j₀ a) :
    SmoothOnOverlaps 𝔇 (mlCocycle 𝔇 j₀ a r) := by
  intro i j x hx
  by_cases hij : i = j₀ ∧ j = j₀
  · refine (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => ?_)
    simp [mlCocycle, hij.1, hij.2]
  · have hxa : x ≠ a := by
      rcases not_and_or.mp hij with hi | hj
      · exact fun h => hiso.2 i hi (h ▸ hx.1)
      · exact fun h => hiso.2 j hj (h ▸ hx.2)
    exact (contMDiffAt_mlPart hiso hxa fun h => h ▸ hx.1).sub
      (contMDiffAt_mlPart hiso hxa fun h => h ▸ hx.2)

omit [Nonempty X] in
/-- The chart-`i` read of one ML part is `ℂ`-differentiable at non-pole
overlap coordinates: it is `r·(φ_{i j₀} z − α)⁻¹` (or `0`), with the
transition holomorphic and the denominator nonvanishing. -/
theorem differentiableAt_mlPart_read (hiso : MLIsolated 𝔇 j₀ a)
    {i k : 𝔇.toFiniteCover.ι} {x : X} (hxi : x ∈ (𝔇.U i : Set X)) (hxa : x ≠ a)
    (hxj : k = j₀ → x ∈ (𝔇.U j₀ : Set X)) :
    DifferentiableAt ℂ
      (fun z => mlPart 𝔇 j₀ a r k ((chartAt ℂ (𝔇.center i)).symm z))
      (chartMap 𝔇 i x) := by
  unfold mlPart
  by_cases hk : k = j₀
  · rw [if_pos hk]
    have hxj' := hxj hk
    -- the read IS `fun z => r * (transitionMap 𝔇 i j₀ z − α)⁻¹` definitionally
    have htrans : AnalyticAt ℂ (transitionMap 𝔇 i j₀) (chartMap 𝔇 i x) :=
      transitionMap_analyticAt 𝔇 hxi hxj'
    have hden : transitionMap 𝔇 i j₀ (chartMap 𝔇 i x) - chartMap 𝔇 j₀ a ≠ 0 := by
      rw [transitionMap_chartMap 𝔇 hxi]
      exact mlDenom_ne_zero hiso hxj' hxa
    exact (analyticAt_const.mul
      ((htrans.sub analyticAt_const).inv hden)).differentiableAt
  · rw [if_neg hk]
    exact differentiableAt_const _

omit [Nonempty X] in
/-- Under isolation, the cocycle is holomorphic on overlaps. -/
theorem holomorphicOnOverlaps_mlCocycle (hiso : MLIsolated 𝔇 j₀ a) :
    HolomorphicOnOverlaps 𝔇 (mlCocycle 𝔇 j₀ a r) := by
  intro i j x hx
  by_cases hij : i = j₀ ∧ j = j₀
  · refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => ?_)
    simp [mlCocycle, hij.1, hij.2]
  · have hxa : x ≠ a := by
      rcases not_and_or.mp hij with hi | hj
      · exact fun h => hiso.2 i hi (h ▸ hx.1)
      · exact fun h => hiso.2 j hj (h ▸ hx.2)
    exact (differentiableAt_mlPart_read hiso hx.1 hxa fun h => h ▸ hx.1).sub
      (differentiableAt_mlPart_read hiso hx.1 hxa fun h => h ▸ hx.2)

/-- The glued family of the ML cocycle is a global `(1,1)` family (R3's
headline applied to the verified hypotheses). -/
theorem mlGlue_mem_oneOneCoeff (hiso : MLIsolated 𝔇 j₀ a)
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) :
    glueCoeff 𝔇 (mlCocycle 𝔇 j₀ a r) g ∈ oneOneCoeff 𝔇 :=
  glueCoeff_mem_oneOneCoeff 𝔇 (smoothOnOverlaps_mlCocycle hiso)
    isOverlapCocycle_mlCocycle (holomorphicOnOverlaps_mlCocycle hiso) hg

end Hypotheses

/-! ### The R5-style integral engine, with the smeared pole `B = ρ_{j₀}·P`

The ML split collapses as `s_j = B − p_j` with `B := ρ_{j₀}·mlPrincipal` (the
smeared pole, `mlSmeared`).  Off the pole this is exactly the R5 coboundary
mechanism (Leibniz + planar Stokes + relocation + PoU-reinsertion kill); the
single surviving term is the chart-`j₀` Stokes integral, which is the smeared
simple-pole model of R0 (`integral_dbar_smearedSimplePole`, i.e.
`DbarDisk.cauchyPompeiu_area` at the pole).  Near the pole every relocation
weight is locally constant (`MLIsolated` + closed-support clearance forces
`ρ_k ≡ 0` for `k ≠ j₀`, hence `ρ_{j₀} ≡ 1`), which supplies the smoothness
clearance the R5 lemmas got from global smoothness of `pouAverage`. -/

/-- The **smeared pole** `B := ρ_{j₀}·P` — the ML analogue of R5's `pouAverage`.
Smooth away from `a`; near `a` it agrees with the honest principal part (since
`ρ_{j₀} ≡ 1` there by isolation). -/
private def mlSmeared (j₀ : 𝔇.toFiniteCover.ι) (a : X) (r : ℂ) : X → ℂ :=
  fun y => rhoC 𝔇 j₀ y * mlPrincipal 𝔇 j₀ a r y

@[simp] private theorem mlSmeared_apply (j₀ : 𝔇.toFiniteCover.ι) (a : X) (r : ℂ) (y : X) :
    mlSmeared 𝔇 j₀ a r y = rhoC 𝔇 j₀ y * mlPrincipal 𝔇 j₀ a r y := rfl

section MLTieEngine

variable {𝔇} {j₀ : 𝔇.toFiniteCover.ι} {a : X} {r : ℂ} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}

/-- A PoU weight vanishes off its total support (value form). -/
private theorem rhoC_eq_zero_of_notMem_tsupport {k : 𝔇.toFiniteCover.ι} {y : X}
    (hy : y ∉ tsupport (cechPoU 𝔇 k)) : rhoC 𝔇 k y = 0 := by
  simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM, image_eq_zero_of_notMem_tsupport hy]
  rfl

/-- Near the isolated pole, every off-index PoU weight vanishes identically
(its closed support is contained in a cover set missing `a`). -/
private theorem eventually_rhoC_eq_zero_near_pole (hiso : MLIsolated 𝔇 j₀ a)
    {k : 𝔇.toFiniteCover.ι} (hk : k ≠ j₀) : ∀ᶠ y in 𝓝 a, rhoC 𝔇 k y = 0 := by
  have hns : a ∉ tsupport (cechPoU 𝔇 k) := fun hs => hiso.2 k hk (cechPoU_subordinate 𝔇 k hs)
  filter_upwards [(isClosed_tsupport (cechPoU 𝔇 k)).isOpen_compl.mem_nhds hns] with y hy
  exact rhoC_eq_zero_of_notMem_tsupport hy

/-- Near the isolated pole, `∑ρ = 1` forces the distinguished weight to be `≡ 1`. -/
private theorem eventually_rhoC_eq_one_near_pole (hiso : MLIsolated 𝔇 j₀ a) :
    ∀ᶠ y in 𝓝 a, rhoC 𝔇 j₀ y = 1 := by
  have hall : ∀ᶠ y in 𝓝 a, ∀ k ∈ Finset.univ.erase j₀, rhoC 𝔇 k y = 0 :=
    (Filter.eventually_all_finset _).2 fun k hk =>
      eventually_rhoC_eq_zero_near_pole hiso (Finset.ne_of_mem_erase hk)
  filter_upwards [hall] with y hy
  have hs := sum_rhoC_apply 𝔇 y
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), Finset.sum_eq_zero hy, add_zero] at hs
  exact hs

private theorem rhoC_pole_eq_one (hiso : MLIsolated 𝔇 j₀ a) : rhoC 𝔇 j₀ a = 1 :=
  (eventually_rhoC_eq_one_near_pole hiso).self_of_nhds

/-- Every PoU weight is locally constant near the isolated pole. -/
private theorem exists_rhoC_eventuallyEq_const_near_pole (hiso : MLIsolated 𝔇 j₀ a)
    (k : 𝔇.toFiniteCover.ι) : ∃ c : ℂ, (fun y => rhoC 𝔇 k y) =ᶠ[𝓝 a] fun _ => c := by
  by_cases hk : k = j₀
  · subst hk
    exact ⟨1, eventually_rhoC_eq_one_near_pole hiso⟩
  · exact ⟨0, eventually_rhoC_eq_zero_near_pole hiso hk⟩

/-- **The ML split collapse** (pointwise, everywhere): `σ_j = B − p_j`. -/
private theorem pouSplit_mlCocycle (j : 𝔇.toFiniteCover.ι) (x : X) :
    pouSplit 𝔇 (mlCocycle 𝔇 j₀ a r) j x
      = mlSmeared 𝔇 j₀ a r x - mlPart 𝔇 j₀ a r j x := by
  have hterm : ∀ k, k ≠ j₀ → rhoC 𝔇 k x * mlPart 𝔇 j₀ a r k x = 0 := by
    intro k hk
    simp only [mlPart, if_neg hk, Pi.zero_apply, mul_zero]
  have hsum1 : (∑ k, rhoC 𝔇 k x * mlPart 𝔇 j₀ a r k x)
      = rhoC 𝔇 j₀ x * mlPrincipal 𝔇 j₀ a r x := by
    rw [Finset.sum_eq_single_of_mem j₀ (Finset.mem_univ _) fun k _ hk => hterm k hk]
    simp [mlPart]
  calc pouSplit 𝔇 (mlCocycle 𝔇 j₀ a r) j x
      = ∑ k, (rhoC 𝔇 k x * mlPart 𝔇 j₀ a r k x - rhoC 𝔇 k x * mlPart 𝔇 j₀ a r j x) := by
        rw [pouSplit_apply]
        exact Finset.sum_congr rfl fun k _ => by simp only [mlCocycle]; ring
    _ = (∑ k, rhoC 𝔇 k x * mlPart 𝔇 j₀ a r k x)
        - (∑ k, rhoC 𝔇 k x) * mlPart 𝔇 j₀ a r j x := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = mlSmeared 𝔇 j₀ a r x - mlPart 𝔇 j₀ a r j x := by
        rw [hsum1, sum_rhoC_apply, one_mul, mlSmeared_apply]

/-- The chart-read split, as a function identity: `s̃_j = B̃_j − p̃_j`. -/
private theorem splitCoeff_mlCocycle (j : 𝔇.toFiniteCover.ι) :
    splitCoeff 𝔇 (mlCocycle 𝔇 j₀ a r) j
      = fun ζ => mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ)
          - mlPart 𝔇 j₀ a r j ((chartAt ℂ (𝔇.center j)).symm ζ) :=
  funext fun ζ => by rw [splitCoeff_apply, pouSplit_mlCocycle]

/-- The smeared pole is smooth away from `a` (the `gdTerm` support-aware gluing). -/
private theorem contMDiffAt_mlSmeared (hiso : MLIsolated 𝔇 j₀ a) {x : X} (hxa : x ≠ a) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (mlSmeared 𝔇 j₀ a r) x := by
  unfold mlSmeared
  by_cases hb : x ∈ tsupport (cechPoU 𝔇 j₀)
  · exact ((rhoC 𝔇 j₀).contMDiff x).mul
      (contMDiffAt_mlPrincipal hiso (cechPoU_subordinate 𝔇 j₀ hb) hxa)
  · refine (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport (cechPoU 𝔇 j₀)).isOpen_compl.mem_nhds hb] with y hy
    rw [rhoC_eq_zero_of_notMem_tsupport hy, zero_mul]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- Local variant of `contDiffAt_chartSymmRead`: the chart read of a function
`ContMDiffAt` at the read point is planar-smooth there. -/
private theorem contDiffAt_chartSymmRead_of_contMDiffAt {F : X → ℂ} {c : X} {z : ℂ}
    (hz : z ∈ (chartAt ℂ c).target)
    (hF : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) F ((chartAt ℂ c).symm z)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w => F ((chartAt ℂ c).symm w)) z := by
  have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (chartAt ℂ c).symm z :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := c) _ hz).contMDiffAt
      ((chartAt ℂ c).open_target.mem_nhds hz)
  exact contMDiffAt_iff_contDiffAt.1 (hF.comp z hsymm)

/-- The chart-`i` read of the smeared pole is planar-smooth at non-pole points. -/
private theorem contDiffAt_mlSmearedRead (hiso : MLIsolated 𝔇 j₀ a)
    {i : 𝔇.toFiniteCover.ι} {x : X} (hx : x ∈ (𝔇.U i : Set X)) (hxa : x ≠ a) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center i)).symm w)) (chartMap 𝔇 i x) := by
  have hsrc : x ∈ (chartAt ℂ (𝔇.center i)).source := mem_chartSource_of_mem_U 𝔇 hx
  have hli : (chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x) = x :=
    (chartAt ℂ (𝔇.center i)).left_inv hsrc
  refine contDiffAt_chartSymmRead_of_contMDiffAt
    ((chartAt ℂ (𝔇.center i)).map_source hsrc) ?_
  rw [hli]
  exact contMDiffAt_mlSmeared hiso hxa

/-- The `B̃·g` slot product is planar-smooth at non-pole image points. -/
private theorem contDiffAt_mlSmearedRead_mul (hiso : MLIsolated 𝔇 j₀ a)
    (hg : IsOneZeroCoeff 𝔇 g) {i : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U i : Set X)) (hxa : x ≠ a) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun ζ => mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center i)).symm ζ) * g i ζ)
      (chartMap 𝔇 i x) :=
  (contDiffAt_mlSmearedRead hiso hx hxa).mul
    (((hg.1 i x hx).restrictScalars (𝕜 := ℝ)).contDiffAt)

omit [Nonempty X] in
/-- The chart-`j₀` read of a function locally constant at `a` is locally constant
at the pole coordinate `α = chartMap 𝔇 j₀ a`. -/
private theorem eventuallyEq_chartSymmRead_near_pole (hiso : MLIsolated 𝔇 j₀ a)
    {F : X → ℂ} {c : ℂ} (hF : F =ᶠ[𝓝 a] fun _ => c) :
    (fun w => F ((chartAt ℂ (𝔇.center j₀)).symm w))
      =ᶠ[𝓝 (chartMap 𝔇 j₀ a)] fun _ => c := by
  have hsrc : a ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 hiso.1
  have hzt : chartMap 𝔇 j₀ a ∈ (chartAt ℂ (𝔇.center j₀)).target :=
    (chartAt ℂ (𝔇.center j₀)).map_source hsrc
  have hcont : ContinuousAt (chartAt ℂ (𝔇.center j₀)).symm (chartMap 𝔇 j₀ a) :=
    (chartAt ℂ (𝔇.center j₀)).symm.continuousAt
      (by rwa [(chartAt ℂ (𝔇.center j₀)).symm_source])
  have hli : (chartAt ℂ (𝔇.center j₀)).symm (chartMap 𝔇 j₀ a) = a :=
    (chartAt ℂ (𝔇.center j₀)).left_inv hsrc
  rw [ContinuousAt, hli] at hcont
  exact hcont.eventually hF

omit [Nonempty X] in
/-- `∂̄` of the chart-`j₀` read of a function locally constant at `a` vanishes
identically near the pole coordinate. -/
private theorem eventually_dbar_chartSymmRead_zero_near_pole (hiso : MLIsolated 𝔇 j₀ a)
    {F : X → ℂ} {c : ℂ} (hF : F =ᶠ[𝓝 a] fun _ => c) :
    ∀ᶠ w in 𝓝 (chartMap 𝔇 j₀ a),
      DbarDisk.dbar (fun ζ => F ((chartAt ℂ (𝔇.center j₀)).symm ζ)) w = 0 := by
  filter_upwards [(eventuallyEq_chartSymmRead_near_pole hiso hF).eventuallyEq_nhds] with w hw
  rw [dbar_congr_of_eventuallyEq hw]
  exact DbarDisk.dbar_const c w

/-- Near-pole clearance for the relocation weights: `∂̄ρ̃_k` (read in chart `j₀`)
vanishes identically near the pole coordinate, for EVERY `k`. -/
private theorem eventually_dbar_rhoC_read_zero_near_pole (hiso : MLIsolated 𝔇 j₀ a)
    (k : 𝔇.toFiniteCover.ι) :
    ∀ᶠ w in 𝓝 (chartMap 𝔇 j₀ a),
      DbarDisk.dbar (fun ζ => rhoC 𝔇 k ((chartAt ℂ (𝔇.center j₀)).symm ζ)) w = 0 := by
  obtain ⟨c, hc⟩ := exists_rhoC_eventuallyEq_const_near_pole hiso k
  exact eventually_dbar_chartSymmRead_zero_near_pole hiso hc

/-- The chart-pushed PoU weight `ρ̃_{j₀}` is `≡ 1` near the pole coordinate. -/
private theorem eventuallyEq_pouCoeff_one_near_pole (hiso : MLIsolated 𝔇 j₀ a) :
    pouCoeff 𝔇 j₀ =ᶠ[𝓝 (chartMap 𝔇 j₀ a)] fun _ => (1 : ℂ) := by
  have himg : chartMap 𝔇 j₀ a ∈ chartMap 𝔇 j₀ '' (𝔇.U j₀ : Set X) := ⟨a, hiso.1, rfl⟩
  filter_upwards [(isOpen_chartMap_image 𝔇 j₀ (𝔇.U j₀).isOpen (subset_refl _)).mem_nhds himg,
    eventuallyEq_chartSymmRead_near_pole hiso (eventually_rhoC_eq_one_near_pole hiso)]
    with w hw1 hw2
  rw [pouCoeff, Set.indicator_of_mem hw1]
  exact hw2

private theorem eventually_dbar_pouCoeff_zero_near_pole (hiso : MLIsolated 𝔇 j₀ a) :
    ∀ᶠ w in 𝓝 (chartMap 𝔇 j₀ a), DbarDisk.dbar (pouCoeff 𝔇 j₀) w = 0 := by
  filter_upwards [(eventuallyEq_pouCoeff_one_near_pole hiso).eventuallyEq_nhds] with w hw
  rw [dbar_congr_of_eventuallyEq hw]
  exact DbarDisk.dbar_const 1 w

/-- The relocation family `∂̄ρ_{jj} ∧ (B·ω₀)` is a `(1,1)` chart-coefficient
family — the ML analogue of R5's `isOneOneCoeff_dbarRead_mul` with the smeared
pole `B` in the scalar slot.  `B` is smooth only away from `a`, but at the pole
the `∂̄ρ̃_{jj}` factor vanishes on a whole neighbourhood (`ρ_{jj}` is locally
constant near `a`), so the family is locally zero there; the overlap law never
differentiates the scalar slot, so the R5 proof applies verbatim. -/
private theorem isOneOneCoeff_dbarRead_mul_mlSmeared (hiso : MLIsolated 𝔇 j₀ a)
    (hg : IsOneZeroCoeff 𝔇 g) (jj : 𝔇.toFiniteCover.ι) :
    IsOneOneCoeff 𝔇 fun i z =>
      DbarDisk.dbar (fun ζ => rhoC 𝔇 jj ((chartAt ℂ (𝔇.center i)).symm ζ)) z
        * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center i)).symm z) * g i z) := by
  constructor
  · intro i x hx
    by_cases hxa : x = a
    · subst hxa
      have hi : i = j₀ := by
        by_contra hi
        exact hiso.2 i hi hx
      subst hi
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [eventually_dbar_rhoC_read_zero_near_pole hiso jj] with w hw
      rw [hw, zero_mul]
    · have hzt : chartMap 𝔇 i x ∈ (chartAt ℂ (𝔇.center i)).target :=
        (chartAt ℂ (𝔇.center i)).map_source (mem_chartSource_of_mem_U 𝔇 hx)
      exact (ChartDiskCover.contDiffAt_dbar_chartDisk
        (contDiffAt_chartSymmRead (rhoC 𝔇 jj).contMDiff hzt)).mul
        (contDiffAt_mlSmearedRead_mul hiso hg hx hxa)
  · intro p q x hx
    have hxp : x ∈ (𝔇.U p : Set X) := hx.1
    have hxq : x ∈ (𝔇.U q : Set X) := hx.2
    have hzqt : chartMap 𝔇 q x ∈ (chartAt ℂ (𝔇.center q)).target :=
      (chartAt ℂ (𝔇.center q)).map_source (mem_chartSource_of_mem_U 𝔇 hxq)
    have htend : Tendsto (transitionMap 𝔇 p q) (𝓝 (chartMap 𝔇 p x))
        (𝓝 (chartMap 𝔇 q x)) := by
      have hc := (transitionMap_analyticAt 𝔇 hxp hxq).continuousAt
      rwa [ContinuousAt, transitionMap_chartMap 𝔇 hxp] at hc
    have hFev : (fun ζ => rhoC 𝔇 jj ((chartAt ℂ (𝔇.center q)).symm (transitionMap 𝔇 p q ζ)))
        =ᶠ[𝓝 (chartMap 𝔇 p x)] fun ζ => rhoC 𝔇 jj ((chartAt ℂ (𝔇.center p)).symm ζ) := by
      filter_upwards [symm_transitionMap_eventuallyEq 𝔇 hx] with ζ hζ
      rw [hζ]
    unfold OneOneLawAt
    filter_upwards [hFev.eventuallyEq_nhds, symm_transitionMap_eventuallyEq 𝔇 hx,
      (transitionMap_analyticAt 𝔇 hxp hxq).eventually_analyticAt,
      htend.eventually ((chartAt ℂ (𝔇.center q)).open_target.mem_nhds hzqt),
      hg.2 p q x hx] with z hzF hzsymm hzan hztgt hzg
    have h1 : DbarDisk.dbar (fun ζ => rhoC 𝔇 jj ((chartAt ℂ (𝔇.center p)).symm ζ)) z
        = DbarDisk.dbar
            (fun ζ => rhoC 𝔇 jj ((chartAt ℂ (𝔇.center q)).symm (transitionMap 𝔇 p q ζ))) z :=
      (dbar_congr_of_eventuallyEq hzF).symm
    have h2 := dbar_comp (f := fun ζ => rhoC 𝔇 jj ((chartAt ℂ (𝔇.center q)).symm ζ))
      (φ := transitionMap 𝔇 p q)
      ((contDiffAt_chartSymmRead (rhoC 𝔇 jj).contMDiff hztgt).differentiableAt (by simp))
      hzan.differentiableAt
    rw [Function.comp_def] at h2
    have hns : ((normSq (deriv (transitionMap 𝔇 p q) z) : ℝ) : ℂ)
        = deriv (transitionMap 𝔇 p q) z
            * (starRingEnd ℂ) (deriv (transitionMap 𝔇 p q) z) :=
      (Complex.mul_conj _).symm
    rw [h1, h2, hzg, ← hzsymm, hns]
    ring

/-- **The ML relocation step** — `integral_overlapTerm_relocate` with the smeared
pole `B` in place of the globally smooth `pouAverage` (R4's
`setIntegral_overlap_relocate` applied to the `(1,1)` family
`isOneOneCoeff_dbarRead_mul_mlSmeared`). -/
private theorem integral_overlapTerm_relocate_ml (hiso : MLIsolated 𝔇 j₀ a)
    (hg : IsOneZeroCoeff 𝔇 g) (j k : 𝔇.toFiniteCover.ι) :
    ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
        * (DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
      = ∫ z, pouCoeff 𝔇 k z
          * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
              * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) := by
  have hu : IsOneOneCoeff 𝔇 fun i z =>
      DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center i)).symm ζ)) z
        * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center i)).symm z) * g i z) :=
    isOneOneCoeff_dbarRead_mul_mlSmeared hiso hg j
  -- step 1: the chart-`j` integrand vanishes off the overlap image
  have hvan1 : ∀ z, z ∉ overlapImage 𝔇 j k →
      rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
        * (DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) = 0 := by
    intro z hz
    by_cases hzs : z ∈ chartMap 𝔇 j '' tsupport (cechPoU 𝔇 j)
    · obtain ⟨x, hxs, rfl⟩ := hzs
      have hxU : x ∈ (𝔇.U j : Set X) := cechPoU_subordinate 𝔇 j hxs
      have hxk : x ∉ (𝔇.U k : Set X) := fun hk => hz ⟨x, ⟨hxU, hk⟩, rfl⟩
      have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
        (chartAt ℂ (𝔇.center j)).left_inv (mem_chartSource_of_mem_U 𝔇 hxU)
      have hxsupp : x ∉ tsupport (cechPoU 𝔇 k) := fun hs => hxk (cechPoU_subordinate 𝔇 k hs)
      rw [hli, rhoC_eq_zero_of_notMem_tsupport hxsupp, zero_mul]
    · rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hzs, zero_mul, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan1]
  -- step 2: on the overlap image, `∂̄ρ̃_j` is the `∂̄` of the honest chart read
  have hcongr1 : ∀ z ∈ overlapImage 𝔇 j k,
      rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
        * (DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
      = rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center j)).symm ζ)) z
            * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
    intro z hz
    rw [dbar_pouCoeff_chartRead 𝔇 (Set.image_mono (fun y hy => hy.1) hz)]
  rw [MeasureTheory.setIntegral_congr_fun (isOpen_overlapImage 𝔇 j k).measurableSet hcongr1]
  -- step 3: relocate to chart `k` (the R4 lemma, with weight `ρ_k`)
  have hrel := setIntegral_overlap_relocate 𝔇 hu j k fun y => rhoC 𝔇 k y
  simp only [] at hrel
  rw [hrel]
  -- step 4: on the chart-`k` overlap image, the weight is the `pouCoeff` indicator
  have hcongr2 : ∀ z ∈ overlapImage 𝔇 k j,
      rhoC 𝔇 k ((chartAt ℂ (𝔇.center k)).symm z)
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center k)).symm z) * g k z))
      = pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) := by
    rintro z ⟨x, hx, rfl⟩
    have hli : (chartAt ℂ (𝔇.center k)).symm (chartMap 𝔇 k x) = x :=
      (chartAt ℂ (𝔇.center k)).left_inv (mem_chartSource_of_mem_U 𝔇 hx.1)
    rw [pouCoeff_chartMap 𝔇 hx.1, hli]
  rw [MeasureTheory.setIntegral_congr_fun (isOpen_overlapImage 𝔇 k j).measurableSet hcongr2]
  -- step 5: the chart-`k` integrand vanishes off the overlap image, re-extend to `ℂ`
  have hvan2 : ∀ z, z ∉ overlapImage 𝔇 k j →
      pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) = 0 := by
    intro z hz
    by_cases hzU : z ∈ chartMap 𝔇 k '' (𝔇.U k : Set X)
    · obtain ⟨x, hxU, rfl⟩ := hzU
      have hxj : x ∉ (𝔇.U j : Set X) := fun hj => hz ⟨x, ⟨hxU, hj⟩, rfl⟩
      have hxsupp : x ∉ tsupport (cechPoU 𝔇 j) := fun hs => hxj (cechPoU_subordinate 𝔇 j hs)
      have hzt : chartMap 𝔇 k x ∈ (chartAt ℂ (𝔇.center k)).target :=
        (chartAt ℂ (𝔇.center k)).map_source (mem_chartSource_of_mem_U 𝔇 hxU)
      have hli : (chartAt ℂ (𝔇.center k)).symm (chartMap 𝔇 k x) = x :=
        (chartAt ℂ (𝔇.center k)).left_inv (mem_chartSource_of_mem_U 𝔇 hxU)
      have hdz : DbarDisk.dbar
          (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) (chartMap 𝔇 k x) = 0 := by
        refine dbar_chartSymmRead_eq_zero hzt ?_
        rw [hli]
        filter_upwards [(isClosed_tsupport (cechPoU 𝔇 j)).isOpen_compl.mem_nhds hxsupp]
          with y hy
        exact rhoC_eq_zero_of_notMem_tsupport hy
      rw [hdz, zero_mul, mul_zero]
    · rw [show pouCoeff 𝔇 k z = 0 from Set.indicator_of_notMem hzU _, zero_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hvan2]

/-- **The ML reinsertion kill**: at fixed chart `k`, the relocated curvature
terms sum to zero — `∑_j ∂̄ρ̃_j = 0` on the chart image (`sum_dbar_rhoC_read`);
near the pole coordinate every `∂̄ρ̃_j`-read vanishes identically, supplying
the integrability clearance. -/
private theorem sum_integral_relocated_eq_zero_ml (hiso : MLIsolated 𝔇 j₀ a)
    (hg : IsOneZeroCoeff 𝔇 g) (k : 𝔇.toFiniteCover.ι) :
    ∑ j, ∫ z, pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) = 0 := by
  have hint : ∀ j ∈ (Finset.univ : Finset 𝔇.toFiniteCover.ι), Integrable fun z =>
      pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) := by
    intro j _
    have hcd : ContDiff ℝ (⊤ : ℕ∞) fun z => pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) := by
      refine contDiff_pouCoeff_mul 𝔇 ?_
      rintro z ⟨x, hxU, rfl⟩
      by_cases hxa : x = a
      · subst hxa
        have hk : k = j₀ := by
          by_contra hk
          exact hiso.2 k hk hxU
        subst hk
        refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        filter_upwards [eventually_dbar_rhoC_read_zero_near_pole hiso j] with w hw
        rw [hw, zero_mul]
      · exact (ChartDiskCover.contDiffAt_dbar_chartDisk (contDiffAt_chartSymmRead
          (rhoC 𝔇 j).contMDiff (chartMap_image_U_subset_target 𝔇 k ⟨x, hxU, rfl⟩))).mul
          (contDiffAt_mlSmearedRead_mul hiso hg hxU hxa)
    exact hcd.continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_pouCoeff 𝔇 k).mul_right
  rw [← integral_finsetSum Finset.univ hint]
  have hzero : (fun z => ∑ j, pouCoeff 𝔇 k z
      * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
          * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center k)).symm z) * g k z)))
      = fun _ => (0 : ℂ) := by
    funext z
    have hfac : ∀ j, pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center k)).symm z) * g k z))
        = (pouCoeff 𝔇 k z * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center k)).symm z) * g k z))
            * DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z :=
      fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => hfac j, ← Finset.mul_sum]
    by_cases hzU : z ∈ chartMap 𝔇 k '' (𝔇.U k : Set X)
    · rw [sum_dbar_rhoC_read 𝔇 k (chartMap_image_U_subset_target 𝔇 k hzU), mul_zero]
    · rw [show pouCoeff 𝔇 k z = 0 from Set.indicator_of_notMem hzU _, zero_mul, zero_mul]
  rw [hzero, integral_zero]

/-- **The surviving term — the smeared simple pole at `j₀`.**  The chart-`j₀`
Stokes integrand IS the R0 model datum `∂̄(χ'·(z − α)⁻¹)` with the C∞c cutoff
`χ' = r·ρ̃_{j₀}·(ρ_{j₀}∘chart⁻¹)·g̃` and `χ'(α) = r·g̃(α)` (both weights are `1`
at the pole), so the area integral is `−π·r·g̃(α)` by
`integral_dbar_smearedSimplePole` — i.e. `DbarDisk.cauchyPompeiu_area` at the
pole.  Constants cited from R0; never re-derived. -/
private theorem integral_dbar_pouCoeff_mlSmeared_pole (hiso : MLIsolated 𝔇 j₀ a)
    (hg : IsOneZeroCoeff 𝔇 g) :
    ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j₀ ζ
        * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)) z
      = -π * (r * g j₀ (chartMap 𝔇 j₀ a)) := by
  have hsrc : a ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 hiso.1
  have hli : (chartAt ℂ (𝔇.center j₀)).symm (chartMap 𝔇 j₀ a) = a :=
    (chartAt ℂ (𝔇.center j₀)).left_inv hsrc
  have hVeq : (fun ζ => pouCoeff 𝔇 j₀ ζ
        * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ))
      = fun ζ => (r * (pouCoeff 𝔇 j₀ ζ
          * (rhoC 𝔇 j₀ ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)))
        * (ζ - chartMap 𝔇 j₀ a)⁻¹ := by
    funext ζ
    by_cases hζ : ζ ∈ chartMap 𝔇 j₀ '' (𝔇.U j₀ : Set X)
    · have hri : chartMap 𝔇 j₀ ((chartAt ℂ (𝔇.center j₀)).symm ζ) = ζ :=
        (chartAt ℂ (𝔇.center j₀)).right_inv (chartMap_image_U_subset_target 𝔇 j₀ hζ)
      simp only [mlSmeared_apply, mlPrincipal, hri]
      ring
    · have h0 : pouCoeff 𝔇 j₀ ζ = 0 := Set.indicator_of_notMem hζ _
      rw [h0]
      ring
  have hχcd : ContDiff ℝ (⊤ : ℕ∞) fun ζ => r * (pouCoeff 𝔇 j₀ ζ
      * (rhoC 𝔇 j₀ ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)) := by
    refine contDiff_const.mul (contDiff_pouCoeff_mul 𝔇 ?_)
    rintro z ⟨x, hxU, rfl⟩
    exact (contDiffAt_chartSymmRead (rhoC 𝔇 j₀).contMDiff
      (chartMap_image_U_subset_target 𝔇 j₀ ⟨x, hxU, rfl⟩)).mul
      (((hg.1 j₀ x hxU).restrictScalars (𝕜 := ℝ)).contDiffAt)
  have hχcs : HasCompactSupport fun ζ => r * (pouCoeff 𝔇 j₀ ζ
      * (rhoC 𝔇 j₀ ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)) :=
    HasCompactSupport.mul_left ((hasCompactSupport_pouCoeff 𝔇 j₀).mul_right)
  calc ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j₀ ζ
        * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)) z
      = ∫ z, DbarDisk.dbar (fun ζ => (r * (pouCoeff 𝔇 j₀ ζ
            * (rhoC 𝔇 j₀ ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)))
          * (ζ - chartMap 𝔇 j₀ a)⁻¹) z := by rw [hVeq]
    _ = -π * (r * (pouCoeff 𝔇 j₀ (chartMap 𝔇 j₀ a)
          * (rhoC 𝔇 j₀ ((chartAt ℂ (𝔇.center j₀)).symm (chartMap 𝔇 j₀ a))
              * g j₀ (chartMap 𝔇 j₀ a)))) :=
        integral_dbar_smearedSimplePole hχcd hχcs (chartMap 𝔇 j₀ a)
    _ = -π * (r * g j₀ (chartMap 𝔇 j₀ a)) := by
        rw [hli, pouCoeff_chartMap 𝔇 hiso.1, rhoC_pole_eq_one hiso]
        ring

/-- Off the distinguished chart the Stokes term dies (planar Stokes atom: the
integrand is `∂̄` of a global C∞c function — no pole in sight, `a ∉ U j`). -/
private theorem integral_dbar_pouCoeff_mlSmeared_eq_zero (hiso : MLIsolated 𝔇 j₀ a)
    (hg : IsOneZeroCoeff 𝔇 g) {j : 𝔇.toFiniteCover.ι} (hj : j ≠ j₀) :
    ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
        * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z = 0 := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) fun ζ => pouCoeff 𝔇 j ζ
      * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ) := by
    refine contDiff_pouCoeff_mul 𝔇 ?_
    rintro z ⟨x, hxU, rfl⟩
    exact contDiffAt_mlSmearedRead_mul hiso hg hxU fun h => hiso.2 j hj (h ▸ hxU)
  exact integral_dbar_eq_zero hcd ((hasCompactSupport_pouCoeff 𝔇 j).mul_right)

/-- **The ML Leibniz/Stokes step** (per chart): the `j`-th summand of the
residue integral splits as the total-derivative (Stokes/Cauchy-Pompeiu) term
minus the PoU-reinserted curvature terms.  A.e. version of R5's
`integral_pouCoeff_glueCoeff_of_coboundary`: the pointwise Leibniz identity
holds off the (measure-zero) pole coordinate. -/
private theorem integral_pouCoeff_glueCoeff_ml (hiso : MLIsolated 𝔇 j₀ a)
    (hg : IsOneZeroCoeff 𝔇 g) (j : 𝔇.toFiniteCover.ι) :
    ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 (mlCocycle 𝔇 j₀ a r) g j z
      = (∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z)
        - ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
            * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
  -- the a.e. pointwise Leibniz identity (off the pole coordinate)
  have hpt : ∀ z : ℂ, z ≠ chartMap 𝔇 j₀ a →
      DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
          * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z
        = pouCoeff 𝔇 j z * glueCoeff 𝔇 (mlCocycle 𝔇 j₀ a r) g j z
          + DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z) := by
    intro z hz
    by_cases hzU : z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X)
    · obtain ⟨x, hxU, rfl⟩ := hzU
      have hxa : x ≠ a := by
        intro h
        have hj : j = j₀ := by
          by_contra hj
          exact hiso.2 j hj (h ▸ hxU)
        exact hz (by rw [h, hj])
      have hBd : DifferentiableAt ℝ
          (fun ζ => mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ))
          (chartMap 𝔇 j x) :=
        (contDiffAt_mlSmearedRead hiso hxU hxa).differentiableAt (by simp)
      have hgd : DifferentiableAt ℝ (g j) (chartMap 𝔇 j x) :=
        ((hg.1 j x hxU).restrictScalars (𝕜 := ℝ)).differentiableAt
      have hpdC : DifferentiableAt ℂ
          (fun ζ => mlPart 𝔇 j₀ a r j ((chartAt ℂ (𝔇.center j)).symm ζ))
          (chartMap 𝔇 j x) :=
        differentiableAt_mlPart_read hiso hxU hxa fun h => h ▸ hxU
      have hdbar_split : DbarDisk.dbar (splitCoeff 𝔇 (mlCocycle 𝔇 j₀ a r) j)
            (chartMap 𝔇 j x)
          = DbarDisk.dbar (fun ζ => mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ))
              (chartMap 𝔇 j x) := by
        rw [splitCoeff_mlCocycle j, DbarOpenDisk.dbar_sub hBd (hpdC.restrictScalars ℝ),
          DbarDisk.dbar_eq_zero_of_differentiableAt hpdC, sub_zero]
      have hdbarBg : DbarDisk.dbar
            (fun ζ => mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)
            (chartMap 𝔇 j x)
          = DbarDisk.dbar (fun ζ => mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ))
              (chartMap 𝔇 j x) * g j (chartMap 𝔇 j x) := by
        rw [dbar_mul hBd hgd,
          DbarDisk.dbar_eq_zero_of_differentiableAt (hg.1 j x hxU).differentiableAt,
          mul_zero, add_zero]
      have hdbarV : DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ))
            (chartMap 𝔇 j x)
          = DbarDisk.dbar (pouCoeff 𝔇 j) (chartMap 𝔇 j x)
              * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x))
                  * g j (chartMap 𝔇 j x))
            + pouCoeff 𝔇 j (chartMap 𝔇 j x)
              * DbarDisk.dbar
                  (fun ζ => mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)
                  (chartMap 𝔇 j x) :=
        dbar_mul ((contDiff_pouCoeff 𝔇 j).differentiable (by simp) _) (hBd.mul hgd)
      rw [glueCoeff_apply, hdbarV, hdbarBg, hdbar_split]
      ring
    · have hzs : z ∉ chartMap 𝔇 j '' tsupport (cechPoU 𝔇 j) := fun hc =>
        hzU (Set.image_mono (fun y hy => cechPoU_subordinate 𝔇 j hy) hc)
      have hP0 : pouCoeff 𝔇 j z = 0 := Set.indicator_of_notMem hzU _
      have hD0 : DbarDisk.dbar (pouCoeff 𝔇 j) z = 0 :=
        dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hzs
      have hV0 : DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
          * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z = 0 := by
        refine dbar_eq_zero_of_eventuallyEq_zero ?_
        filter_upwards [(isCompact_image_tsupport_cechPoU 𝔇
          j).isClosed.isOpen_compl.mem_nhds hzs] with ζ hζ
        rw [pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hζ, zero_mul]
      rw [hV0, hP0, hD0, zero_mul, zero_mul, add_zero]
  -- integrability bookkeeping
  have hIt : Integrable fun z => pouCoeff 𝔇 j z * glueCoeff 𝔇 (mlCocycle 𝔇 j₀ a r) g j z :=
    integrable_pouCoeff_mul 𝔇 (mlGlue_mem_oneOneCoeff hiso hg) j
  have hYcd : ContDiff ℝ (⊤ : ℕ∞) fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z) := by
    refine contDiff_of_chartImage_clearance 𝔇 (j := j) ?_ ?_
    · rintro z ⟨x, hxU, rfl⟩
      by_cases hxa : x = a
      · subst hxa
        have hj : j = j₀ := by
          by_contra hj
          exact hiso.2 j hj hxU
        subst hj
        refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        filter_upwards [eventually_dbar_pouCoeff_zero_near_pole hiso] with w hw
        rw [hw, zero_mul]
      · exact (ChartDiskCover.contDiffAt_dbar_chartDisk (contDiff_pouCoeff 𝔇 j).contDiffAt).mul
          (contDiffAt_mlSmearedRead_mul hiso hg hxU hxa)
    · intro z hz
      rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hz, zero_mul]
  have hYcs : HasCompactSupport fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    (DbarDisk.hasCompactSupport_dbar (hasCompactSupport_pouCoeff 𝔇 j)).mul_right
  have hIY : Integrable fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    hYcd.continuous.integrable_of_hasCompactSupport hYcs
  -- the pole coordinate is volume-negligible
  have hane : ∀ᵐ z : ℂ ∂volume, z ≠ chartMap 𝔇 j₀ a := by
    refine ae_iff.mpr ?_
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact measure_singleton _
  have hkey : ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
        * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z
      = (∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 (mlCocycle 𝔇 j₀ a r) g j z)
        + ∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z) := by
    rw [← integral_add hIt hIY]
    refine integral_congr_ae ?_
    filter_upwards [hane] with z hz
    exact hpt z hz
  -- PoU reinsertion of the curvature term
  have hreins : (∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
        * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
      = ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
    calc ∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
          * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
        = ∫ z, ∑ k, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
            * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          simp only [← Finset.sum_mul, sum_rhoC_apply, one_mul]
      _ = ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
            * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
          refine integral_finsetSum Finset.univ fun k _ => ?_
          have hcd : ContDiff ℝ (⊤ : ℕ∞) fun z =>
              rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
                * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                    * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) :=
            contDiff_of_chartImage_clearance 𝔇
              (fun z hz => (contDiffAt_chartSymmRead (rhoC 𝔇 k).contMDiff
                (chartMap_image_U_subset_target 𝔇 j hz)).mul hYcd.contDiffAt)
              (fun z hz => by
                rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hz, zero_mul, mul_zero])
          exact hcd.continuous.integrable_of_hasCompactSupport hYcs.mul_left
  rw [← hreins, hkey]
  ring

end MLTieEngine

section Tie

variable {𝔇} {j₀ : 𝔇.toFiniteCover.ι} {a : X} {r : ℂ}
variable {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}

/-- **R6 headline — the simple-pole Mittag-Leffler tie.** On an isolated
simple pole, the residue functional of the glued ML family is the residue
times the `dz`-slot value at the pole. -/
theorem resFunctional_mlGlue (hiso : MLIsolated 𝔇 j₀ a)
    (hg : IsOneZeroCoeff 𝔇 g) :
    resFunctional 𝔇 ⟨glueCoeff 𝔇 (mlCocycle 𝔇 j₀ a r) g,
        mlGlue_mem_oneOneCoeff hiso hg⟩
      = r * g j₀ (chartMap 𝔇 j₀ a) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- the relocated curvature double sum dies (R5 mechanism: relocate, swap, kill)
  have hcurv : ∑ j, ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
      * (DbarDisk.dbar (pouCoeff 𝔇 j) z
          * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) = 0 := by
    calc ∑ j, ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
        = ∑ j, ∑ k, ∫ z, pouCoeff 𝔇 k z
            * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
                * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
            integral_overlapTerm_relocate_ml hiso hg j k
      _ = ∑ k, ∑ j, ∫ z, pouCoeff 𝔇 k z
            * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
                * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) :=
          Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero fun k _ => sum_integral_relocated_eq_zero_ml hiso hg k
  -- the Stokes sum survives only at `j₀`, where it is the Cauchy-Pompeiu atom
  have hstokes : ∑ j, ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
      * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z
      = -π * (r * g j₀ (chartMap 𝔇 j₀ a)) := by
    calc ∑ j, ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
          * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z
        = ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j₀ ζ
            * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)) z :=
          Finset.sum_eq_single j₀
            (fun b _ hb => integral_dbar_pouCoeff_mlSmeared_eq_zero hiso hg hb)
            (fun h => absurd (Finset.mem_univ j₀) h)
      _ = -π * (r * g j₀ (chartMap 𝔇 j₀ a)) :=
          integral_dbar_pouCoeff_mlSmeared_pole hiso hg
  have hres : resIntegral 𝔇 (⟨glueCoeff 𝔇 (mlCocycle 𝔇 j₀ a r) g,
        mlGlue_mem_oneOneCoeff hiso hg⟩ : oneOneCoeff 𝔇)
      = -π * (r * g j₀ (chartMap 𝔇 j₀ a)) := by
    calc resIntegral 𝔇 (⟨glueCoeff 𝔇 (mlCocycle 𝔇 j₀ a r) g,
          mlGlue_mem_oneOneCoeff hiso hg⟩ : oneOneCoeff 𝔇)
        = ∑ j, ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 (mlCocycle 𝔇 j₀ a r) g j z := rfl
      _ = ∑ j, ((∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
              * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z)
            - ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
                * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                    * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z))) :=
          Finset.sum_congr rfl fun j _ => integral_pouCoeff_glueCoeff_ml hiso hg j
      _ = (∑ j, ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
              * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z)
            - ∑ j, ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
                * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                    * (mlSmeared 𝔇 j₀ a r ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
          rw [Finset.sum_sub_distrib]
      _ = -π * (r * g j₀ (chartMap 𝔇 j₀ a)) := by rw [hstokes, hcurv, sub_zero]
  rw [resFunctional_apply, hres, resNormalization]
  field_simp

/-- **The R0-contract sign test (END-TO-END):** a residue-1 datum with the
`dz`-slot normalized to `1` at the pole evaluates to EXACTLY `1`. -/
theorem resFunctional_mlCocycle_residue_one (hiso : MLIsolated 𝔇 j₀ a)
    (hg : IsOneZeroCoeff 𝔇 g) (hnorm : g j₀ (chartMap 𝔇 j₀ a) = 1) :
    resFunctional 𝔇 ⟨glueCoeff 𝔇 (mlCocycle 𝔇 j₀ a (1 : ℂ)) g,
        mlGlue_mem_oneOneCoeff hiso hg⟩ = 1 := by
  rw [resFunctional_mlGlue hiso hg, hnorm, mul_one]

end Tie

end Jacobians.Dolbeault.FineResidue
