/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FineResidue.CoboundaryVanish
import KirovDolbeault.Dolbeault.FineResidue.OmegaWitness
import KirovDolbeault.Dolbeault.HoloRep
import KirovDolbeault.Dolbeault.GlobalResidueConstruct

/-!
# R7 — the germ→coefficient descent: `resFunctional` becomes a functional on `cechH1 K`

The descent rung of the fine-sheaf residue ladder (`docs/planning/R6_HANDOFF.md`, "the prize
lap"): connect the **germ-level** Čech complex of the port (`CechComplex.lean`: cochains are
codiscrete germ classes `MGerm`, `cechH1 K = Z¹/B¹` via `submoduleOf`) to the **chart-coefficient**
fine-sheaf residue engine (lanes R0–R5: `resFunctional`, `glueCoeff`,
`resFunctional_eq_zero_of_coboundary`), producing the `resCocycle`/`vanish_coboundary` fields of
the port's isolated Cousin interface `CousinResidueData` (`GlobalResidueConstruct.lean`).

## The three layers

* **Extraction (`cocycleFn`).** A 1-cocycle `c ∈ Z¹(𝒪_K)` on the chart-disk cover assigns to each
  overlap a *codiscrete germ class*; raw representatives carry removable-singularity junk, so the
  extraction goes through the proven `holoFn` limit-repair (`HoloRep.lean`), which returns the
  honest analytic representative.  This needs the overlap germs to be `𝒪`-classes
  (`OmegaDGerm 0`), which holds when no pole of `K` lies on an overlap — the **K-point refinement
  discipline** of `Glue.lean`/`OmegaWitness.lean`, packaged here as `SeparatesPoles 𝔇 K` (poles
  of `K` lie in single cover sets).  Diagonal pairs get the zero function (the cocycle identity
  forces the diagonal germ to vanish).  The extracted family satisfies `SmoothOnOverlaps`,
  `IsOverlapCocycle`, `HolomorphicOnOverlaps`, so `glueCoeff 𝔇 (cocycleFn …) g ∈ oneOneCoeff 𝔇`
  by the R3 glue law, and `resFunctional` applies.

* **Linearity & well-definedness (`resCocycle`).** Different germ representatives agree
  *pointwise on the overlaps* (codiscrete agreement + continuity of the analytic representatives,
  `eq_at_of_toGerm_eq`), and `resFunctional ∘ glueCoeff` only ever reads overlap values
  (`resFunctional_congr_chartImage`), so `c ↦ resFunctional (glueCoeff (cocycleFn c) g)` is a
  ℂ-**linear** functional on `Z¹(𝒪_K)` — the `resCocycle` field.

* **Coboundary vanishing & the liftQ descent.** For a coboundary `δ⁰f` with `f` a 0-cochain of
  `𝒪`-classes (`sections0 0`), the extracted data is exactly the `(w, h)`-shape of R5's
  `resFunctional_eq_zero_of_coboundary`, so the functional kills it
  (`resCocycle_eq_zero_of_holomorphic_coboundary`).  When `K ≤ 0` (in particular `K = 0`, the
  genus-1 canonical divisor) **every** coboundary is of this shape, giving the full
  `vanish_coboundary` field (`resCocycle_vanish_coboundary_of_nonpos`) and hence the descended
  functional on `cechH1 K` (`Submodule.liftQ`, exactly the port's `CousinResidueData.res`
  packaging).  For `K > 0` somewhere (genus ≥ 2), coboundary 0-cochains of `𝒪_K` carry *scalar*
  poles at the K-points (the forms `h·ω₀` are holomorphic, the scalars are not), and their
  vanishing is the residue-theorem leg that needs the (higher-order) Mittag–Leffler tie — a
  genuine R6-class gap, taken as a hypothesis here and recorded in
  `docs/planning/R7_BLOCKER.md`.

## Conditionality on R6 (in flight, separate branch)

`MLTie.lean` is being finished in parallel and is **not imported**.  Its outputs are packaged as
the hypothesis structure `R6Outputs`, whose fields copy the statement shapes of the in-flight
`resFunctional_mlGlue` / `resFunctional_mlCocycle_residue_one` *verbatim* (over local copies of
the ML-datum definitions in the `R6Shape` namespace, same orientation contract
`w i j = p_i − p_j`).  When R6 lands, `R6Outputs` is inhabited by a two-line bridge.  The final
assembly `cousinResidueData_of_descent` builds the port's `CousinResidueData 𝔇.toFiniteCover K`
from the proven `resCocycle` plus the two named open legs (`hvanish`, `hnondeg`).

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.2–17.6.
-/

open Complex Filter MeasureTheory
open scoped Manifold ContDiff Topology Classical
open TopologicalSpace (Opens)

-- Same permissive transparency as the sibling FineResidue files (the `SmoothCFunctions`
-- coercions of `rhoC` need it).
set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable (𝔇 : ChartDiskCover X)

/-! ### A. Germ classes pin continuous representatives pointwise

`MGerm` identifies functions agreeing off a discrete set.  On a Riemann surface no point is
isolated (`nhdsNE_neBot`), so two representatives that are *continuous* at a point of the open
agree **at** the point: codiscrete agreement gives punctured-neighbourhood agreement, and both
values are the (unique) limits. -/

omit [Nonempty X] in
/-- **Continuous representatives of equal germ classes agree pointwise.**  If the `↥V`-germ
classes of `f, f' : X → ℂ` agree and both are continuous at `x ∈ V`, then `f x = f' x`. -/
theorem eq_at_of_toGerm_eq {V : Opens X} {f f' : X → ℂ}
    (hg : toGerm V (fun v => f v.1) = toGerm V (fun v => f' v.1))
    {x : X} (hx : x ∈ V) (hf : ContinuousAt f x) (hf' : ContinuousAt f' x) :
    f x = f' x := by
  haveI := nhdsNE_neBot x
  rw [toGerm_eq_iff] at hg
  have hev : f =ᶠ[𝓝[≠] x] f' := by
    refine eventually_nhdsNE_of_subtype hx (fun z => f z = f' z) ?_
    filter_upwards [hg ⟨x, hx⟩] with w hw
    exact hw
  have h1 : Tendsto f (𝓝[≠] x) (𝓝 (f x)) := hf.continuousWithinAt.tendsto
  have h2 : Tendsto f (𝓝[≠] x) (𝓝 (f' x)) :=
    (hf'.continuousWithinAt.tendsto).congr' hev.symm
  exact tendsto_nhds_unique h1 h2

/-! ### B. Pole separation and the `𝒪_K ⊆ 𝒪` comparison off the poles -/

omit [Nonempty X] in
/-- Where `K ≤ 0`, sections of `𝒪_K` are sections of `𝒪` (the order bound `≥ −K ≥ 0` is at least
the holomorphy bound). -/
theorem OmegaD_le_zero_of_nonpos {K : Divisor X} {V : Opens X} (hK : ∀ x ∈ V, K x ≤ 0) :
    OmegaD K V ≤ OmegaD (0 : Divisor X) V := by
  rintro f ⟨hmer, hord⟩
  refine ⟨hmer, fun v => le_trans ?_ (hord v)⟩
  have h0 : ((0 : Divisor X) v.1 : ℤ) = 0 := rfl
  have e1 : -(((0 : Divisor X) v.1 : ℤ) : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by
    rw [h0]; simp
  have e2 : -((K v.1 : ℤ) : WithTop ℤ) = ((-(K v.1) : ℤ) : WithTop ℤ) := rfl
  rw [e1, e2]
  exact_mod_cast neg_nonneg.mpr (hK v.1 v.2)

omit [Nonempty X] in
/-- Germ-class version of `OmegaD_le_zero_of_nonpos`. -/
theorem OmegaDGerm_le_zero_of_nonpos {K : Divisor X} {V : Opens X} (hK : ∀ x ∈ V, K x ≤ 0) :
    OmegaDGerm K V ≤ OmegaDGerm (0 : Divisor X) V :=
  Submodule.map_mono (OmegaD_le_zero_of_nonpos hK)

/-- **The K-point refinement discipline of the chart-disk cover** (the cover constraint recorded
in `Glue.lean` / `OmegaWitness.lean` / `R_LANE_PROGRESS.log`): on every overlap of two *distinct*
cover sets the divisor `K` is non-positive — equivalently, each pole of `K` lies in a single
cover set.  Under this, `𝒪_K`-germs on overlaps are honest `𝒪`-germs, which is what the
`holoFn` extraction consumes.  At `K = 0` (genus 1) every cover qualifies. -/
def SeparatesPoles (K : Divisor X) : Prop :=
  ∀ i j : 𝔇.toFiniteCover.ι, i ≠ j → ∀ x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X), K x ≤ 0

omit [Nonempty X] in
theorem separatesPoles_of_nonpos {K : Divisor X} (hK : ∀ x, K x ≤ 0) :
    SeparatesPoles 𝔇 K :=
  fun _ _ _ x _ => hK x

/-! ### C. The germ→chart-coefficient extraction -/

variable {K : Divisor X}

omit [Nonempty X] in
/-- Off-diagonal overlap germs of a `Z¹(𝒪_K)`-cocycle are `𝒪`-classes (pole separation). -/
theorem cocycle_pair_mem_zero (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) {i j : 𝔇.toFiniteCover.ι}
    (hij : i ≠ j) :
    (c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) (i, j)
      ∈ OmegaDGerm (0 : Divisor X) (𝔇.U i ⊓ 𝔇.U j) :=
  OmegaDGerm_le_zero_of_nonpos (fun x hx => hsep i j hij x hx) (c.2.2 (i, j))

/-- **The germ→chart-coefficient extraction**: the scalar overlap family of a Čech 1-cocycle
`c ∈ Z¹(𝒪_K)` on the chart-disk cover.  Off the diagonal it is the canonical analytic
representative (`holoFn`, the limit-repair that discards codiscrete junk) of the overlap germ
`c (i,j)`; on the diagonal it is `0` (the value the cocycle identity forces).  Values off the
overlaps are junk and never consumed (the R1/R2 membership-guarded discipline). -/
noncomputable def cocycleFn (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) :
    𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ :=
  fun i j => if h : i = j then 0 else holoFn (cocycle_pair_mem_zero 𝔇 hsep c h)

omit [Nonempty X] in
@[simp] theorem cocycleFn_diag (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) (j : 𝔇.toFiniteCover.ι) :
    cocycleFn 𝔇 hsep c j j = 0 := by
  simp [cocycleFn]

omit [Nonempty X] in
/-- The extraction reads back the germ on its own overlap (off-diagonal). -/
theorem toGerm_cocycleFn (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) {i j : 𝔇.toFiniteCover.ι}
    (hij : i ≠ j) :
    toGerm (𝔇.U i ⊓ 𝔇.U j) (fun v => cocycleFn 𝔇 hsep c i j v.1)
      = (c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) (i, j) := by
  simp only [cocycleFn, dif_neg hij]
  exact toGerm_holoFn _

omit [Nonempty X] in
/-- The extraction reads back the *restricted* germ on any sub-open of its overlap. -/
theorem toGerm_cocycleFn_restrict (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) {i j : 𝔇.toFiniteCover.ι}
    (hij : i ≠ j) {V : Opens X} (hV : V ≤ 𝔇.U i ⊓ 𝔇.U j) :
    toGerm V (fun v => cocycleFn 𝔇 hsep c i j v.1)
      = rawRestrictG hV ((c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) (i, j)) := by
  rw [← toGerm_cocycleFn 𝔇 hsep c hij, rawRestrictG_coe]
  rfl

omit [Nonempty X] in
/-- The extraction is real-smooth at every point of its overlap. -/
theorem contMDiffAt_cocycleFn (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) {i j : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X)) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (cocycleFn 𝔇 hsep c i j) x := by
  by_cases h : i = j
  · simp only [cocycleFn, dif_pos h]
    exact contMDiffAt_const
  · simp only [cocycleFn, dif_neg h]
    exact holoFn_contMDiffAt _ hx

omit [Nonempty X] in
/-- The extraction is continuous at every point of its overlap. -/
theorem continuousAt_cocycleFn (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) {i j : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X)) :
    ContinuousAt (cocycleFn 𝔇 hsep c i j) x :=
  (contMDiffAt_cocycleFn 𝔇 hsep c hx).continuousAt

omit [Nonempty X] in
/-- **The extraction is smooth on overlaps** (R2 input predicate). -/
theorem smoothOnOverlaps_cocycleFn (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) :
    SmoothOnOverlaps 𝔇 (cocycleFn 𝔇 hsep c) :=
  fun _ _ _ hx => contMDiffAt_cocycleFn 𝔇 hsep c hx

omit [Nonempty X] in
/-- **The extraction is holomorphic on overlaps** (R3 input predicate): the analytic
representative's own-chart analyticity (`holoFn_chart_analyticAt`) relocated to the cover chart
(`analyticAt_chart_change_to`). -/
theorem holomorphicOnOverlaps_cocycleFn (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) :
    HolomorphicOnOverlaps 𝔇 (cocycleFn 𝔇 hsep c) := by
  intro i j x hx
  by_cases h : i = j
  · simp only [cocycleFn, dif_pos h, Pi.zero_apply]
    exact differentiableAt_const _
  · simp only [cocycleFn, dif_neg h]
    have ha := holoFn_chart_analyticAt (cocycle_pair_mem_zero 𝔇 hsep c h) hx
    exact (analyticAt_chart_change_to (mem_chartSource_of_mem_U 𝔇 hx.1) ha).differentiableAt

/-! ### The cocycle identity, from germs to points

The Čech cocycle identity (`c ∈ ker δ¹`) is an `MGerm` identity on triple overlaps; the analytic
representatives are continuous there, so it holds pointwise (`eq_at_of_toGerm_eq`).  Diagonal
pairs are handled by the forced vanishing of the diagonal germs. -/

omit [Nonempty X] in
/-- The Čech 1-cocycle identity of `c`, evaluated at a triple `(a, b, c')`, as an `MGerm`
identity on the triple overlap (the value-level unfolding of `cechDelta1 c = 0`). -/
theorem cocycle_germ_identity (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K))
    (a b c' : 𝔇.toFiniteCover.ι) :
    rawRestrictG (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        ((c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) (b, c'))
      - rawRestrictG (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
          ((c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) (a, c'))
      + rawRestrictG inf_le_left
          ((c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) (a, b)) = 0 := by
  have hker : 𝔇.toFiniteCover.toFiniteFamily.cechDelta1
      (c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) = 0 :=
    LinearMap.mem_ker.mp c.2.1
  have h := congrFun hker (a, b, c')
  simpa only [FiniteFamily.cechDelta1, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.proj_apply, Pi.zero_apply] using h

omit [Nonempty X] in
/-- **The diagonal germs of a 1-cocycle vanish** (after restriction below a triple overlap
`U b ⊓ U a ⊓ U a`): the cocycle identity at `(b, a, a)` telescopes to the diagonal alone. -/
theorem cocycle_diag_restrict_eq_zero (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K))
    (a b : 𝔇.toFiniteCover.ι) :
    rawRestrictG (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        (𝔇.U b ⊓ 𝔇.U a ⊓ 𝔇.U a : Opens X) ≤ 𝔇.U a ⊓ 𝔇.U a)
      ((c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) (a, a)) = 0 := by
  have h := cocycle_germ_identity 𝔇 c b a a
  -- the two `(b, a)`-restrictions are along proofs of the same `≤`, hence equal terms
  have hpe : rawRestrictG
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          (𝔇.U b ⊓ 𝔇.U a ⊓ 𝔇.U a : Opens X) ≤ 𝔇.U b ⊓ 𝔇.U a)
        ((c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) (b, a))
      = rawRestrictG inf_le_left
        ((c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) (b, a)) := rfl
  rw [hpe, sub_add_cancel] at h
  exact h

omit [Nonempty X] in
/-- Any further restriction of a diagonal cocycle germ vanishes. -/
theorem cocycle_diag_restrict_eq_zero' (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K))
    {a b : 𝔇.toFiniteCover.ι} {V : Opens X}
    (hV : V ≤ 𝔇.U b ⊓ 𝔇.U a ⊓ 𝔇.U a) (h2 : V ≤ 𝔇.U a ⊓ 𝔇.U a) :
    rawRestrictG h2 ((c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) (a, a)) = 0 := by
  calc rawRestrictG h2 ((c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) (a, a))
      = rawRestrictG hV (rawRestrictG
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            (𝔇.U b ⊓ 𝔇.U a ⊓ 𝔇.U a : Opens X) ≤ 𝔇.U a ⊓ 𝔇.U a)
          ((c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) (a, a))) :=
        (FiniteFamily.rawRestrictG_comp_apply _ _ _).symm
    _ = 0 := by rw [cocycle_diag_restrict_eq_zero 𝔇 c a b, map_zero]

omit [Nonempty X] in
/-- **The extraction is an overlap cocycle** (R2 input predicate): pointwise on every triple
overlap, from the germ-level `δ¹c = 0` through continuity of the analytic representatives. -/
theorem isOverlapCocycle_cocycleFn (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) :
    IsOverlapCocycle 𝔇 (cocycleFn 𝔇 hsep c) := by
  intro a b c' x hx
  by_cases hab : a = b
  · subst hab
    rw [cocycleFn_diag]
    simp
  by_cases hbc : b = c'
  · subst hbc
    rw [cocycleFn_diag]
    simp
  -- germ branch: `a ≠ b`, `b ≠ c'`; the middle pair may still be diagonal (`a = c'`)
  have h1 : (𝔇.U a ⊓ 𝔇.U b ⊓ 𝔇.U c' : Opens X) ≤ 𝔇.U b ⊓ 𝔇.U c' :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have h2 : (𝔇.U a ⊓ 𝔇.U b ⊓ 𝔇.U c' : Opens X) ≤ 𝔇.U a ⊓ 𝔇.U c' :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have h3 : (𝔇.U a ⊓ 𝔇.U b ⊓ 𝔇.U c' : Opens X) ≤ 𝔇.U a ⊓ 𝔇.U b := inf_le_left
  have hg1 := toGerm_cocycleFn_restrict 𝔇 hsep c hbc h1
  have hg3 := toGerm_cocycleFn_restrict 𝔇 hsep c hab h3
  have hg2 : toGerm (𝔇.U a ⊓ 𝔇.U b ⊓ 𝔇.U c')
      (fun v => cocycleFn 𝔇 hsep c a c' v.1)
      = rawRestrictG h2 ((c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) (a, c')) := by
    by_cases hac : a = c'
    · subst hac
      rw [cocycleFn_diag,
        cocycle_diag_restrict_eq_zero' 𝔇 c (b := b)
          (le_inf (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_right) h2]
      exact map_zero _
    · exact toGerm_cocycleFn_restrict 𝔇 hsep c hac h2
  have hsplit : (fun v : ↥(𝔇.U a ⊓ 𝔇.U b ⊓ 𝔇.U c') =>
        cocycleFn 𝔇 hsep c b c' v.1 - cocycleFn 𝔇 hsep c a c' v.1
          + cocycleFn 𝔇 hsep c a b v.1)
      = (fun v : ↥(𝔇.U a ⊓ 𝔇.U b ⊓ 𝔇.U c') => cocycleFn 𝔇 hsep c b c' v.1)
        - (fun v => cocycleFn 𝔇 hsep c a c' v.1)
        + fun v => cocycleFn 𝔇 hsep c a b v.1 := rfl
  have hgerm : toGerm (𝔇.U a ⊓ 𝔇.U b ⊓ 𝔇.U c')
      (fun v => cocycleFn 𝔇 hsep c b c' v.1 - cocycleFn 𝔇 hsep c a c' v.1
        + cocycleFn 𝔇 hsep c a b v.1)
      = toGerm (𝔇.U a ⊓ 𝔇.U b ⊓ 𝔇.U c') (fun v => (0 : X → ℂ) v.1) := by
    rw [hsplit, map_add, map_sub, hg1, hg2, hg3,
      cocycle_germ_identity 𝔇 c a b c']
    exact (map_zero _).symm
  have hpt := eq_at_of_toGerm_eq hgerm hx
    (((continuousAt_cocycleFn 𝔇 hsep c ⟨hx.1.2, hx.2⟩).sub
        (continuousAt_cocycleFn 𝔇 hsep c ⟨hx.1.1, hx.2⟩)).add
      (continuousAt_cocycleFn 𝔇 hsep c hx.1))
    continuousAt_const
  exact hpt

/-- **The R3 glue law applies to the extraction**: the glued `(1,1)` family of an extracted
cocycle against any holomorphic `(1,0)` slot family is a global `(1,1)` chart-coefficient
family. -/
theorem glueCoeff_cocycleFn_mem (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K))
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) :
    glueCoeff 𝔇 (cocycleFn 𝔇 hsep c) g ∈ oneOneCoeff 𝔇 :=
  glueCoeff_mem_oneOneCoeff 𝔇 (smoothOnOverlaps_cocycleFn 𝔇 hsep c)
    (isOverlapCocycle_cocycleFn 𝔇 hsep c) (holomorphicOnOverlaps_cocycleFn 𝔇 hsep c) hg

/-! ### E. The residue functional reads only overlap values

The PoU split consumes an overlap family only where some `ρ_k` survives — inside the overlaps —
and the integral functional only reads the chart images of the cover sets.  These congruence
atoms make the (choice-dependent) extraction well-defined and ℂ-linear after composition with
`resFunctional`. -/

/-- Overlap-equal families have equal PoU splits on each cover set. -/
theorem pouSplit_congr_of_overlap_eq {w w' : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    (hov : ∀ i j, ∀ x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X), w i j x = w' i j x)
    (j : 𝔇.toFiniteCover.ι) {x : X} (hx : x ∈ (𝔇.U j : Set X)) :
    pouSplit 𝔇 w j x = pouSplit 𝔇 w' j x := by
  simp only [pouSplit_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hb : x ∈ tsupport (cechPoU 𝔇 k)
  · rw [hov k j x ⟨cechPoU_subordinate 𝔇 k hb, hx⟩]
  · have hr : rhoC 𝔇 k x = 0 := by
      simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM, image_eq_zero_of_notMem_tsupport hb]
      rfl
    rw [hr, zero_mul, zero_mul]

/-- Chart-read splits of overlap-equal families agree near the chart image of the cover set. -/
theorem splitCoeff_eventuallyEq_of_overlap_eq
    {w w' : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    (hov : ∀ i j, ∀ x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X), w i j x = w' i j x)
    (j : 𝔇.toFiniteCover.ι) {x : X} (hx : x ∈ (𝔇.U j : Set X)) :
    splitCoeff 𝔇 w j =ᶠ[𝓝 (chartMap 𝔇 j x)] splitCoeff 𝔇 w' j := by
  have hxsrc : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hx
  have hzt : chartMap 𝔇 j x ∈ (chartAt ℂ (𝔇.center j)).target :=
    (chartAt ℂ (𝔇.center j)).map_source hxsrc
  have hcont : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) :=
    (chartAt ℂ (𝔇.center j)).symm.continuousAt
      (by rwa [(chartAt ℂ (𝔇.center j)).symm_source])
  have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
    (chartAt ℂ (𝔇.center j)).left_inv hxsrc
  have hovU : ((𝔇.U j : Opens X) : Set X)
      ∈ 𝓝 ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x)) := by
    rw [hli]
    exact (𝔇.U j).isOpen.mem_nhds hx
  filter_upwards [hcont.preimage_mem_nhds hovU] with z hz
  simp only [splitCoeff_apply]
  exact pouSplit_congr_of_overlap_eq 𝔇 hov j hz

/-- **The residue functional depends only on the chart-image values** of a `(1,1)` family (off
them, the `pouCoeff` indicator kills the integrand). -/
theorem resFunctional_congr_chartImage {t t' : oneOneCoeff 𝔇}
    (h : ∀ j, ∀ x ∈ (𝔇.U j : Set X),
      (t : 𝔇.toFiniteCover.ι → ℂ → ℂ) j (chartMap 𝔇 j x)
        = (t' : 𝔇.toFiniteCover.ι → ℂ → ℂ) j (chartMap 𝔇 j x)) :
    resFunctional 𝔇 t = resFunctional 𝔇 t' := by
  have hint : ∀ j, (fun z => pouCoeff 𝔇 j z * (t : 𝔇.toFiniteCover.ι → ℂ → ℂ) j z)
      = fun z => pouCoeff 𝔇 j z * (t' : 𝔇.toFiniteCover.ι → ℂ → ℂ) j z := by
    intro j
    funext z
    by_cases hz : z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X)
    · obtain ⟨x, hxU, rfl⟩ := hz
      rw [h j x hxU]
    · have h0 : pouCoeff 𝔇 j z = 0 := Set.indicator_of_notMem hz _
      rw [h0, zero_mul, zero_mul]
  rw [resFunctional_apply, resFunctional_apply]
  congr 1
  rw [resIntegral_apply, resIntegral_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [hint j]

/-! ### F. ℂ-linearity: the `resCocycle` field -/

omit [Nonempty X] in
/-- The extraction is additive on overlaps (germ addition + continuity). -/
theorem cocycleFn_add_overlap (hsep : SeparatesPoles 𝔇 K)
    (c c' : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) {i j : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X)) :
    cocycleFn 𝔇 hsep (c + c') i j x
      = cocycleFn 𝔇 hsep c i j x + cocycleFn 𝔇 hsep c' i j x := by
  by_cases h : i = j
  · subst h
    rw [cocycleFn_diag, cocycleFn_diag, cocycleFn_diag]
    simp
  · refine eq_at_of_toGerm_eq ?_ hx (continuousAt_cocycleFn 𝔇 hsep (c + c') hx)
      ((continuousAt_cocycleFn 𝔇 hsep c hx).add (continuousAt_cocycleFn 𝔇 hsep c' hx))
    show toGerm (𝔇.U i ⊓ 𝔇.U j) (fun v => cocycleFn 𝔇 hsep (c + c') i j v.1)
        = toGerm (𝔇.U i ⊓ 𝔇.U j)
            ((fun v : ↥(𝔇.U i ⊓ 𝔇.U j) => cocycleFn 𝔇 hsep c i j v.1)
              + fun v => cocycleFn 𝔇 hsep c' i j v.1)
    rw [map_add, toGerm_cocycleFn 𝔇 hsep (c + c') h, toGerm_cocycleFn 𝔇 hsep c h,
      toGerm_cocycleFn 𝔇 hsep c' h]
    rfl

omit [Nonempty X] in
/-- The extraction is homogeneous on overlaps. -/
theorem cocycleFn_smul_overlap (hsep : SeparatesPoles 𝔇 K) (a : ℂ)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) {i j : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X)) :
    cocycleFn 𝔇 hsep (a • c) i j x = a * cocycleFn 𝔇 hsep c i j x := by
  by_cases h : i = j
  · subst h
    rw [cocycleFn_diag, cocycleFn_diag]
    simp
  · refine eq_at_of_toGerm_eq ?_ hx (continuousAt_cocycleFn 𝔇 hsep (a • c) hx)
      (continuousAt_const.mul (continuousAt_cocycleFn 𝔇 hsep c hx))
    show toGerm (𝔇.U i ⊓ 𝔇.U j) (fun v => cocycleFn 𝔇 hsep (a • c) i j v.1)
        = toGerm (𝔇.U i ⊓ 𝔇.U j)
            (a • fun v : ↥(𝔇.U i ⊓ 𝔇.U j) => cocycleFn 𝔇 hsep c i j v.1)
    rw [map_smul, toGerm_cocycleFn 𝔇 hsep (a • c) h, toGerm_cocycleFn 𝔇 hsep c h]
    rfl

/-- The PoU split is additive in the overlap family. -/
theorem pouSplit_add_apply (w w' : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ)
    (j : 𝔇.toFiniteCover.ι) (x : X) :
    pouSplit 𝔇 (fun i j y => w i j y + w' i j y) j x
      = pouSplit 𝔇 w j x + pouSplit 𝔇 w' j x := by
  simp only [pouSplit_apply, mul_add, Finset.sum_add_distrib]

/-- The PoU split is homogeneous in the overlap family. -/
theorem pouSplit_smul_apply (a : ℂ) (w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ)
    (j : 𝔇.toFiniteCover.ι) (x : X) :
    pouSplit 𝔇 (fun i j y => a * w i j y) j x = a * pouSplit 𝔇 w j x := by
  simp only [pouSplit_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **The `resCocycle` field of the Cousin interface — the fine-sheaf residue as a ℂ-linear
functional on `Z¹(𝒪_K)`** (Forster §17.3, steps 1–4 composed): extract chart coefficients
(`cocycleFn`, through `holoFn`), glue against the `dz`-slot family `g` (R3), and integrate
(R4's `resFunctional`, normalized by the pinned R0 constant `resNormalization = −π⁻¹`).
Linearity holds because the functional only reads overlap values, where the extraction is
germ-determined, hence additive and homogeneous. -/
noncomputable def resCocycle (hsep : SeparatesPoles 𝔇 K) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ)
    (hg : IsOneZeroCoeff 𝔇 g) :
    ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K) →ₗ[ℂ] ℂ where
  toFun c := resFunctional 𝔇
    ⟨glueCoeff 𝔇 (cocycleFn 𝔇 hsep c) g, glueCoeff_cocycleFn_mem 𝔇 hsep c hg⟩
  map_add' c c' := by
    rw [← map_add (resFunctional 𝔇)]
    refine resFunctional_congr_chartImage 𝔇 fun j x hx => ?_
    have hov : ∀ i j', ∀ y ∈ (𝔇.U i ⊓ 𝔇.U j' : Opens X),
        cocycleFn 𝔇 hsep (c + c') i j' y
          = cocycleFn 𝔇 hsep c i j' y + cocycleFn 𝔇 hsep c' i j' y :=
      fun i j' y hy => cocycleFn_add_overlap 𝔇 hsep c c' hy
    have hev := splitCoeff_eventuallyEq_of_overlap_eq 𝔇 hov j hx
    have hsum : splitCoeff 𝔇
        (fun i j' y => cocycleFn 𝔇 hsep c i j' y + cocycleFn 𝔇 hsep c' i j' y) j
        = fun z => splitCoeff 𝔇 (cocycleFn 𝔇 hsep c) j z
            + splitCoeff 𝔇 (cocycleFn 𝔇 hsep c') j z := by
      funext z
      simp only [splitCoeff_apply, pouSplit_add_apply]
    have hda : DifferentiableAt ℝ (splitCoeff 𝔇 (cocycleFn 𝔇 hsep c) j)
        (chartMap 𝔇 j x) :=
      (contDiffAt_splitCoeff 𝔇 (smoothOnOverlaps_cocycleFn 𝔇 hsep c) j
        hx).differentiableAt (by simp)
    have hdb : DifferentiableAt ℝ (splitCoeff 𝔇 (cocycleFn 𝔇 hsep c') j)
        (chartMap 𝔇 j x) :=
      (contDiffAt_splitCoeff 𝔇 (smoothOnOverlaps_cocycleFn 𝔇 hsep c') j
        hx).differentiableAt (by simp)
    simp only [Submodule.coe_add, Pi.add_apply, glueCoeff_apply]
    rw [dbar_congr_of_eventuallyEq hev, hsum, DbarOpenDisk.dbar_add hda hdb]
    ring
  map_smul' a c := by
    rw [RingHom.id_apply, ← map_smul (resFunctional 𝔇)]
    refine resFunctional_congr_chartImage 𝔇 fun j x hx => ?_
    have hov : ∀ i j', ∀ y ∈ (𝔇.U i ⊓ 𝔇.U j' : Opens X),
        cocycleFn 𝔇 hsep (a • c) i j' y = a * cocycleFn 𝔇 hsep c i j' y :=
      fun i j' y hy => cocycleFn_smul_overlap 𝔇 hsep a c hy
    have hev := splitCoeff_eventuallyEq_of_overlap_eq 𝔇 hov j hx
    have hsm : splitCoeff 𝔇 (fun i j' y => a * cocycleFn 𝔇 hsep c i j' y) j
        = fun z => a * splitCoeff 𝔇 (cocycleFn 𝔇 hsep c) j z := by
      funext z
      simp only [splitCoeff_apply, pouSplit_smul_apply]
    have hda : DifferentiableAt ℝ (splitCoeff 𝔇 (cocycleFn 𝔇 hsep c) j)
        (chartMap 𝔇 j x) :=
      (contDiffAt_splitCoeff 𝔇 (smoothOnOverlaps_cocycleFn 𝔇 hsep c) j
        hx).differentiableAt (by simp)
    have hdmul : DbarDisk.dbar (fun z => a * splitCoeff 𝔇 (cocycleFn 𝔇 hsep c) j z)
        (chartMap 𝔇 j x)
        = a * DbarDisk.dbar (splitCoeff 𝔇 (cocycleFn 𝔇 hsep c) j) (chartMap 𝔇 j x) := by
      rw [dbar_mul (differentiableAt_const a) hda,
        DbarDisk.dbar_eq_zero_of_differentiableAt (differentiableAt_const a), zero_mul,
        zero_add]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, glueCoeff_apply]
    rw [dbar_congr_of_eventuallyEq hev, hsm, hdmul]
    ring

theorem resCocycle_apply (hsep : SeparatesPoles 𝔇 K) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ)
    (hg : IsOneZeroCoeff 𝔇 g) (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) :
    resCocycle 𝔇 hsep g hg c = resFunctional 𝔇
      ⟨glueCoeff 𝔇 (cocycleFn 𝔇 hsep c) g, glueCoeff_cocycleFn_mem 𝔇 hsep c hg⟩ :=
  rfl

/-! ### G. Coboundary vanishing and the `liftQ` descent

A Čech coboundary `δ⁰f` whose 0-cochain components are `𝒪`-classes extracts to exactly the
`(w, h)`-shape of R5's `resFunctional_eq_zero_of_coboundary`, so the functional kills it.  When
`K ≤ 0` (genus 1: `K = div ω₀ = 0`) every `B¹(𝒪_K)`-coboundary is of this shape and the full
`vanish_coboundary` field is **proven**; for `K` with positive part (genus ≥ 2) the remaining
leg — 0-cochains with scalar poles at the (cover-isolated) K-points — is the residue-theorem
content that needs the (higher-order) Mittag–Leffler tie, recorded in
`docs/planning/R7_BLOCKER.md` and taken as the `hvanish` hypothesis of the assembly. -/

/-- 0-cochain extraction: the analytic representative of each `𝒪`-class component. -/
noncomputable def cochainFn (f : 𝔇.toFiniteCover.toFiniteFamily.Cochain0)
    (hf : f ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 (0 : Divisor X)) :
    𝔇.toFiniteCover.ι → X → ℂ :=
  fun i => holoFn (hf i)

omit [Nonempty X] in
theorem smoothOnSets_cochainFn (f : 𝔇.toFiniteCover.toFiniteFamily.Cochain0)
    (hf : f ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 (0 : Divisor X)) :
    SmoothOnSets 𝔇 (cochainFn 𝔇 f hf) :=
  fun j _ hx => holoFn_contMDiffAt (hf j) hx

omit [Nonempty X] in
theorem holomorphicOnSets_cochainFn (f : 𝔇.toFiniteCover.toFiniteFamily.Cochain0)
    (hf : f ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 (0 : Divisor X)) :
    HolomorphicOnSets 𝔇 (cochainFn 𝔇 f hf) := by
  intro j x hx
  have ha := holoFn_chart_analyticAt (hf j) hx
  exact (analyticAt_chart_change_to (mem_chartSource_of_mem_U 𝔇 hx) ha).differentiableAt

omit [Nonempty X] in
/-- For a cocycle that **is** a coboundary `δ⁰f` of `𝒪`-classes, the extracted overlap family is
the coboundary of the extracted 0-cochain, pointwise on overlaps (the R5 input shape). -/
theorem isCoboundaryOn_cocycleFn_of_coboundary (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K))
    (f : 𝔇.toFiniteCover.toFiniteFamily.Cochain0)
    (hf : f ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 (0 : Divisor X))
    (hcb : (c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1)
      = 𝔇.toFiniteCover.toFiniteFamily.cechDelta0 f) :
    IsCoboundaryOn 𝔇 (cocycleFn 𝔇 hsep c) (cochainFn 𝔇 f hf) := by
  intro i j x hx
  by_cases h : i = j
  · subst h
    rw [cocycleFn_diag]
    simp
  · refine eq_at_of_toGerm_eq ?_ hx (continuousAt_cocycleFn 𝔇 hsep c hx)
      (((holoFn_contMDiffAt (hf j) hx.2).continuousAt).sub
        ((holoFn_contMDiffAt (hf i) hx.1).continuousAt))
    show toGerm (𝔇.U i ⊓ 𝔇.U j) (fun v => cocycleFn 𝔇 hsep c i j v.1)
        = toGerm (𝔇.U i ⊓ 𝔇.U j)
            ((fun v : ↥(𝔇.U i ⊓ 𝔇.U j) => cochainFn 𝔇 f hf j v.1)
              - fun v => cochainFn 𝔇 f hf i v.1)
    have hj : toGerm (𝔇.U i ⊓ 𝔇.U j) (fun v => cochainFn 𝔇 f hf j v.1)
        = rawRestrictG inf_le_right (f j) := by
      rw [← toGerm_holoFn (hf j), rawRestrictG_coe]
      rfl
    have hi : toGerm (𝔇.U i ⊓ 𝔇.U j) (fun v => cochainFn 𝔇 f hf i v.1)
        = rawRestrictG inf_le_left (f i) := by
      rw [← toGerm_holoFn (hf i), rawRestrictG_coe]
      rfl
    rw [map_sub, toGerm_cocycleFn 𝔇 hsep c h, hcb, hj, hi]
    simp only [FiniteFamily.cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]

/-- **The holomorphic-coboundary leg of `vanish_coboundary`** — R5's coboundary Stokes applied
through the extraction: the residue functional kills every coboundary of `𝒪`-class 0-cochains. -/
theorem resCocycle_eq_zero_of_holomorphic_coboundary (hsep : SeparatesPoles 𝔇 K)
    (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (hg : IsOneZeroCoeff 𝔇 g)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K))
    (f : 𝔇.toFiniteCover.toFiniteFamily.Cochain0)
    (hf : f ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 (0 : Divisor X))
    (hcb : (c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1)
      = 𝔇.toFiniteCover.toFiniteFamily.cechDelta0 f) :
    resCocycle 𝔇 hsep g hg c = 0 :=
  resFunctional_eq_zero_of_coboundary 𝔇 _ rfl hg (smoothOnSets_cochainFn 𝔇 f hf)
    (holomorphicOnSets_cochainFn 𝔇 f hf)
    (isCoboundaryOn_cocycleFn_of_coboundary 𝔇 hsep c f hf hcb)

/-- **The full `vanish_coboundary` field at `K ≤ 0`** (in particular the genus-1 canonical
divisor `K = 0`): every `B¹(𝒪_K)`-coboundary has `𝒪`-class components, so the holomorphic leg
covers all of `B¹` and the residue functional descends to `cechH1 K`. -/
theorem resCocycle_vanish_coboundary_of_nonpos (hsep : SeparatesPoles 𝔇 K)
    (hK : ∀ x, K x ≤ 0) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (hg : IsOneZeroCoeff 𝔇 g) :
    ∀ c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K),
      c ∈ (𝔇.toFiniteCover.toFiniteFamily.coboundaries1 K).submoduleOf
        (𝔇.toFiniteCover.toFiniteFamily.cocycles1 K) →
      resCocycle 𝔇 hsep g hg c = 0 := by
  intro c hc
  have hc' : (c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1)
      ∈ 𝔇.toFiniteCover.toFiniteFamily.coboundaries1 K := hc
  obtain ⟨f, hfK, hcb⟩ := hc'
  have hf0 : f ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 (0 : Divisor X) :=
    fun i => OmegaDGerm_le_zero_of_nonpos (fun x _ => hK x) (hfK i)
  exact resCocycle_eq_zero_of_holomorphic_coboundary 𝔇 hsep g hg c f hf0 hcb.symm

/-- **The `liftQ` descent — the fine-sheaf residue on Čech cohomology.**  Given the
coboundary-vanishing leg, `resCocycle` descends through the `Z¹/B¹` quotient to a ℂ-linear
functional on `cechH1 K` — exactly the `CousinResidueData.res` packaging of the port. -/
noncomputable def resH1 (hsep : SeparatesPoles 𝔇 K) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ)
    (hg : IsOneZeroCoeff 𝔇 g)
    (hvanish : ∀ c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K),
      c ∈ (𝔇.toFiniteCover.toFiniteFamily.coboundaries1 K).submoduleOf
        (𝔇.toFiniteCover.toFiniteFamily.cocycles1 K) →
      resCocycle 𝔇 hsep g hg c = 0) :
    𝔇.toFiniteCover.toFiniteFamily.cechH1 K →ₗ[ℂ] ℂ :=
  Submodule.liftQ _ (resCocycle 𝔇 hsep g hg) hvanish

@[simp] theorem resH1_mk (hsep : SeparatesPoles 𝔇 K) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ)
    (hg : IsOneZeroCoeff 𝔇 g) (hvanish) (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) :
    resH1 𝔇 hsep g hg hvanish (Submodule.Quotient.mk c) = resCocycle 𝔇 hsep g hg c :=
  rfl

/-- The descent, unconditional at `K ≤ 0` (the genus-1 leg). -/
noncomputable def resH1_of_nonpos (hK : ∀ x, K x ≤ 0) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ)
    (hg : IsOneZeroCoeff 𝔇 g) :
    𝔇.toFiniteCover.toFiniteFamily.cechH1 K →ₗ[ℂ] ℂ :=
  resH1 𝔇 (separatesPoles_of_nonpos 𝔇 hK) g hg
    (resCocycle_vanish_coboundary_of_nonpos 𝔇 (separatesPoles_of_nonpos 𝔇 hK) hK g hg)

/-! ### H. The R6 interface and the conditional Cousin assembly

`MLTie.lean` (rung R6, in flight on a parallel branch) is **not imported**: its outputs are
taken as the hypothesis structure `R6Outputs`, whose fields copy the statement shapes of the
in-flight `resFunctional_mlGlue` / `resFunctional_mlCocycle_residue_one` over local copies of
the ML-datum definitions (`R6Shape`, definition bodies verbatim from `MLTie.lean`, same
orientation contract `w i j = p_i − p_j`).  When R6 lands, instantiating `R6Outputs` is a
two-line bridge (`Subtype.ext` on the glued element). -/

namespace R6Shape

/-- The pole `a` lies in the cover set `U j₀` and in NO other cover set — the K-point/pole
refinement discipline.  (Shape copy of the in-flight `MLTie.MLIsolated`.) -/
def MLIsolated (j₀ : 𝔇.toFiniteCover.ι) (a : X) : Prop :=
  a ∈ (𝔇.U j₀ : Set X) ∧ ∀ i, i ≠ j₀ → a ∉ (𝔇.U i : Set X)

/-- The simple-pole principal part in the distinguished chart.  (Shape copy of the in-flight
`MLTie.mlPrincipal`.) -/
noncomputable def mlPrincipal (j₀ : 𝔇.toFiniteCover.ι) (a : X) (r : ℂ) : X → ℂ :=
  fun x => r * (chartMap 𝔇 j₀ x - chartMap 𝔇 j₀ a)⁻¹

/-- The one-point ML part family.  (Shape copy of the in-flight `MLTie.mlPart`.) -/
noncomputable def mlPart (j₀ : 𝔇.toFiniteCover.ι) (a : X) (r : ℂ) : 𝔇.toFiniteCover.ι → X → ℂ :=
  fun i => if i = j₀ then mlPrincipal 𝔇 j₀ a r else 0

/-- The simple-pole ML overlap cocycle, in the orientation the R6 sign test pins
(`w i j = p_i − p_j`).  (Shape copy of the in-flight `MLTie.mlCocycle`.) -/
noncomputable def mlCocycle (j₀ : 𝔇.toFiniteCover.ι) (a : X) (r : ℂ) :
    𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ :=
  fun i j x => mlPart 𝔇 j₀ a r i x - mlPart 𝔇 j₀ a r j x

end R6Shape

/-- **The R6 outputs, as a hypothesis structure** — exactly what the in-flight `MLTie.lean`
will provide (statement shapes copied verbatim, quantified over any `(1,1)` element whose
coefficients are the glued ML family, so the bridge from R6 is `Subtype.ext`):

* `resFunctional_mlGlue` — the simple-pole Mittag–Leffler tie: on an isolated simple pole the
  residue functional of the glued ML family is the residue times the `dz`-slot value at the
  pole;
* `resFunctional_mlCocycle_residue_one` — the R0-contract end-to-end sign test: a residue-1
  datum with slot value 1 evaluates to exactly `1` (under the pinned
  `resNormalization = −π⁻¹`). -/
structure R6Outputs : Prop where
  resFunctional_mlGlue :
    ∀ {j₀ : 𝔇.toFiniteCover.ι} {a : X} {r : ℂ} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ},
      R6Shape.MLIsolated 𝔇 j₀ a → IsOneZeroCoeff 𝔇 g →
      ∀ t : oneOneCoeff 𝔇,
        (t : 𝔇.toFiniteCover.ι → ℂ → ℂ) = glueCoeff 𝔇 (R6Shape.mlCocycle 𝔇 j₀ a r) g →
        resFunctional 𝔇 t = r * g j₀ (chartMap 𝔇 j₀ a)
  resFunctional_mlCocycle_residue_one :
    ∀ {j₀ : 𝔇.toFiniteCover.ι} {a : X} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ},
      R6Shape.MLIsolated 𝔇 j₀ a → IsOneZeroCoeff 𝔇 g → g j₀ (chartMap 𝔇 j₀ a) = 1 →
      ∀ t : oneOneCoeff 𝔇,
        (t : 𝔇.toFiniteCover.ι → ℂ → ℂ)
          = glueCoeff 𝔇 (R6Shape.mlCocycle 𝔇 j₀ a (1 : ℂ)) g →
        resFunctional 𝔇 t = 1

/-- **Glued-family congruence**: the residue functional of glued `(1,1)` elements agrees for
overlap-equal cocycle data (the functional never reads junk values off the overlaps). -/
theorem resFunctional_glueCoeff_congr
    {w w' : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    (hov : ∀ i j, ∀ x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X), w i j x = w' i j x)
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (t t' : oneOneCoeff 𝔇)
    (ht : (t : 𝔇.toFiniteCover.ι → ℂ → ℂ) = glueCoeff 𝔇 w g)
    (ht' : (t' : 𝔇.toFiniteCover.ι → ℂ → ℂ) = glueCoeff 𝔇 w' g) :
    resFunctional 𝔇 t = resFunctional 𝔇 t' := by
  refine resFunctional_congr_chartImage 𝔇 fun j x hx => ?_
  rw [ht, ht']
  simp only [glueCoeff_apply]
  rw [dbar_congr_of_eventuallyEq (splitCoeff_eventuallyEq_of_overlap_eq 𝔇 hov j hx)]

/-- **The §17.6 cup–ML witness transport** — the remaining genuinely-open §17.6 leg (see
`docs/planning/R7_BLOCKER.md` §2): for every nonzero `[f] ∈ L(K−D)` there is a class
`ξ ∈ H¹(𝒪_D)` whose cup product is represented by a cocycle whose extraction agrees on overlaps
with an *isolated simple-pole ML cocycle* of residue 1, slot-normalized at the pole (Forster
§17.6's `dz/z` datum, transported through the cup).  The final membership conjunct is the glued
ML family's `(1,1)`-membership (proven in the in-flight R6 as `mlGlue_mem_oneOneCoeff`). -/
def CupMLWitness (hsep : SeparatesPoles 𝔇 K) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) : Prop :=
  ∀ (D : Divisor X) (v : lSysModule (K - D)), v ≠ 0 →
    ∃ (ξ : 𝔇.toFiniteCover.toFiniteFamily.cechH1 D)
      (z : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K))
      (j₀ : 𝔇.toFiniteCover.ι) (a : X),
      R6Shape.MLIsolated 𝔇 j₀ a ∧ g j₀ (chartMap 𝔇 j₀ a) = 1 ∧
      cup (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) D K v ξ = Submodule.Quotient.mk z ∧
      (∀ i j, ∀ x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X),
        cocycleFn 𝔇 hsep z i j x = R6Shape.mlCocycle 𝔇 j₀ a (1 : ℂ) i j x) ∧
      glueCoeff 𝔇 (R6Shape.mlCocycle 𝔇 j₀ a (1 : ℂ)) g ∈ oneOneCoeff 𝔇

/-- **The `nondegenerate` field from the R6 tie + the witness transport**: the descended
residue of the cup is computed by the extraction-congruence (`resFunctional_glueCoeff_congr`)
against the ML representative, where the R6 sign-test gives exactly `1`. -/
theorem nondegenerate_of_r6 (hsep : SeparatesPoles 𝔇 K) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ)
    (hg : IsOneZeroCoeff 𝔇 g)
    (hvanish : ∀ c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K),
      c ∈ (𝔇.toFiniteCover.toFiniteFamily.coboundaries1 K).submoduleOf
        (𝔇.toFiniteCover.toFiniteFamily.cocycles1 K) →
      resCocycle 𝔇 hsep g hg c = 0)
    (hR6 : R6Outputs 𝔇) (hwit : CupMLWitness 𝔇 hsep g) :
    ∀ (D : Divisor X) (v : lSysModule (K - D)), v ≠ 0 →
      ∃ ξ : 𝔇.toFiniteCover.toFiniteFamily.cechH1 D,
        (Submodule.liftQ _ (resCocycle 𝔇 hsep g hg) hvanish)
          (cup (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) D K v ξ) = 1 := by
  intro D v hv
  obtain ⟨ξ, z, j₀, a, hiso, hnorm, hcup, hov, hmem⟩ := hwit D v hv
  refine ⟨ξ, ?_⟩
  rw [hcup]
  have h1 : (Submodule.liftQ _ (resCocycle 𝔇 hsep g hg) hvanish)
      (Submodule.Quotient.mk z) = resCocycle 𝔇 hsep g hg z := rfl
  rw [h1, resCocycle_apply]
  rw [resFunctional_glueCoeff_congr 𝔇 hov
    (⟨_, glueCoeff_cocycleFn_mem 𝔇 hsep z hg⟩ : oneOneCoeff 𝔇)
    (⟨_, hmem⟩ : oneOneCoeff 𝔇) rfl rfl]
  exact hR6.resFunctional_mlCocycle_residue_one hiso hg hnorm ⟨_, hmem⟩ rfl

/-! ### The assembled Cousin interface -/

/-- **The descent assembly of the port's isolated Cousin interface**
(`GlobalResidueConstruct.CousinResidueData`): the `resCocycle` field is the **proven** fine-sheaf
residue functional of this file; the two open legs are taken as named hypotheses —

* `hvanish` — the full coboundary vanishing (PROVEN at `K ≤ 0` by
  `resCocycle_vanish_coboundary_of_nonpos`; at general `K` the K-point-pole leg remains, see
  `docs/planning/R7_BLOCKER.md` §1);
* `hnondeg` — the §17.6 non-degeneracy (derivable from `R6Outputs` + `CupMLWitness` via
  `nondegenerate_of_r6`, see `cousinResidueData_of_r6`).

Feeding the result to `CousinResidueData.toGlobalResidue` →
`GlobalResidue.toSerreResidueRealization` (both PROVEN in the port) yields the full Serre
pairing, `pairing_injective`, `lDim_le_h1Dim`, and `toSerreDualityData`. -/
noncomputable def cousinResidueData_of_descent (hsep : SeparatesPoles 𝔇 K)
    (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (hg : IsOneZeroCoeff 𝔇 g)
    (hvanish : ∀ c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K),
      c ∈ (𝔇.toFiniteCover.toFiniteFamily.coboundaries1 K).submoduleOf
        (𝔇.toFiniteCover.toFiniteFamily.cocycles1 K) →
      resCocycle 𝔇 hsep g hg c = 0)
    (hnondeg : ∀ (D : Divisor X) (v : lSysModule (K - D)), v ≠ 0 →
      ∃ ξ : 𝔇.toFiniteCover.toFiniteFamily.cechH1 D,
        (Submodule.liftQ _ (resCocycle 𝔇 hsep g hg) hvanish)
          (cup (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) D K v ξ) = 1) :
    CousinResidueData 𝔇.toFiniteCover K where
  resCocycle := resCocycle 𝔇 hsep g hg
  vanish_coboundary := hvanish
  nondegenerate := hnondeg

/-- **`CousinResidueData`, conditionally on R6** — the headline conditional assembly: from the
in-flight R6 outputs (`R6Outputs`, the ML tie + sign test), the §17.6 witness transport
(`CupMLWitness`), and the coboundary-vanishing leg (`hvanish`, proven at `K ≤ 0`), the full
Cousin interface of the port assembles over the proven `resCocycle`.  The R6 tie genuinely
enters: it evaluates the descended residue on the cup against the transported `dz/z` witness
(`nondegenerate_of_r6`). -/
noncomputable def cousinResidueData_of_r6 (hsep : SeparatesPoles 𝔇 K)
    (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (hg : IsOneZeroCoeff 𝔇 g)
    (hR6 : R6Outputs 𝔇) (hwit : CupMLWitness 𝔇 hsep g)
    (hvanish : ∀ c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K),
      c ∈ (𝔇.toFiniteCover.toFiniteFamily.coboundaries1 K).submoduleOf
        (𝔇.toFiniteCover.toFiniteFamily.cocycles1 K) →
      resCocycle 𝔇 hsep g hg c = 0) :
    CousinResidueData 𝔇.toFiniteCover K :=
  cousinResidueData_of_descent 𝔇 hsep g hg hvanish
    (nondegenerate_of_r6 𝔇 hsep g hg hvanish hR6 hwit)

end Jacobians.Dolbeault.FineResidue
