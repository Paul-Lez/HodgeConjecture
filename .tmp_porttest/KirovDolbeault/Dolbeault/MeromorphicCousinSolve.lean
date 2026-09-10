/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.MeromorphicCousin
import KirovDolbeault.Dolbeault.GlobalResidueConstruct

/-!
# Forster §15 + §17.2–17.3 — the meromorphic Cousin solve, the distribution algebra, and the descent

This file continues `MeromorphicCousin.lean` (the connecting map `δ` and the residue calculus at the
genuine Forster `δμ ∈ Z¹(Ω)` strength).  Its goal is the wall `H¹(X, ℳ) = 0` (the `surjective` field
of `MeromorphicCousinSolvable`) and the mechanical descent that turns a Cousin solution into the
Serre residue functional.

## The `holoOff` gap (read first — a genuine soundness finding)

The committed `CoverMLDistribution 𝔘 ω₀ K` carries `diffMem`/`formHoloDiff` (the overlap conditions of
`δμ ∈ Z¹(Ω)`) and `iso` (isolated singularity at each recorded pole) — but **no `holoOff` field**
(holomorphy away from the recorded poles, as `GeneralMLDistribution` has).  Without it:

* its distribution **algebra is unbuildable**: `combine μ₁ μ₂`'s `iso` at a pole `a ∈ μ₁.poles \ μ₂.poles`
  needs `μ₂.g (μ₁.patch a)` isolated at `a`, which (when `a ∉ μ₂.poles`) is exactly `holoOff`; and
* `μ.res = ∑_{a ∈ poles} Resₐ` need **not be the genuine total residue** (a "global" pole of every `gᵢ`
  outside `poles`, cancelled in all differences, is invisible to `poles` yet contributes a residue).

So the descent's well-definedness `[δμ₁] = [δμ₂] ⟹ μ₁.res = μ₂.res` (via Gate A) genuinely needs
`holoOff`.  Rather than mutate the committed structure (and the proven connecting map), we introduce a
**richer lift** `CoverMLLift 𝔘 ω₀ K` (= `CoverMLDistribution` + `holoOff`), build the algebra and the
descent on it, and reduce the wall to a single precise Cousin atom on `CoverMLLift`.  A genuine Cousin
solution (the local-meromorphic lift of a cocycle) always has `holoOff`, so this is no loss.

## What this file delivers (complete, axiom-clean unless noted)

* `CoverMLLift 𝔘 ω₀ K` — the `holoOff`-equipped lift; `toDistribution` forgets `holoOff`, `res`/
  `connectingCocycle`/`connectingClass` inherited.
* The **distribution algebra**: `smul`, `neg`, `combine` (add), `sub`, each a genuine `CoverMLLift`,
  with `res_smul`/`res_neg`/`res_combine`/`res_sub` (res-additivity from `formFnResidue_add`/`_smul`)
  and `connectingCochain`/`connectingClass` additivity.
* `holoOff` gives that **`res` is the genuine total residue** (`res_eq_residueSum_of_subset`-style):
  every pole of every `gᵢ` is recorded, so `res` reads the full Laurent residue sum.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §15 (`H¹(X,ℳ)=0`), §17.2–17.3;
`MeromorphicCousin.lean`; `GeneralMittagLeffler.lean` (`res_eq_zero_of_globalMeromorphic`).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]

variable {𝔘 : FiniteCover X} {ω₀ : HolomorphicOneForms X} {K : Divisor X}

/-! ## The `holoOff`-equipped Cousin lift -/

/-- **A meromorphic Cousin lift** over the fixed cover `𝔘`: a `CoverMLDistribution` together with the
**off-poles holomorphy** field `holoOff` that the committed `CoverMLDistribution` omits (see the module
docstring).  A genuine Cousin solution (the local-meromorphic lift `gᵢ` of an `𝒪_K` cocycle) always has
it: away from the finitely many recorded poles each `gᵢ` is holomorphic.  With it the residue is the
genuine total residue and the distribution algebra (`combine`/`sub`) closes. -/
structure CoverMLLift (𝔘 : FiniteCover X) (ω₀ : HolomorphicOneForms X) (K : Divisor X) where
  /-- The underlying cover-adapted distribution (the data the connecting map δ consumes). -/
  toDistribution : CoverMLDistribution 𝔘 ω₀ K
  /-- **Off-poles holomorphy**: away from the recorded poles each `gᵢ`'s chart-pullback is analytic at
  every point of `𝔘.U i` (so `ωᵢ = gᵢ·ω₀` is holomorphic there). -/
  holoOff : ∀ (i : 𝔘.ι) (a : X), a ∈ 𝔘.U i → a ∉ toDistribution.poles →
    AnalyticAt ℂ (fun z => toDistribution.g i ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)

namespace CoverMLLift

variable (μ : CoverMLLift 𝔘 ω₀ K)

/-- The local principal part on patch `i`. -/
def g (i : 𝔘.ι) : X → ℂ := μ.toDistribution.g i

/-- The finite pole set. -/
def poles : Finset X := μ.toDistribution.poles

/-- The total residue of the lift (the underlying distribution's genuine Laurent residue sum). -/
noncomputable def res : ℂ := μ.toDistribution.res

/-- The connecting cocycle `δμ ∈ Z¹(𝔘, 𝒪_K)` (inherited from the underlying distribution). -/
noncomputable def connectingCocycle : ↥(𝔘.toFiniteFamily.cocycles1 K) :=
  μ.toDistribution.connectingCocycle

/-- The connecting class `[δμ] ∈ cechH1 K` (inherited). -/
noncomputable def connectingClass : 𝔘.toFiniteFamily.cechH1 K :=
  μ.toDistribution.connectingClass

theorem connectingClass_eq :
    μ.connectingClass = Submodule.Quotient.mk μ.connectingCocycle := rfl

@[simp] theorem res_def : μ.res = ∑ a ∈ μ.poles, formFnResidue ω₀ (μ.g (μ.toDistribution.patch a)) a :=
  CoverMLDistribution.res_def μ.toDistribution

/-- **Off poles, `ω₀·gᵢ` has an isolated singularity** (from `holoOff`).  At any `a ∉ poles` in
`𝔘.U i`, `gᵢ`'s chart-pullback is analytic, so `ω₀·gᵢ` is holomorphic — in particular isolated. -/
theorem formFnHoloPunctured_off (i : 𝔘.ι) {a : X} (ha : a ∈ 𝔘.U i) (hb : a ∉ μ.poles) :
    formFnHoloPunctured ω₀ (μ.g i) a :=
  formFnHoloPunctured_of_analyticAt ω₀ (μ.g i) a (μ.holoOff i a ha hb)

/-- **`ω₀·gᵢ` has an isolated singularity at every point of `𝔘.U i`** (genuine, from `iso` ∪ `holoOff`):
at recorded poles by `iso`/`formHoloDiff`, off them by `holoOff`.  This is the key fact the algebra and
the genuine-total-residue statement rest on. -/
theorem formFnHoloPunctured_everywhere (i : 𝔘.ι) {a : X} (ha : a ∈ 𝔘.U i) :
    formFnHoloPunctured ω₀ (μ.g i) a := by
  by_cases hb : a ∈ μ.poles
  · exact μ.toDistribution.toFormMLDistribution.formFnHoloPunctured_of_mem hb ha
  · exact μ.formFnHoloPunctured_off i ha hb

/-- **The residue of `ω₀·gᵢ` vanishes at a non-pole** of `𝔘.U i` (from `holoOff`): off the recorded
poles the form is holomorphic, residue `0`.  The key fact that makes `res` the genuine *total* residue
(extra points in any pole superset contribute nothing) and the distribution algebra close. -/
theorem formFnResidue_eq_zero_off (i : 𝔘.ι) {a : X} (ha : a ∈ 𝔘.U i) (hb : a ∉ μ.poles) :
    formFnResidue ω₀ (μ.g i) a = 0 :=
  formFnResidue_eq_zero_of_analyticAt ω₀ (μ.g i) a (μ.holoOff i a ha hb)

/-- **Cross-patch residue agreement** (the genuine Forster §17.2 patch-independence at full strength):
at any point `a` lying in both `𝔘.U i` and `𝔘.U j`, the residues of `ω₀·gᵢ` and `ω₀·gⱼ` agree, because
their form difference `(gᵢ − gⱼ)·ω₀` is holomorphic (`formHoloDiff`) and both are isolated. -/
theorem formFnResidue_patch_indep {i j : 𝔘.ι} {a : X} (hi : a ∈ 𝔘.U i) (hj : a ∈ 𝔘.U j) :
    formFnResidue ω₀ (μ.g i) a = formFnResidue ω₀ (μ.g j) a :=
  formFnResidue_eq_of_form_analyticAt_sub ω₀ (μ.g i) (μ.g j) a
    (μ.formFnHoloPunctured_everywhere i hi) (μ.toDistribution.formHoloDiff i j a hi hj)

/-! ### `res` as a residue-sum over any superset of the poles

The genuine total residue: for any finite `S ⊇ poles` such that every extra point lies in some patch
(automatic on a cover, where every point is in some `𝔘.U i`), the residue read at a point via *any*
patch containing it sums over `S` to `res` (the extra points are holomorphic, residue `0`).  This is
the bridge that makes `res` additive under `combine`. -/

/-- Every point of `X` lies in some patch of the cover `𝔘` (the cover is `⊤`). -/
theorem exists_patch (𝔘 : FiniteCover X) (a : X) : ∃ i, a ∈ 𝔘.U i := by
  have : a ∈ (⊤ : Opens X) := trivial
  rw [← 𝔘.covers] at this
  exact TopologicalSpace.Opens.mem_iSup.mp this

/-- A choice of patch containing `a` (well-defined on a genuine cover, where every point is covered). -/
noncomputable def patchOf (𝔘 : FiniteCover X) (a : X) : 𝔘.ι := (exists_patch 𝔘 a).choose

theorem patchOf_mem (𝔘 : FiniteCover X) (a : X) : a ∈ 𝔘.U (patchOf 𝔘 a) :=
  (exists_patch 𝔘 a).choose_spec

/-- **`res` as a residue-sum read via `patchOf` over the pole set.**  At each pole `a`, the residue
read via *any* patch containing `a` equals `resAtPole a` (patch-independence), so the `patchOf`-read
sum over `poles` is `res`. -/
theorem res_eq_sum_patchOf :
    μ.res = ∑ a ∈ μ.poles, formFnResidue ω₀ (μ.g (patchOf 𝔘 a)) a := by
  rw [CoverMLLift.res, CoverMLDistribution.res_def]
  refine Finset.sum_congr rfl fun a ha => ?_
  exact (μ.formFnResidue_patch_indep (patchOf_mem 𝔘 a) (μ.toDistribution.patch_mem a ha)).symm

/-- **`res` equals the `patchOf`-read residue-sum over any finite superset `S` of the poles** (the
genuine total residue): extra points of `S` are holomorphic (`formFnResidue_eq_zero_off`), residue `0`. -/
theorem res_eq_sum_patchOf_superset {S : Finset X} (hS : μ.poles ⊆ S) :
    μ.res = ∑ a ∈ S, formFnResidue ω₀ (μ.g (patchOf 𝔘 a)) a := by
  rw [μ.res_eq_sum_patchOf, ← Finset.sum_subset hS]
  intro a _ ha
  exact μ.formFnResidue_eq_zero_off (patchOf 𝔘 a) (patchOf_mem 𝔘 a) ha

/-! ### ℂ-scaling -/

/-- **ℂ-scaling** `c • μ`: scale each principal part by `c`; poles/patch/overlap structure unchanged
(`c • gᵢ` is analytic / isolated wherever `gᵢ` is, and `c • gᵢ − c • gⱼ = c • (gᵢ − gⱼ) ∈ 𝒪_K`). -/
noncomputable def smul (c : ℂ) (μ : CoverMLLift 𝔘 ω₀ K) : CoverMLLift 𝔘 ω₀ K where
  toDistribution :=
    { g := fun i => c • μ.g i
      poles := μ.poles
      patch := μ.toDistribution.patch
      patch_mem := μ.toDistribution.patch_mem
      diffMem := fun i j => by
        have h := μ.toDistribution.diffMem i j
        have heq : ((c • μ.g i - c • μ.g j) ∘ (Subtype.val : ↥(𝔘.U i ⊓ 𝔘.U j) → X))
            = c • ((μ.g i - μ.g j) ∘ (Subtype.val : ↥(𝔘.U i ⊓ 𝔘.U j) → X)) := by
          funext x
          simp only [Function.comp_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
        rw [heq]; exact Submodule.smul_mem _ c h
      formHoloDiff := fun i j a hi hj => by
        have h := μ.toDistribution.formHoloDiff i j a hi hj
        have heq : (fun z => coeffAt ω₀ a z * (c • μ.g i - c • μ.g j) ((chartAt ℂ a).symm z))
            = (fun z => c * (coeffAt ω₀ a z * (μ.g i - μ.g j) ((chartAt ℂ a).symm z))) := by
          funext z; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
        rw [heq]; exact analyticAt_const.mul h
      iso := fun a ha => by
        have h := μ.formFnHoloPunctured_everywhere (μ.toDistribution.patch a)
          (μ.toDistribution.patch_mem a ha)
        obtain ⟨ρ, hρ, hball⟩ := h
        refine ⟨ρ, hρ, fun z hz => ?_⟩
        have hd := hball z hz
        have heq : (fun z => coeffAt ω₀ a z * (c • μ.g (μ.toDistribution.patch a))
              ((chartAt ℂ a).symm z))
            = (fun z => c * (coeffAt ω₀ a z * μ.g (μ.toDistribution.patch a)
              ((chartAt ℂ a).symm z))) := by
          funext w; simp only [Pi.smul_apply, smul_eq_mul]; ring
        rw [heq]; exact hd.const_mul c }
  holoOff := fun i a ha hb => by
    have h := μ.holoOff i a ha hb
    have heq : (fun z => (c • μ.g i) ((chartAt ℂ a).symm z))
        = (fun z => c * μ.g i ((chartAt ℂ a).symm z)) := by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]
    rw [heq]; exact analyticAt_const.mul h

@[simp] theorem smul_g (c : ℂ) (μ : CoverMLLift 𝔘 ω₀ K) (i : 𝔘.ι) : (smul c μ).g i = c • μ.g i := rfl
@[simp] theorem smul_poles (c : ℂ) (μ : CoverMLLift 𝔘 ω₀ K) : (smul c μ).poles = μ.poles := rfl
@[simp] theorem smul_patch (c : ℂ) (μ : CoverMLLift 𝔘 ω₀ K) :
    (smul c μ).toDistribution.patch = μ.toDistribution.patch := rfl

/-- **`res (c • μ) = c · res μ`** (Forster §17.2 ℂ-homogeneity). -/
theorem res_smul (c : ℂ) (μ : CoverMLLift 𝔘 ω₀ K) : (smul c μ).res = c • μ.res := by
  rw [μ.res_eq_sum_patchOf, (smul c μ).res_eq_sum_patchOf, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [smul_g, smul_patch]
  exact formFnResidue_smul ω₀ c (μ.g (patchOf 𝔘 a)) a
    (μ.formFnHoloPunctured_everywhere (patchOf 𝔘 a) (patchOf_mem 𝔘 a))

/-! ### Additive combination -/

open scoped Classical in
/-- **Sum of two Cousin lifts** `combine μ₁ μ₂`: `gᵢ := μ₁.gᵢ + μ₂.gᵢ`, pole set the union, patch the
left one on `μ₁.poles` and the right one elsewhere.  All overlap conditions add (`𝒪_K` is a submodule,
analytic forms add); isolated/holomorphic structure adds via `formFnHoloPunctured_everywhere`/`holoOff`. -/
noncomputable def combine (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) : CoverMLLift 𝔘 ω₀ K where
  toDistribution :=
    { g := fun i => μ₁.g i + μ₂.g i
      poles := μ₁.poles ∪ μ₂.poles
      patch := fun a => if a ∈ μ₁.poles then μ₁.toDistribution.patch a else μ₂.toDistribution.patch a
      patch_mem := fun a ha => by
        by_cases h : a ∈ μ₁.poles
        · rw [if_pos h]; exact μ₁.toDistribution.patch_mem a h
        · rw [if_neg h]
          exact μ₂.toDistribution.patch_mem a ((Finset.mem_union.mp ha).resolve_left h)
      diffMem := fun i j => by
        have h1 := μ₁.toDistribution.diffMem i j
        have h2 := μ₂.toDistribution.diffMem i j
        have heq : ((μ₁.g i + μ₂.g i - (μ₁.g j + μ₂.g j))
              ∘ (Subtype.val : ↥(𝔘.U i ⊓ 𝔘.U j) → X))
            = ((μ₁.g i - μ₁.g j) ∘ (Subtype.val : ↥(𝔘.U i ⊓ 𝔘.U j) → X))
              + ((μ₂.g i - μ₂.g j) ∘ (Subtype.val : ↥(𝔘.U i ⊓ 𝔘.U j) → X)) := by
          funext x; simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply]; ring
        rw [heq]; exact Submodule.add_mem _ h1 h2
      formHoloDiff := fun i j a hi hj => by
        have h1 := μ₁.toDistribution.formHoloDiff i j a hi hj
        have h2 := μ₂.toDistribution.formHoloDiff i j a hi hj
        have heq : (fun z => coeffAt ω₀ a z *
              (μ₁.g i + μ₂.g i - (μ₁.g j + μ₂.g j)) ((chartAt ℂ a).symm z))
            = (fun z => coeffAt ω₀ a z * (μ₁.g i - μ₁.g j) ((chartAt ℂ a).symm z))
              + (fun z => coeffAt ω₀ a z * (μ₂.g i - μ₂.g j) ((chartAt ℂ a).symm z)) := by
          funext z; simp only [Pi.add_apply, Pi.sub_apply]; ring
        rw [heq]; exact h1.add h2
      iso := fun a ha => by
        -- patch `p` contains `a`; both `ω₀·μ₁.gₚ`, `ω₀·μ₂.gₚ` isolated there, so their sum is.
        set p := if a ∈ μ₁.poles then μ₁.toDistribution.patch a else μ₂.toDistribution.patch a with hp
        have hpmem : a ∈ 𝔘.U p := by
          rw [hp]; by_cases h : a ∈ μ₁.poles
          · rw [if_pos h]; exact μ₁.toDistribution.patch_mem a h
          · rw [if_neg h]
            exact μ₂.toDistribution.patch_mem a ((Finset.mem_union.mp ha).resolve_left h)
        have h1 := μ₁.formFnHoloPunctured_everywhere p hpmem
        have h2 := μ₂.formFnHoloPunctured_everywhere p hpmem
        obtain ⟨ρ₁, hρ₁, hb₁⟩ := h1
        obtain ⟨ρ₂, hρ₂, hb₂⟩ := h2
        refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun z hz => ?_⟩
        have hz1 : z ∈ ball ((chartAt ℂ a) a) ρ₁ \ {(chartAt ℂ a) a} :=
          ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_left _ _)), hz.2⟩
        have hz2 : z ∈ ball ((chartAt ℂ a) a) ρ₂ \ {(chartAt ℂ a) a} :=
          ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_right _ _)), hz.2⟩
        have heq : (fun z => coeffAt ω₀ a z * (μ₁.g p + μ₂.g p) ((chartAt ℂ a).symm z))
            = (fun z => coeffAt ω₀ a z * μ₁.g p ((chartAt ℂ a).symm z))
              + fun z => coeffAt ω₀ a z * μ₂.g p ((chartAt ℂ a).symm z) := by
          funext w; simp only [Pi.add_apply]; ring
        rw [heq]; exact (hb₁ z hz1).add (hb₂ z hz2) }
  holoOff := fun i a ha hb => by
    have hb1 : a ∉ μ₁.poles := fun h => hb (Finset.mem_union_left _ h)
    have hb2 : a ∉ μ₂.poles := fun h => hb (Finset.mem_union_right _ h)
    have h1 := μ₁.holoOff i a ha hb1
    have h2 := μ₂.holoOff i a ha hb2
    have heq : (fun z => (μ₁.g i + μ₂.g i) ((chartAt ℂ a).symm z))
        = (fun z => μ₁.g i ((chartAt ℂ a).symm z)) + fun z => μ₂.g i ((chartAt ℂ a).symm z) := by
      funext z; simp only [Pi.add_apply]
    rw [heq]; exact h1.add h2

@[simp] theorem combine_g (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) (i : 𝔘.ι) :
    (combine μ₁ μ₂).g i = μ₁.g i + μ₂.g i := rfl

@[simp] theorem combine_toDistribution_g (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) (i : 𝔘.ι) :
    (combine μ₁ μ₂).toDistribution.g i = μ₁.toDistribution.g i + μ₂.toDistribution.g i := rfl

@[simp] theorem smul_toDistribution_g (c : ℂ) (μ : CoverMLLift 𝔘 ω₀ K) (i : 𝔘.ι) :
    (smul c μ).toDistribution.g i = c • μ.toDistribution.g i := rfl

open scoped Classical in
@[simp] theorem combine_poles (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) :
    (combine μ₁ μ₂).poles = μ₁.poles ∪ μ₂.poles := rfl

open scoped Classical in
/-- **`res (combine μ₁ μ₂) = res μ₁ + res μ₂`** (Forster §17.2 additivity).  Both residues are read over
the common pole-union via `res_eq_sum_patchOf_superset`, where the integrand splits (`formFnResidue_add`,
both summands isolated everywhere). -/
theorem res_combine (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) :
    (combine μ₁ μ₂).res = μ₁.res + μ₂.res := by
  rw [(combine μ₁ μ₂).res_eq_sum_patchOf,
    μ₁.res_eq_sum_patchOf_superset (Finset.subset_union_left (s₁ := μ₁.poles) (s₂ := μ₂.poles)),
    μ₂.res_eq_sum_patchOf_superset (Finset.subset_union_right (s₁ := μ₁.poles) (s₂ := μ₂.poles)),
    combine_poles, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [combine_g]
  exact formFnResidue_add ω₀ (μ₁.g (patchOf 𝔘 a)) (μ₂.g (patchOf 𝔘 a)) a
    (μ₁.formFnHoloPunctured_everywhere (patchOf 𝔘 a) (patchOf_mem 𝔘 a))
    (μ₂.formFnHoloPunctured_everywhere (patchOf 𝔘 a) (patchOf_mem 𝔘 a))

/-- **Negation** `neg μ := (-1) • μ`. -/
noncomputable def neg (μ : CoverMLLift 𝔘 ω₀ K) : CoverMLLift 𝔘 ω₀ K := smul (-1) μ

@[simp] theorem neg_g (μ : CoverMLLift 𝔘 ω₀ K) (i : 𝔘.ι) : (neg μ).g i = -μ.g i := by
  simp only [neg, smul_g, neg_smul, one_smul]

theorem res_neg (μ : CoverMLLift 𝔘 ω₀ K) : (neg μ).res = -μ.res := by
  rw [neg, res_smul]; simp

/-- **Difference** `sub μ₁ μ₂ := combine μ₁ (neg μ₂)`, with `gᵢ = μ₁.gᵢ − μ₂.gᵢ` and `res = res μ₁ −
res μ₂`.  The lift whose connecting cocycle is `δμ₁ − δμ₂`. -/
noncomputable def sub (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) : CoverMLLift 𝔘 ω₀ K := combine μ₁ (neg μ₂)

@[simp] theorem sub_g (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) (i : 𝔘.ι) :
    (sub μ₁ μ₂).g i = μ₁.g i - μ₂.g i := by
  simp only [sub, combine_g, neg_g]; ring

theorem res_sub (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) : (sub μ₁ μ₂).res = μ₁.res - μ₂.res := by
  rw [sub, res_combine, res_neg]; ring

/-! ### The connecting cocycle is a homomorphism of the algebra

`δμ = (cᵢⱼ) = ([gᵢ − gⱼ])` is ℂ-linear in `μ`: scaling/adding the principal parts scales/adds the
difference-germs (`toGerm` is linear).  Hence `connectingClass` is additive/ℂ-homogeneous — the key
fact for the descent (the residue functional on classes is well-defined and linear). -/

/-- The connecting cochain of a sum is the sum of the connecting cochains (`toGerm` linearity:
`(μ₁.gᵢ+μ₂.gᵢ) − (μ₁.gⱼ+μ₂.gⱼ) = (μ₁.gᵢ−μ₁.gⱼ) + (μ₂.gᵢ−μ₂.gⱼ)` pointwise). -/
theorem connectingCochain_combine (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) :
    (combine μ₁ μ₂).toDistribution.connectingCochain
      = μ₁.toDistribution.connectingCochain + μ₂.toDistribution.connectingCochain := by
  funext p
  rw [Pi.add_apply]
  show toGerm _ _ = toGerm _ _ + toGerm _ _
  rw [← map_add]
  refine congrArg (toGerm _) ?_
  funext x
  simp only [combine_toDistribution_g, Function.comp_apply, Pi.add_apply, Pi.sub_apply]
  ring

/-- The connecting cochain of a scaling is the scaling of the connecting cochain. -/
theorem connectingCochain_smul (c : ℂ) (μ : CoverMLLift 𝔘 ω₀ K) :
    (smul c μ).toDistribution.connectingCochain = c • μ.toDistribution.connectingCochain := by
  funext p
  rw [Pi.smul_apply]
  show toGerm _ _ = c • toGerm _ _
  rw [← map_smul]
  refine congrArg (toGerm _) ?_
  funext x
  simp only [smul_toDistribution_g, Function.comp_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- **The connecting cocycle of a sum is the sum** (as elements of `cocycles1 K`). -/
theorem connectingCocycle_combine (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) :
    (combine μ₁ μ₂).connectingCocycle = μ₁.connectingCocycle + μ₂.connectingCocycle := by
  apply Subtype.ext
  simp only [CoverMLLift.connectingCocycle, CoverMLDistribution.connectingCocycle_coe,
    Submodule.coe_add]
  exact connectingCochain_combine μ₁ μ₂

/-- **The connecting cocycle of a scaling is the scaling.** -/
theorem connectingCocycle_smul (c : ℂ) (μ : CoverMLLift 𝔘 ω₀ K) :
    (smul c μ).connectingCocycle = c • μ.connectingCocycle := by
  apply Subtype.ext
  simp only [CoverMLLift.connectingCocycle, CoverMLDistribution.connectingCocycle_coe,
    SetLike.val_smul]
  exact connectingCochain_smul c μ

/-- **The connecting cocycle of a difference is the difference.** -/
theorem connectingCocycle_sub (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) :
    (sub μ₁ μ₂).connectingCocycle = μ₁.connectingCocycle - μ₂.connectingCocycle := by
  rw [sub, connectingCocycle_combine, neg, connectingCocycle_smul]
  module

/-- **The connecting class of a difference is the difference** (so `[δ(sub μ₁ μ₂)] = [δμ₁] − [δμ₂]`). -/
theorem connectingClass_sub (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) :
    (sub μ₁ μ₂).connectingClass = μ₁.connectingClass - μ₂.connectingClass := by
  show Submodule.Quotient.mk (sub μ₁ μ₂).connectingCocycle
    = Submodule.Quotient.mk μ₁.connectingCocycle - Submodule.Quotient.mk μ₂.connectingCocycle
  rw [connectingCocycle_sub, Submodule.Quotient.mk_sub]

end CoverMLLift

/-! ## The meromorphic Cousin solutions datum and the descent to `CousinResidueData`

We isolate the two genuinely-greenfield inputs the Serre residue functional needs into a single sound
datum `MeromorphicCousinSolutions`, and build the **descent** — the full `CousinResidueData` (hence the
entire Serre pairing, `pairing_injective`, `lDim_le_h1Dim`) — from it.

The two inputs are exactly Forster §15 + §17.3:

* `lift` — **`H¹(X, ℳ) = 0`** (the wall): every `𝒪_K` cocycle `c` is the connecting cocycle of a
  meromorphic Cousin lift `μ : CoverMLLift` (the local-meromorphic `gᵢ` with `gᵢ − gⱼ = cᵢⱼ`,
  `holoOff` off the K-points), `[δμ] = [c]`.  Solved (Forster §15) by splitting off the finite
  principal parts at the K-points and clearing the holomorphic remainder by `H¹(𝔘, 𝒪) = 0`.
* `vanish` — **the residue descent** (`∑Res = 0`, Gate A): a lift whose connecting cocycle is a
  coboundary (`connectingClass μ = 0`, i.e. `δμ ∈ B¹`) is *globally meromorphic* (its `gᵢ` glue to a
  single global `f` modulo the holomorphic coboundary), so `μ.res = ∑ Resₐ(ω₀·f) = 0` by the 1-form
  residue theorem.

From `lift` + `vanish` the residue functional `resCocycle(c) := (lift c).res` is well-defined,
ℂ-linear (the algebra: `combine`/`smul` lifts are cohomologous to the chosen lift, so `vanish` forces
res-additivity), and vanishes on `B¹`.  `nondegenerate` (the §17.6 `dz/z` cup datum) is orthogonal and
carried as a field. -/

variable (𝔘 ω₀ K)

/-- **[ISOLATED — the meromorphic Cousin solutions].**  The two genuinely-new Serre inputs (Forster §15
+ §17.3), on the `holoOff`-equipped lift `CoverMLLift` (so the residue is the genuine total residue and
the descent's well-definedness is sound; see the module docstring on the `holoOff` gap of the bare
`CoverMLDistribution`).

* `lift` — **`H¹(X, ℳ) = 0`**: every `𝒪_K` cocycle class is `[δμ]` for a meromorphic Cousin lift `μ`
  (THE WALL, Forster §15 — principal-part splitting at the K-points + `H¹(𝔘, 𝒪) = 0`).
* `vanish` — **the residue descent** (`∑Res = 0`, Gate A, Forster §17.3): a lift whose connecting
  cocycle is a coboundary (`connectingClass μ = 0`) has residue `0`.  In the genuine Serre setting
  `K = div ω₀` this is exactly `GeneralMittagLeffler.res_eq_zero_of_globalMeromorphic`: `δμ ∈ B¹` means
  `gᵢ = f − σᵢ` for a global meromorphic `f` and an `𝒪_K`-section 0-cochain `σ`, and since `ω₀·σᵢ ∈ Ω`
  is *holomorphic* (poles ≤ `K = div ω₀` cancelled by `ω₀`'s zeros) it contributes residue `0`, leaving
  `μ.res = ∑ Resₐ(ω₀·f) = 0` (the 1-form residue theorem).  (For an unconstrained `K` ⊋ `div ω₀` the
  `σ`-correction need not vanish, so `vanish` is the genuine Serre-setting descent — an isolated input,
  satisfiable: trivially via `ω₀ = 0`, see `nonempty_of_trivial`; genuinely via Gate A when
  `K = div ω₀`.)

From these the residue functional, its ℂ-linearity, and its coboundary-vanishing are all *derived*
(`resCocycle`, `vanish_coboundary` below).  The §17.6 `dz/z` non-degeneracy is orthogonal and supplied
as a hypothesis to `toCousinResidueData`. -/
structure MeromorphicCousinSolutions where
  /-- **`H¹(X, ℳ) = 0`** — a meromorphic Cousin lift of every `𝒪_K` cocycle. -/
  lift : ∀ c : ↥(𝔘.toFiniteFamily.cocycles1 K),
    { μ : CoverMLLift 𝔘 ω₀ K // μ.connectingClass = Submodule.Quotient.mk c }
  /-- **The residue descent** (`∑Res = 0`, Gate A; the genuine Serre-setting `K = div ω₀` fact): a lift
  whose connecting cocycle is a coboundary has residue `0` (see the structure docstring). -/
  vanish : ∀ μ : CoverMLLift 𝔘 ω₀ K, μ.connectingClass = 0 → μ.res = 0

namespace MeromorphicCousinSolutions

variable {𝔘 ω₀ K}

/-- The chosen meromorphic Cousin lift of a cocycle `c` (with `[δ(lift c)] = [c]`). -/
noncomputable def liftOf (S : MeromorphicCousinSolutions 𝔘 ω₀ K)
    (c : ↥(𝔘.toFiniteFamily.cocycles1 K)) : CoverMLLift 𝔘 ω₀ K := (S.lift c).1

theorem liftOf_connectingClass (S : MeromorphicCousinSolutions 𝔘 ω₀ K)
    (c : ↥(𝔘.toFiniteFamily.cocycles1 K)) :
    (S.liftOf c).connectingClass = Submodule.Quotient.mk c := (S.lift c).2

/-- **Well-definedness on classes** (the heart of the descent): if two lifts have the same connecting
class, their residues agree.  `μ₁.res − μ₂.res = res(μ₁ − μ₂) = 0` by `vanish` (the difference's
connecting class is `0`). -/
theorem res_eq_of_connectingClass_eq (S : MeromorphicCousinSolutions 𝔘 ω₀ K)
    {μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K} (h : μ₁.connectingClass = μ₂.connectingClass) :
    μ₁.res = μ₂.res := by
  have hv := S.vanish (CoverMLLift.sub μ₁ μ₂)
    (by rw [CoverMLLift.connectingClass_sub, h, sub_self])
  rw [CoverMLLift.res_sub, sub_eq_zero] at hv
  exact hv

/-- **The residue read on any lift of a cocycle** equals the chosen lift's residue (well-definedness). -/
theorem res_liftOf_eq (S : MeromorphicCousinSolutions 𝔘 ω₀ K)
    {c : ↥(𝔘.toFiniteFamily.cocycles1 K)} {μ : CoverMLLift 𝔘 ω₀ K}
    (h : μ.connectingClass = Submodule.Quotient.mk c) : μ.res = (S.liftOf c).res :=
  S.res_eq_of_connectingClass_eq (by rw [h, S.liftOf_connectingClass])

/-- The connecting class of a combine of two chosen lifts is `[c₁ + c₂]`. -/
theorem connectingClass_combine_liftOf (S : MeromorphicCousinSolutions 𝔘 ω₀ K)
    (c₁ c₂ : ↥(𝔘.toFiniteFamily.cocycles1 K)) :
    (CoverMLLift.combine (S.liftOf c₁) (S.liftOf c₂)).connectingClass
      = Submodule.Quotient.mk (c₁ + c₂) := by
  rw [CoverMLLift.connectingClass_eq, CoverMLLift.connectingCocycle_combine,
    Submodule.Quotient.mk_add, Submodule.Quotient.mk_add,
    ← CoverMLLift.connectingClass_eq, ← CoverMLLift.connectingClass_eq,
    S.liftOf_connectingClass, S.liftOf_connectingClass]

/-- The connecting class of a scaling of a chosen lift is `[a • c]`. -/
theorem connectingClass_smul_liftOf (S : MeromorphicCousinSolutions 𝔘 ω₀ K) (a : ℂ)
    (c : ↥(𝔘.toFiniteFamily.cocycles1 K)) :
    (CoverMLLift.smul a (S.liftOf c)).connectingClass = Submodule.Quotient.mk (a • c) := by
  rw [CoverMLLift.connectingClass_eq, CoverMLLift.connectingCocycle_smul,
    Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, ← CoverMLLift.connectingClass_eq,
    S.liftOf_connectingClass]

/-- **The residue functional `Res(c) := (lift c).res` on cocycles, ℂ-linear** (Forster's `Res`).
Linearity is exactly the well-definedness: `lift (c₁+c₂)` and `combine (lift c₁) (lift c₂)` are
cohomologous (their connecting classes agree), so `res_eq_of_connectingClass_eq` + `res_combine` give
additivity; similarly `smul` gives homogeneity. -/
noncomputable def resCocycle (S : MeromorphicCousinSolutions 𝔘 ω₀ K) :
    ↥(𝔘.toFiniteFamily.cocycles1 K) →ₗ[ℂ] ℂ where
  toFun c := (S.liftOf c).res
  map_add' c₁ c₂ := by
    rw [← S.res_liftOf_eq (S.connectingClass_combine_liftOf c₁ c₂), CoverMLLift.res_combine]
  map_smul' a c := by
    rw [RingHom.id_apply, ← S.res_liftOf_eq (S.connectingClass_smul_liftOf a c),
      CoverMLLift.res_smul, smul_eq_mul]

@[simp] theorem resCocycle_apply (S : MeromorphicCousinSolutions 𝔘 ω₀ K)
    (c : ↥(𝔘.toFiniteFamily.cocycles1 K)) : S.resCocycle c = (S.liftOf c).res := rfl

/-- **`resCocycle` vanishes on coboundaries `B¹`** (the descent to `cechH1`): a coboundary has zero
class, so its chosen lift's connecting class is `0`, hence residue `0` by `vanish`. -/
theorem resCocycle_vanish_coboundary (S : MeromorphicCousinSolutions 𝔘 ω₀ K)
    (c : ↥(𝔘.toFiniteFamily.cocycles1 K))
    (hc : c ∈ (𝔘.toFiniteFamily.coboundaries1 K).submoduleOf (𝔘.toFiniteFamily.cocycles1 K)) :
    S.resCocycle c = 0 := by
  rw [resCocycle_apply]
  exact S.vanish (S.liftOf c)
    (by rw [S.liftOf_connectingClass, (Submodule.Quotient.mk_eq_zero _).mpr hc])

/-- **The genuine-residue tie**: `resCocycle (δμ) = μ.res` for **every `holoOff`-equipped lift** `μ`
(the sound analogue of `MeromorphicCousinSolvable.resCocycle_connecting`, which over-quantifies to all
bare `CoverMLDistribution` — see the module docstring).  This forces `resCocycle` to read the genuine
total Laurent residue, NOT smooth/PoU junk. -/
theorem resCocycle_connecting (S : MeromorphicCousinSolutions 𝔘 ω₀ K) (μ : CoverMLLift 𝔘 ω₀ K) :
    S.resCocycle μ.connectingCocycle = μ.res := by
  rw [resCocycle_apply]
  exact (S.res_liftOf_eq (μ := μ) (c := μ.connectingCocycle) rfl).symm

/-- **The descent to `CousinResidueData`** — the full Serre residue data (hence `toGlobalResidue`,
`pairing_injective`, `lDim_le_h1Dim`, `toSerreDualityData`) from the Cousin solutions plus the §17.6
`dz/z` non-degeneracy datum.  `resCocycle`/`vanish_coboundary` are *derived* (not interface fields). -/
def toCousinResidueData (S : MeromorphicCousinSolutions 𝔘 ω₀ K)
    (nondeg : ∀ (D : Divisor X) (v : lSysModule (K - D)), v ≠ 0 →
      ∃ ξ : 𝔘.toFiniteFamily.cechH1 D,
        (Submodule.liftQ _ S.resCocycle (S.resCocycle_vanish_coboundary))
          (cup (𝔘 := 𝔘.toFiniteFamily) D K v ξ) = 1) :
    CousinResidueData 𝔘 K where
  resCocycle := S.resCocycle
  vanish_coboundary := S.resCocycle_vanish_coboundary
  nondegenerate := nondeg

/-- **The full Serre residue realization** `GlobalResidue 𝔘 K` from the Cousin solutions. -/
def toGlobalResidue (S : MeromorphicCousinSolutions 𝔘 ω₀ K)
    (nondeg : ∀ (D : Divisor X) (v : lSysModule (K - D)), v ≠ 0 →
      ∃ ξ : 𝔘.toFiniteFamily.cechH1 D,
        (Submodule.liftQ _ S.resCocycle (S.resCocycle_vanish_coboundary))
          (cup (𝔘 := 𝔘.toFiniteFamily) D K v ξ) = 1) :
    GlobalResidue 𝔘 K :=
  (S.toCousinResidueData nondeg).toGlobalResidue

/-- **§17.6 — the EASY-half dimension bound `lDim (K−D) ≤ h1Dim D`** from the Cousin solutions. -/
theorem lDim_le_h1Dim (S : MeromorphicCousinSolutions 𝔘 ω₀ K)
    (nondeg : ∀ (D : Divisor X) (v : lSysModule (K - D)), v ≠ 0 →
      ∃ ξ : 𝔘.toFiniteFamily.cechH1 D,
        (Submodule.liftQ _ S.resCocycle (S.resCocycle_vanish_coboundary))
          (cup (𝔘 := 𝔘.toFiniteFamily) D K v ξ) = 1)
    (D : Divisor X) (hfin : FiniteDimensional ℂ (𝔘.toFiniteFamily.cechH1 D)) :
    lDim (X := X) (K - D) ≤ 𝔘.toFiniteFamily.h1Dim D :=
  (S.toCousinResidueData nondeg).lDim_le_h1Dim D hfin

/-- **The full ladder target `SerreDualityData 𝔘`** from the Cousin solutions — the end-to-end chain
`MeromorphicCousinSolutions → CousinResidueData → GlobalResidue → SerreDualityData`.  The remaining
ladder inputs are exactly the standard ones the §17 plan records: the §17.6 `dz/z` non-degeneracy
(`nondeg`), the HARD §17.9 pairing surjectivity (`ι_surj`), Forster §17.4's `hKgenus`
(`lDim K = kirovGenus X`, proven via `CanonicalFormIso`), and Forster §14 finiteness (`finH1`, PROVEN
unconditionally by `finiteDimensional_cechH1_wired`).  This exhibits that an inhabitant of
`MeromorphicCousinSolutions` (the meromorphic Cousin wall + Gate-A descent) feeds the entire Serre
duality ladder. -/
def toSerreDualityData (S : MeromorphicCousinSolutions 𝔘 ω₀ K)
    (nondeg : ∀ (D : Divisor X) (v : lSysModule (K - D)), v ≠ 0 →
      ∃ ξ : 𝔘.toFiniteFamily.cechH1 D,
        (Submodule.liftQ _ S.resCocycle (S.resCocycle_vanish_coboundary))
          (cup (𝔘 := 𝔘.toFiniteFamily) D K v ξ) = 1)
    (hKgenus : lDim (X := X) K = kirovGenus X)
    (ι_surj : ∀ D : Divisor X, Function.Surjective ((S.toCousinResidueData nondeg).pairing D))
    (finH1 : ∀ D : Divisor X, FiniteDimensional ℂ (𝔘.toFiniteFamily.cechH1 D)) :
    SerreDualityData 𝔘 :=
  (S.toCousinResidueData nondeg).toSerreDualityData hKgenus ι_surj finH1

/-! ### Soundness — non-vacuity / inhabitability (NOT a disguised `False`)

`MeromorphicCousinSolutions` is **inhabitable**: in the degenerate configuration `cechH1 K` trivial
(so the `lift` is the trivial zero lift and the connecting map is surjective) over the **zero form**
`ω₀ = 0` (so every lift's residue is `0`, `vanish` holds genuinely), the zero lift gives a genuine
`MeromorphicCousinSolutions`.  Crucially both fields are honestly satisfied: `lift` exercises the
surjectivity (the wall, on the trivial target) and `vanish` exercises the residue descent genuinely
(every lift has residue `0` because the zero form does). -/

/-- The **zero lift** `gᵢ = 0`, empty poles (a `holoOff`-equipped `CoverMLDistribution.zero`). -/
def zeroLift (𝔘 : FiniteCover X) (ω₀ : HolomorphicOneForms X) (K : Divisor X) :
    CoverMLLift 𝔘 ω₀ K where
  toDistribution := CoverMLDistribution.zero 𝔘 ω₀ K
  holoOff := fun i a _ _ => analyticAt_const

/-- **Non-vacuity / inhabitability.**  When `cechH1 K` is trivial (so the connecting map is trivially
surjective), the zero lift over the zero form `ω₀ = 0` is a genuine `MeromorphicCousinSolutions`:
`vanish` holds because the zero form has all residues `0` (`formFnResidue_zero`).  This proves the
isolated solutions structure is **consistent (inhabitable)** — not a disguised `False` — exercising
both `lift` (the surjectivity wall) and `vanish` (the residue descent) genuinely. -/
theorem nonempty_of_trivial (𝔘 : FiniteCover X) (K : Divisor X)
    (htrivH1 : Subsingleton (𝔘.toFiniteFamily.cechH1 K)) :
    Nonempty (MeromorphicCousinSolutions 𝔘 (0 : HolomorphicOneForms X) K) :=
  ⟨{ lift := fun c => ⟨zeroLift 𝔘 0 K, Subsingleton.elim _ _⟩
     vanish := fun μ _ => by
       rw [CoverMLLift.res_def]
       exact Finset.sum_eq_zero fun a _ => formFnResidue_zero _ a }⟩

end MeromorphicCousinSolutions

end Jacobians.Dolbeault

end
