/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.DolbeaultComparisonInverse

/-!
# R2 — the partition-of-unity split of an overlap cocycle

Step 2 of the Forster §17.3 fine-sheaf residue construction (S3 scoping §2.0–2.1, lane R):
given a chart-disk cover and a family of overlap functions `w i j` (holomorphic cocycle values —
what a Mittag–Leffler datum contributes as `w i j = m j − m i`, and what R1's germ→coefficient
extraction will produce from a Čech cocycle in `Z¹(𝒪_K)` via `ω₀·`), the smooth partition of
unity glues the *local* overlap data into per-chart split functions

  `σ_i := ∑_k ρ_k · w k i`,

smooth on `U i` (`contMDiffAt_pouSplit` — the support-aware `gdTerm` gluing pattern), with the
telescoping identity

  `σ_j − σ_i = w i j` on `U i ⊓ U j`  (`pouSplit_telescope`),

so the Čech cocycle becomes a coboundary of the smooth `0`-cochain `σ` — the input to R3's
`τ_i := ∂̄σ_i` (which the telescoping makes well-glued, since `∂̄w_{ij} = 0`).

Everything is **reused** from the proven `DolbeaultComparisonInverse` backbone: the fixed
subordinate PoU `cechPoU` (from `SmoothPartitionOfUnity.exists_isSubordinate` through the
`RealManifold` bridge), its complexification `rhoC`, the normalizations `sum_rhoC_apply` /
`cechPoU_subordinate`.  The telescoping here is the *support-aware* refinement of the abstract
`cechCoboundary_telescoping`: the cocycle identity is only demanded on **triple overlaps**
(`IsOverlapCocycle`), because the weight `ρ_k` kills every summand whose index leaves its cover
set — this is what lets Mittag–Leffler/Čech data, which carry no information outside the
overlaps, feed the split.

Hypotheses are stated pointwise-on-overlaps (membership-guarded), matching the germ-eventual
discipline of R1 (`OneOneCoeff.lean`): only values on the (open) overlaps are ever consumed.
-/

open Complex Filter
open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

-- Same permissive transparency as `RealForms`/`DolbeaultComparisonInverse` (the
-- `SmoothCFunctions` coercions below need it).
set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable (𝔇 : ChartDiskCover X)

/-! ### The overlap-family interface -/

/-- An overlap family `w` is **smooth on overlaps** when each `w i j` is `C^∞` (over `ℝ`, the
`ContMDiffAt 𝓘(ℝ, ℂ)` of the port's form calculus) at every point of `U i ⊓ U j`.  Values
outside the overlap are junk and never consumed (the `gdTerm`/`diskVal` global-stand-in
idiom). -/
def SmoothOnOverlaps (w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ) : Prop :=
  ∀ i j, ∀ x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X),
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (w i j) x

/-- An overlap family `w` is an **overlap cocycle** when the additive Čech cocycle identity
`w b c − w a c + w a b = 0` holds pointwise on every **triple** overlap — the only place the
PoU split ever reads it.  This is the value-level shadow of `cechDelta1 = 0`. -/
def IsOverlapCocycle (w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ) : Prop :=
  ∀ a b c, ∀ x ∈ (𝔇.U a ⊓ 𝔇.U b ⊓ 𝔇.U c : Opens X),
    w b c x - w a c x + w a b x = 0

omit [Nonempty X] in
/-- **Difference families are overlap cocycles** — the Mittag–Leffler shape: for any value
family `v` (e.g. the local lifts `m_i` of an ML datum, or the disk primitives `diskVal`), the
overlap family `w i j := v j − v i` satisfies the cocycle identity identically. -/
theorem isOverlapCocycle_sub (v : 𝔇.toFiniteCover.ι → X → ℂ) :
    IsOverlapCocycle 𝔇 fun i j x => v j x - v i x := fun _ _ _ _ _ => by ring

/-! ### The PoU split and its smoothness -/

/-- The **partition-of-unity split** of an overlap family: `σ_i := ∑_k ρ_k · w k i`, with
`ρ = cechPoU 𝔇` the fixed subordinate smooth PoU of the inverse-comparison backbone.  A global
stand-in function, meaningful (and smooth) on `U i`. -/
noncomputable def pouSplit (w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ)
    (i : 𝔇.toFiniteCover.ι) : X → ℂ :=
  fun x => ∑ k, rhoC 𝔇 k x * w k i x

@[simp] theorem pouSplit_apply (w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ)
    (i : 𝔇.toFiniteCover.ι) (x : X) :
    pouSplit 𝔇 w i x = ∑ k, rhoC 𝔇 k x * w k i x := rfl

/-- **Smoothness of the split on its own cover set** (the `gdTerm` support-aware gluing): at
`x ∈ U i`, every summand `ρ_k · w k i` is smooth — on `tsupport ρ_k` because subordination puts
`x` in `U k ⊓ U i` where `w k i` is smooth, off it because the summand vanishes on a
neighbourhood. -/
theorem contMDiffAt_pouSplit {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    (hw : SmoothOnOverlaps 𝔇 w) (i : 𝔇.toFiniteCover.ι) {x : X} (hx : x ∈ (𝔇.U i : Set X)) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (pouSplit 𝔇 w i) x := by
  refine ContMDiffAt.sum fun k _ => ?_
  by_cases hb : x ∈ tsupport (cechPoU 𝔇 k)
  · exact ((rhoC 𝔇 k).contMDiff x).mul (hw k i x ⟨cechPoU_subordinate 𝔇 k hb, hx⟩)
  · refine (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport (cechPoU 𝔇 k)).isOpen_compl.mem_nhds hb] with y hy
    have hr : rhoC 𝔇 k y = 0 := by
      simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM, image_eq_zero_of_notMem_tsupport hy]
      rfl
    simp only [hr, zero_mul]

/-! ### The telescoping identity -/

/-- **The telescoping identity of the PoU split**: on `U i ⊓ U j`,

  `σ_j − σ_i = w i j`.

Support-aware refinement of `cechCoboundary_telescoping`: termwise, either `ρ_k x = 0` (and the
`k`-summand contributes nothing), or subordination places `x` in the triple overlap
`U k ⊓ U i ⊓ U j` where the cocycle identity converts `w k j − w k i` into `w i j`; summing the
weights with `∑_k ρ_k x = 1` finishes.  This is what makes the split a smooth 0-cochain whose
coboundary is the input cocycle — the heart of "the fine sheaf has no `H¹`". -/
theorem pouSplit_telescope {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    (hcoc : IsOverlapCocycle 𝔇 w) {i j : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X)) :
    pouSplit 𝔇 w j x - pouSplit 𝔇 w i x = w i j x := by
  have hpt : ∀ k, rhoC 𝔇 k x * w k j x - rhoC 𝔇 k x * w k i x
      = rhoC 𝔇 k x * w i j x := by
    intro k
    by_cases hb : x ∈ tsupport (cechPoU 𝔇 k)
    · have hk : x ∈ (𝔇.U k : Set X) := cechPoU_subordinate 𝔇 k hb
      have hc := hcoc k i j x ⟨⟨hk, hx.1⟩, hx.2⟩
      rw [← mul_sub]
      have hsub : w k j x - w k i x = w i j x := by linear_combination -hc
      rw [hsub]
    · have hr : rhoC 𝔇 k x = 0 := by
        simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM,
          image_eq_zero_of_notMem_tsupport hb]
        rfl
      simp only [hr, zero_mul, sub_zero]
  calc pouSplit 𝔇 w j x - pouSplit 𝔇 w i x
      = ∑ k, (rhoC 𝔇 k x * w k j x - rhoC 𝔇 k x * w k i x) := by
        rw [pouSplit_apply, pouSplit_apply, Finset.sum_sub_distrib]
    _ = ∑ k, rhoC 𝔇 k x * w i j x := by simp_rw [hpt]
    _ = (∑ k, rhoC 𝔇 k x) * w i j x := by rw [Finset.sum_mul]
    _ = w i j x := by rw [sum_rhoC_apply, one_mul]

end Jacobians.Dolbeault.FineResidue
