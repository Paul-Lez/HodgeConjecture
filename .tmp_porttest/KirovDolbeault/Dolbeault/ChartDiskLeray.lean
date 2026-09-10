/-
  Čech `H¹` finiteness on a CHART-DISK cover — the Forster GTM 81 Lemma 14.6 `leray` lift,
  analytic foundation.

  This file supplies the genuinely-new analytic content the `leray` field of
  `ChartDiskCover.holomorphicCoboundaries` (`ChartDiskFinitenessComplete.lean`) consumes: a
  **shrinking-level smooth partition of unity** on a `ChartDiskCover`, subordinate to the covering
  shrinking sets `shrinkSet a = V_a` (built in `ChartDiskFiniteness.lean` via the shrinking lemma),
  summing to `1` on ALL of `X`.

  ## Why a shrinking-level PoU (the fix over the cover-level PoU)

  Forster 14.6 lifts a SHRINKING cocycle `s` (holomorphic only on the relatively-compact overlaps
  `Wov (a,b) = φ_a '' (V_a ∩ V_b)`) to `s = δ⁰η + ρ x` with `x` a holomorphic COVER cocycle (on the
  full ball overlaps `Uov (a,b)`).  The smooth split `g_a := ∑_c ρ_c · (chart-read of s_{ca})` must be
  smooth so its `∂̄` is a smooth datum.  On the SHRINKING `V_a` this is automatic: the two opens
  `V_c ∩ V_a` (where `s_{ca}` lives) and `V_a \ tsupport ρ_c` (where `ρ_c = 0`) cover `V_a` — so each
  term `ρ_c · s_{ca}` is smooth on `V_a` (no boundary discontinuity).  A COVER-level PoU (subordinate
  to `U_a`) would instead need `s_{ca}` on `V_c ∩ U_a`, which exceeds where the shrinking cocycle is
  defined.  Hence the PoU must be subordinate to the SHRINKINGS, summing to `1` on `X` (the shrinkings
  cover `X`, `ChartDiskCover.iUnion_shrinkSet_eq_univ`).

  This mirrors `ChartCoverDbarGlue.exists_genuineCoverPoU` (the Montel-cover genuine PoU) but on the
  generic `ChartDiskCover` shrinking sets.

  See the (corrected) `leray` diagnosis in `ChartDiskFinitenessComplete.lean` for how this foundation
  fits the full lift: the `∂̄g_a` agree across charts as a global `(0,1)`-form (the cross-chart frame
  identity `∂̄g_a = conj(τ_{ab}′)·∂̄g_b∘τ` on `Wov`), so they GLUE to a global smooth form `ω̂` on `X`
  (the shrinkings cover `X`); its chart-`a` read on the FULL ball `U_a` is smooth and the frame
  identity then holds on the FULL `Uov (a,b)`.  Solving `∂̄h_a = ω̂_a` on the ball (Forster 13.2,
  `DbarOpenDisk.dbar_solvable_open_disk`) yields `x_{ab} = h_b∘τ − h_a` holomorphic on the FULL `Uov`
  — the ball geometry's genuine unblock over the Montel cover.
-/
import KirovDolbeault.Dolbeault.ChartDiskFiniteness
import KirovDolbeault.Dolbeault.DiskAcyclicCore

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Metric Complex Filter

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace ChartDiskCover

variable (𝔇 : ChartDiskCover X)

/-! ## The shrinking-level smooth partition of unity (sum-to-one on ALL of `X`)

The covering shrinking sets `shrinkSet a = V_a` (from `ChartDiskFiniteness`) genuinely cover `X`
(`iUnion_shrinkSet_eq_univ`), so a subordinate smooth PoU summing to `1` on all of `X` exists. -/

/-- The shrinking sets as `Opens X` (they are open, `shrinkSet_isOpen`). -/
noncomputable def shrinkSetOpens (a : 𝔇.ι) : Opens X := ⟨𝔇.shrinkSet a, 𝔇.shrinkSet_isOpen a⟩

@[simp] theorem shrinkSetOpens_coe (a : 𝔇.ι) :
    ((𝔇.shrinkSetOpens a : Opens X) : Set X) = 𝔇.shrinkSet a := rfl

/-- **The shrinking-level smooth PoU exists (sum-to-one on all of `X`).**  A smooth partition of unity
over `𝓘(ℝ,ℂ)`, subordinate to the covering shrinkings `(V_a)`, summing to `1` on ALL of `X` (the closed
sum-to-one locus is `univ`, since the shrinkings cover `X`).  This is the foundation the Forster 14.6
smooth split consumes: the PoU is subordinate to the SHRINKINGS, where the input cocycle is defined. -/
theorem exists_shrinkPoU :
    ∃ ρ : SmoothPartitionOfUnity 𝔇.ι 𝓘(ℝ, ℂ) X Set.univ,
      ρ.IsSubordinate (fun a => (𝔇.shrinkSet a)) := by
  refine exists_smoothPartitionOfUnity_core 𝔇.shrinkSetOpens isClosed_univ ?_
  rw [Set.univ_subset_iff]
  simpa only [shrinkSetOpens_coe] using 𝔇.iUnion_shrinkSet_eq_univ

/-- A fixed shrinking-level smooth PoU subordinate to `(V_a)`, summing to `1` on all of `X`. -/
noncomputable def shrinkPoU : SmoothPartitionOfUnity 𝔇.ι 𝓘(ℝ, ℂ) X Set.univ :=
  𝔇.exists_shrinkPoU.choose

/-- The shrinking PoU is subordinate to `(V_a)`: `tsupport ρ_a ⊆ V_a`. -/
theorem shrinkPoU_subordinate :
    (𝔇.shrinkPoU).IsSubordinate (fun a => (𝔇.shrinkSet a)) :=
  𝔇.exists_shrinkPoU.choose_spec

/-- **Sum-to-one EVERYWHERE.**  `∑ a, ρ_a x = 1` for every `x : X`. -/
theorem sum_shrinkPoU_eq_one (x : X) :
    ∑ a, (𝔇.shrinkPoU) a x = 1 :=
  smoothPartitionOfUnity_sum_eq_one_of_mem (𝔇.shrinkPoU) (Set.mem_univ x)

/-- The subordination as a `tsupport` containment: `tsupport (ρ_a) ⊆ V_a`. -/
theorem shrinkPoU_tsupport_subset (a : 𝔇.ι) :
    tsupport (𝔇.shrinkPoU a) ⊆ 𝔇.shrinkSet a :=
  𝔇.shrinkPoU_subordinate a

/-- Each PoU function `ρ_a : X → ℝ` is globally `C^∞` on `X` (over `𝓘(ℝ,ℂ) → 𝓘(ℝ,ℝ)`). -/
theorem contMDiff_shrinkPoU (a : 𝔇.ι) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (𝔇.shrinkPoU a) :=
  (𝔇.shrinkPoU a).contMDiff

/-- `ρ_a x = 0` for `x ∉ tsupport ρ_a`. -/
theorem shrinkPoU_eq_zero_of_notMem (a : 𝔇.ι) {x : X}
    (hx : x ∉ tsupport (𝔇.shrinkPoU a)) : (𝔇.shrinkPoU a) x = 0 :=
  image_eq_zero_of_notMem_tsupport hx

end ChartDiskCover

end Jacobians.Dolbeault
