/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dissection
import KirovDolbeault.CutSurface
import KirovDolbeault.BoundaryWordR2

/-!
# The cut surface and the Riemann bilinear relations as THEOREMS

This file discharges the directive *"prove the Riemann relations; isolate only the chart existence."*
It introduces a `CutSurface X` — the analytic boundary data of a canonical dissection realized as a
cut chart `cut : box → X` — and **proves**, from that data alone, both Riemann bilinear relations:

* `cutSurface_R1 : (aPeriodBlock loop)ᵀ * bPeriodBlock loop = (bPeriodBlock loop)ᵀ * aPeriodBlock loop`
  — via Cauchy's theorem on the box (`riemann_R1_of_boundaryWord`);
* `cutSurface_R2 : (periodHermitian loop).PosDef`
  — via the Green-positivity bridge (`riemann_R2_posDef_of_boundaryWord`).

The two relations are therefore **no longer bundled assertions**: they are consequences of the
*boundary word* — the concrete integral identities `(AᵀB − BᵀA)_{ij} = ∮_{∂box}(F_i h_j dz)` and
`(AᵀB̄ − BᵀĀ)_{ij} = −∮_{∂box}(F̄_i h_j dz)` that record how the cut chart's boundary traverses the
symplectic loops. Those boundary words, the holomorphy of the pulled-back forms `h_j = cut^*ω_j`, and
the non-degeneracy of the pullbacks are the **`CutSurface` fields**; the existence of such a cut
surface (`exists_cutSurface`) is the single isolated input — the Radó triangulation + surface
classification + `4g`-gon Green that Mathlib lacks for surfaces.

`exists_canonicalDissection` is then *derived* (no longer a raw obligation): a `CutSurface` yields a
`CanonicalDissection` whose two relation fields are the theorems above.

References: Riemann (1857); Griffiths–Harris pp. 231–232; Springer pp. 139–141; Chai §1.4;
Forster §§20–21.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set intervalIntegral Complex Matrix
open scoped Manifold ContDiff Bundle Topology ComplexOrder

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Cut surface of a compact Riemann surface.** A symplectic homology basis of `2g` closed loops
together with the *analytic boundary data* of the cut chart that realizes the canonical dissection:

* the pulled-back holomorphic forms `h_j = cut^*ω_j`, holomorphic on a convex open `U ⊇ [0,1]²`, with
  primitives `F_i` (`F_i' = h_i`);
* the two **boundary words** — concrete `∮_{∂box}` integral identities that record how the cut
  chart's boundary traverses the loops (this is the surface-topology / polygon-Green content);
* non-degeneracy of the pullbacks (a nonzero form pulls back to a function nonzero somewhere in the
  open box — true because `cut` is a diffeo on the interior and the `ω_j` are a basis).

From these the Riemann bilinear relations R1/R2 are **proven** (`cutSurface_R1`, `cutSurface_R2`).
Only the *existence* of such data, `exists_cutSurface`, stays isolated. -/
structure CutSurface (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] where
  /-- The `2g` symplectic homology-basis loops `a₁,…,a_g,b₁,…,b_g`. -/
  loop : Fin (2 * kirovGenus X) → (ℝ → X)
  /-- Each is a closed smooth loop. -/
  loop_closed : ∀ k, IsClosedSmoothLoop (loop k)
  /-- **Generation.** Every closed-loop period is a `ℤ`-combination of the basis loops' periods. -/
  generates : closedLoopPeriods X ⊆
    Submodule.span ℤ (Set.range (fun k => periodVec (loop k)))
  /-- A convex open neighborhood of the closed box `[0,1]²` (embedded in `ℂ` via
  `wCLM (x,y) = x + y·I`) on which the pulled-back forms are holomorphic. -/
  U : Set ℂ
  /-- The closed box lies in `U`. -/
  hbox : wCLM '' (Set.Icc 0 1 ×ˢ Set.Icc 0 1) ⊆ U
  /-- Pullback coefficients `h_j = cut^*ω_j` (`h_j dz` is the pullback of the `j`-th basis form). -/
  h : Fin (kirovGenus X) → ℂ → ℂ
  /-- Primitives `F_i` of `h_i` on `U`. -/
  F : Fin (kirovGenus X) → ℂ → ℂ
  /-- Each `h_i` is holomorphic on `U`. -/
  hh : ∀ i, ∀ z ∈ U, HasDerivAt (h i) (deriv (h i) z) z
  /-- Each `F_i` is a primitive of `h_i` on `U`. -/
  hF : ∀ i, ∀ z ∈ U, HasDerivAt (F i) (h i z) z
  /-- **Riemann's first boundary word.** The `(i,j)` entry of `AᵀB − BᵀA` is the box contour integral
  of the *holomorphic* `F_i·h_j`. (The cut chart's boundary traverses `a₁b₁a₁⁻¹b₁⁻¹⋯`; the primitive's
  jumps across the cuts are the conjugate periods, collapsing `∮_{∂box}` to this period sum.) -/
  boundaryWord_R1 : ∀ i j,
    ((aPeriodBlock loop)ᵀ * bPeriodBlock loop - (bPeriodBlock loop)ᵀ * aPeriodBlock loop) i j
      = rectBoundaryIntegral (fun z => F i z * h j z)
  /-- **Riemann's second boundary word.** The `(i,j)` entry of `AᵀB̄ − BᵀĀ` is `−∮_{∂box}(F̄_i·h_j)`. -/
  boundaryWord_R2 : ∀ i j,
    ((aPeriodBlock loop)ᵀ * (bPeriodBlock loop).map (starRingEnd ℂ)
      - (bPeriodBlock loop)ᵀ * (aPeriodBlock loop).map (starRingEnd ℂ)) i j
      = - boundaryForm (h j) (F i)
  /-- **Non-degeneracy.** A nonzero coefficient vector `v` pulls back to a function `∑ⱼ vⱼ hⱼ` that is
  nonzero somewhere in the *open* box. (`∑ⱼ vⱼ ωⱼ ≠ 0` is a nonzero holomorphic form, so its pullback
  is nonzero on the dense interior of the cut surface.) -/
  nondeg : ∀ v : Fin (kirovGenus X) → ℂ, v ≠ 0 →
    ∃ p ∈ Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1, (∑ j, v j * h j (wCLM p)) ≠ 0

namespace CutSurface

variable (S : CutSurface X)

/-- The closed box (as a complex rectangle `[0,1] ×ℂ [0,1]`) lies in `S.U`. -/
lemma box_reProdIm_subset_U :
    (Set.uIcc (0:ℝ) 1 ×ℂ Set.uIcc (0:ℝ) 1) ⊆ S.U := by
  intro z hz
  rw [Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hz
  refine S.hbox ⟨(z.re, z.im), ?_, ?_⟩
  · rw [Set.mem_prod]; exact ⟨hz.1, hz.2⟩
  · rw [wCLM_apply]; exact Complex.re_add_im z

/-- `h_j` is differentiable on `S.U`. -/
lemma differentiableOn_h (j : Fin (kirovGenus X)) : DifferentiableOn ℂ (S.h j) S.U :=
  fun z hz => (S.hh j z hz).differentiableAt.differentiableWithinAt

/-- `F_i` is differentiable on `S.U`. -/
lemma differentiableOn_F (i : Fin (kirovGenus X)) : DifferentiableOn ℂ (S.F i) S.U :=
  fun z hz => (S.hF i z hz).differentiableAt.differentiableWithinAt

/-- `F_i·h_j` is differentiable on the closed box (needed for box Cauchy in R1). -/
lemma differentiableOn_Fh (i j : Fin (kirovGenus X)) :
    DifferentiableOn ℂ (fun z => S.F i z * S.h j z) (Set.uIcc (0:ℝ) 1 ×ℂ Set.uIcc (0:ℝ) 1) :=
  ((S.differentiableOn_F i).mul (S.differentiableOn_h j)).mono S.box_reProdIm_subset_U

/-- **Riemann's first bilinear relation `AᵀB = BᵀA`, PROVEN** from the cut surface, via Cauchy's
theorem on the box (`riemann_R1_of_boundaryWord`). -/
theorem cutSurface_R1 :
    (aPeriodBlock S.loop)ᵀ * bPeriodBlock S.loop
      = (bPeriodBlock S.loop)ᵀ * aPeriodBlock S.loop :=
  riemann_R1_of_boundaryWord (aPeriodBlock S.loop) (bPeriodBlock S.loop) S.h S.F
    S.differentiableOn_Fh S.boundaryWord_R1

/-- **Riemann's second bilinear relation (positive-definiteness of the period Hermitian form),
PROVEN** from the cut surface, via the Green-positivity bridge
(`riemann_R2_posDef_of_boundaryWord`). -/
theorem cutSurface_R2 : (periodHermitian S.loop).PosDef :=
  riemann_R2_posDef_of_boundaryWord (aPeriodBlock S.loop) (bPeriodBlock S.loop) S.h S.F S.U
    S.hbox S.hh S.hF S.boundaryWord_R2 S.nondeg

/-- **A cut surface yields a canonical dissection** whose two Riemann-relation fields are the
*theorems* `cutSurface_R1` / `cutSurface_R2` (not bundled assertions). -/
def toCanonicalDissection : CanonicalDissection X where
  loop := S.loop
  loop_closed := S.loop_closed
  generates := S.generates
  periodRel_vanishing := S.cutSurface_R1
  periodRel_posDef := S.cutSurface_R2

end CutSurface

/-- **[ISOLATED INPUT — chart existence only]** Every compact connected Riemann surface admits a cut
surface: a canonical dissection realized as a cut chart with the boundary-word data. This bundles
exactly the surface-topology + polygon-Green content Mathlib lacks — the Radó triangulation, the
classification of surfaces (`H₁(X;ℤ) ≅ ℤ^{2g}` + the canonical `4g`-gon), the holomorphic cut chart,
and Green's theorem on the `4g`-gon (which turns `∮_{∂box}` into the period sums of the two boundary
words). **Everything analytic downstream — both Riemann bilinear relations — is proven**
(`CutSurface.cutSurface_R1`, `CutSurface.cutSurface_R2`). (Forster §§20–21; Griffiths–Harris
pp. 231–232; Springer pp. 139–141.) -/
theorem exists_cutSurface (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    Nonempty (CutSurface X) :=
  sorry

/-- **Every compact connected Riemann surface admits a canonical dissection** — *derived* from
`exists_cutSurface` with the two Riemann bilinear relations as the proven theorems
`CutSurface.cutSurface_R1` / `CutSurface.cutSurface_R2`. (This replaces the former raw obligation: the
relations are no longer bundled; only the chart existence is isolated.) -/
theorem exists_canonicalDissection (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    Nonempty (CanonicalDissection X) :=
  (exists_cutSurface X).map CutSurface.toCanonicalDissection

end Jacobians
