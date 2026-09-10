/-
Project-side addition to the Kirov Dolbeault port (NOT from upstream
rkirov/jacobian-claude). Apache 2.0, same as the surrounding port.
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import KirovDolbeault.CutSurface
import KirovDolbeault.BoundaryWordR2

/-!
# Interior-holomorphy boundary-word engines (BW ladder rungs 1–5)

The closed-box engines (`riemann_R1_of_boundaryWord`, `integral_normSq_eq_boundary`,
`boundaryForm_pos`, `riemann_R2_posDef_of_boundaryWord`) demand holomorphy of the cut pullbacks
`h_j` and primitives `F_i` on an open `U` **containing the closed unit box**. A geometric cut
chart at genus ≥ 2 cannot supply that (the C2 angle-count obstruction,
`docs/planning/CUTSURFACE_GAP_ANALYSIS.md` §C2): at the polygon vertices the chart is only
continuous. What a cut chart *does* supply is

* holomorphy on the **open** box image, and
* continuity up to the **closed** box image.

This file re-proves all four engines from exactly that weaker input. No new mathematics: the two
analytic cores already have the split form — Mathlib's
`Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn` (Cauchy) and the
port's `Jacobians.greenOnUnitBox` (Green), both of which take closed-box continuity + open-box
derivatives. The closed-box originals are left untouched for their existing consumers; the
`_interior` variants below are strictly weaker-hypothesis versions (see
`docs/planning/BW_ROUTE.md`, rungs 1–5).

Main results:
* `rectBoundaryIntegral_eq_zero_of_continuousOn_of_differentiableOn_unitBox` — rung 1, split
  Cauchy in the unit-box vocabulary;
* `riemann_R1_of_boundaryWord_interior` — rung 2, R1 from the boundary word;
* `integral_normSq_eq_boundary_interior` — rung 3, the Green positivity bridge;
* `boundaryForm_pos_interior` — rung 4, box-level positivity;
* `riemann_R2_posDef_of_boundaryWord_interior` — rung 5, R2 positive-definiteness.

Also provides the image-set dictionary `wCLM_image_prod` / `wCLM_image_closedBox` /
`wCLM_image_openBox` translating between the `wCLM ''` (Green-side) and `×ℂ` (Cauchy-side)
descriptions of the box.
-/

open MeasureTheory Set intervalIntegral Complex Matrix
open scoped ComplexConjugate ComplexOrder

namespace Jacobians

/-! ## The box dictionary: `wCLM` images vs `×ℂ` strips -/

/-- The coordinate map `wCLM (x,y) = x + y·I` sends a product of real sets to the corresponding
complex strip: `wCLM '' (s ×ˢ t) = s ×ℂ t`. -/
lemma wCLM_image_prod (s t : Set ℝ) : wCLM '' (s ×ˢ t) = s ×ℂ t := by
  ext z
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    rw [Complex.mem_reProdIm, wCLM_apply]
    constructor
    · simpa using hx
    · simpa using hy
  · intro hz
    refine ⟨(z.re, z.im), ⟨hz.1, hz.2⟩, ?_⟩
    rw [wCLM_apply]
    exact Complex.re_add_im z

/-- The closed-box image is the closed complex unit box (`uIcc` form, as consumed by Mathlib's
rectangle theorems). -/
lemma wCLM_image_closedBox :
    wCLM '' (Icc 0 1 ×ˢ Icc 0 1) = Set.uIcc (0 : ℝ) 1 ×ℂ Set.uIcc (0 : ℝ) 1 := by
  rw [wCLM_image_prod, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]

/-- The open-box image is the open complex unit box. -/
lemma wCLM_image_openBox :
    wCLM '' (Ioo 0 1 ×ˢ Ioo 0 1) = Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (0 : ℝ) 1 :=
  wCLM_image_prod _ _

/-! ## Rung 1: split Cauchy on the unit box -/

/-- **Cauchy on the box, split form (rung 1).** If `f` is continuous on the closed unit box and
holomorphic on the open unit box, its contour integral over `∂box` vanishes. Direct from
`Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn` specialized to
`z = 0`, `w = 1 + i`. Interior weakening of `rectBoundaryIntegral_eq_zero_of_differentiableOn`. -/
theorem rectBoundaryIntegral_eq_zero_of_continuousOn_of_differentiableOn_unitBox {f : ℂ → ℂ}
    (hc : ContinuousOn f (Set.uIcc 0 1 ×ℂ Set.uIcc 0 1))
    (hd : DifferentiableOn ℂ f (Set.Ioo (0:ℝ) 1 ×ℂ Set.Ioo (0:ℝ) 1)) :
    rectBoundaryIntegral f = 0 := by
  have hmin : min (0:ℝ) 1 = 0 := min_eq_left zero_le_one
  have hmax : max (0:ℝ) 1 = 1 := max_eq_right zero_le_one
  have h := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f 0
    (1 + Complex.I) (by simpa using hc) (by simpa [hmin, hmax] using hd)
  simpa [rectBoundaryIntegral, smul_eq_mul] using h

/-! ## Rung 2: R1 from the boundary word, interior form -/

/-- **Riemann's first bilinear relation from the boundary word, interior form (rung 2).** Same
conclusion as `riemann_R1_of_boundaryWord`, but each `F_i·h_j` is only required to be continuous
on the closed unit box and holomorphic on the open unit box. -/
theorem riemann_R1_of_boundaryWord_interior {g : ℕ} (A B : Matrix (Fin g) (Fin g) ℂ)
    (h F : Fin g → ℂ → ℂ)
    (hFhc : ∀ i j, ContinuousOn (fun z => F i z * h j z) (Set.uIcc 0 1 ×ℂ Set.uIcc 0 1))
    (hFhd : ∀ i j, DifferentiableOn ℂ (fun z => F i z * h j z)
      (Set.Ioo (0:ℝ) 1 ×ℂ Set.Ioo (0:ℝ) 1))
    (boundaryWord : ∀ i j,
      (Aᵀ * B - Bᵀ * A) i j = rectBoundaryIntegral (fun z => F i z * h j z)) :
    Aᵀ * B = Bᵀ * A := by
  rw [← sub_eq_zero]
  ext i j
  rw [Matrix.zero_apply, boundaryWord i j]
  exact rectBoundaryIntegral_eq_zero_of_continuousOn_of_differentiableOn_unitBox
    (hFhc i j) (hFhd i j)

/-! ## Rung 3: the Green positivity bridge, interior form -/

section InteriorGreen

variable {h F : ℂ → ℂ}

/-- `P = F̄(w·)·h(w·)` is continuous on the closed box, from *boundary continuity* of `h` and `F`
(no holomorphy needed). Interior-form replacement for `continuousOn_Pfun`. -/
lemma continuousOn_Pfun_of_continuousOn
    (hhc : ContinuousOn h (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)))
    (hFc : ContinuousOn F (wCLM '' (Icc 0 1 ×ˢ Icc 0 1))) :
    ContinuousOn (Pfun h F) (Icc 0 1 ×ˢ Icc 0 1) := by
  have hγc : ContinuousOn (fun p : ℝ × ℝ => wCLM p) (Icc 0 1 ×ˢ Icc 0 1) :=
    wCLM.continuous.continuousOn
  have hγm : MapsTo (fun p : ℝ × ℝ => wCLM p) (Icc 0 1 ×ˢ Icc 0 1)
      (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)) := Set.mapsTo_image _ _
  exact (Complex.continuous_conj.comp_continuousOn (hFc.comp hγc hγm)).mul (hhc.comp hγc hγm)

/-- `Q = I·P` is continuous on the closed box, from boundary continuity. -/
lemma continuousOn_Qfun_of_continuousOn
    (hhc : ContinuousOn h (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)))
    (hFc : ContinuousOn F (wCLM '' (Icc 0 1 ×ˢ Icc 0 1))) :
    ContinuousOn (Qfun h F) (Icc 0 1 ×ˢ Icc 0 1) :=
  continuousOn_const.mul (continuousOn_Pfun_of_continuousOn hhc hFc)

/-- `‖h(w·)‖²` (ℂ-valued) is continuous on the closed box, from boundary continuity of `h`. -/
lemma continuousOn_normSq_of_continuousOn
    (hhc : ContinuousOn h (wCLM '' (Icc 0 1 ×ˢ Icc 0 1))) :
    ContinuousOn (fun p : ℝ × ℝ => (‖h (wCLM p)‖ ^ 2 : ℂ)) (Icc 0 1 ×ˢ Icc 0 1) := by
  have hcomp : ContinuousOn (fun p : ℝ × ℝ => h (wCLM p)) (Icc 0 1 ×ˢ Icc 0 1) :=
    hhc.comp wCLM.continuous.continuousOn (Set.mapsTo_image _ _)
  exact (Complex.continuous_ofReal.comp_continuousOn hcomp.norm).pow 2

/-- The Green integrand `∂Q/∂x − ∂P/∂y` is integrable on the closed box, from boundary continuity
of `h` alone (the pointwise identity `integrand_eq` holds unconditionally, so the integrand agrees
with the continuous `2I·‖h‖²` everywhere). -/
lemma integrableOn_integrand_of_continuousOn
    (hhc : ContinuousOn h (wCLM '' (Icc 0 1 ×ˢ Icc 0 1))) :
    IntegrableOn (fun p => Qder h F p (1, 0) - Pder h F p (0, 1)) (Icc 0 1 ×ˢ Icc 0 1) := by
  have hcont : ContinuousOn (fun p => Qder h F p (1, 0) - Pder h F p (0, 1))
      (Icc 0 1 ×ˢ Icc 0 1) :=
    (continuousOn_const.mul (continuousOn_normSq_of_continuousOn hhc)).congr
      (fun p _ => integrand_eq p)
  exact hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

/-- **Green positivity bridge, interior form (rung 3).** For `h` continuous on the closed box
image and holomorphic on the open box image, with primitive `F` (`F' = h` on the open box image,
`F` continuous up to the boundary), the area integral of `‖h‖²` over the box equals `−(i/2)`
times the boundary integral `∮_{∂box} F̄·h dz`. Interior weakening of
`integral_normSq_eq_boundary`: the closed-box-neighbourhood holomorphy hypotheses are replaced by
exactly the closed-continuity / open-derivative split that `greenOnUnitBox` consumes. -/
theorem integral_normSq_eq_boundary_interior
    (hhc : ContinuousOn h (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)))
    (hFc : ContinuousOn F (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)))
    (hh : ∀ z ∈ wCLM '' (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1), HasDerivAt h (deriv h z) z)
    (hF : ∀ z ∈ wCLM '' (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1), HasDerivAt F (h z) z) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, (‖h (wCLM (x, y))‖ ^ 2 : ℂ))
      = -(Complex.I / 2) *
        (((∫ x in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (x, 0))) * h (wCLM (x, 0)))
            + Complex.I * ∫ y in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (1, y))) * h (wCLM (1, y)))
          - (∫ x in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (x, 1))) * h (wCLM (x, 1)))
          - Complex.I * ∫ y in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (0, y))) * h (wCLM (0, y))) := by
  have hdP : ∀ p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1, HasFDerivAt (Pfun h F) (Pder h F p) p :=
    fun p hp => hasFDerivAt_Pfun (hF _ ⟨p, hp, rfl⟩) (hh _ ⟨p, hp, rfl⟩)
  have hdQ : ∀ p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1, HasFDerivAt (Qfun h F) (Qder h F p) p :=
    fun p hp => hasFDerivAt_Qfun (hF _ ⟨p, hp, rfl⟩) (hh _ ⟨p, hp, rfl⟩)
  have hgreen := greenOnUnitBox (Pfun h F) (Qfun h F) (Pder h F) (Qder h F)
    (continuousOn_Pfun_of_continuousOn hhc hFc) (continuousOn_Qfun_of_continuousOn hhc hFc)
    hdP hdQ (integrableOn_integrand_of_continuousOn hhc)
  -- Rewrite the area integral of the Green integrand as `2I · ∬ ‖h‖²`.
  have hinner : (fun x : ℝ => ∫ y in (0:ℝ)..1, (Qder h F (x, y) (1, 0) - Pder h F (x, y) (0, 1)))
      = (fun x : ℝ => 2 * Complex.I * ∫ y in (0:ℝ)..1, (‖h (wCLM (x, y))‖ ^ 2 : ℂ)) := by
    funext x
    rw [intervalIntegral.integral_congr
          (g := fun y => 2 * Complex.I * (‖h (wCLM (x, y))‖ ^ 2 : ℂ))
          (fun y _ => integrand_eq (x, y))]
    exact intervalIntegral.integral_const_mul _ _
  have hRHS : (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, (Qder h F (x, y) (1, 0) - Pder h F (x, y) (0, 1)))
      = 2 * Complex.I * ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, (‖h (wCLM (x, y))‖ ^ 2 : ℂ) := by
    rw [hinner]
    exact intervalIntegral.integral_const_mul _ _
  -- Rewrite the boundary integral, pulling `I` out of the vertical edges and unfolding `Pfun/Qfun`.
  have hLHS : ((∫ x in (0:ℝ)..1, Pfun h F (x, 0)) + ∫ y in (0:ℝ)..1, Qfun h F (1, y))
        - (∫ x in (0:ℝ)..1, Pfun h F (x, 1)) - ∫ y in (0:ℝ)..1, Qfun h F (0, y)
      = ((∫ x in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (x, 0))) * h (wCLM (x, 0)))
            + Complex.I * ∫ y in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (1, y))) * h (wCLM (1, y)))
          - (∫ x in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (x, 1))) * h (wCLM (x, 1)))
          - Complex.I * ∫ y in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (0, y))) * h (wCLM (0, y)) := by
    simp only [Pfun, Qfun]
    rw [show (∫ y in (0:ℝ)..1,
            Complex.I * ((starRingEnd ℂ) (F (wCLM (1, y))) * h (wCLM (1, y))))
          = Complex.I * ∫ y in (0:ℝ)..1, ((starRingEnd ℂ) (F (wCLM (1, y))) * h (wCLM (1, y)))
        from intervalIntegral.integral_const_mul _ _,
       show (∫ y in (0:ℝ)..1,
            Complex.I * ((starRingEnd ℂ) (F (wCLM (0, y))) * h (wCLM (0, y))))
          = Complex.I * ∫ y in (0:ℝ)..1, ((starRingEnd ℂ) (F (wCLM (0, y))) * h (wCLM (0, y)))
        from intervalIntegral.integral_const_mul _ _]
  rw [hRHS, hLHS] at hgreen
  -- hgreen : boundary = 2I · ∬‖h‖².  Conclude ∬‖h‖² = -(I/2)·boundary.
  rw [hgreen]
  have h2I : -(Complex.I / 2) * (2 * Complex.I) = 1 := by
    rw [show (2 : ℂ) * Complex.I = Complex.I * 2 from by ring]
    field_simp
    rw [Complex.I_sq]; ring
  rw [← mul_assoc, h2I, one_mul]

/-! ## Rung 4: box-level positivity, interior form -/

/-- **Box-level Riemann positivity (identity form), interior.** For `h` continuous on the closed
box image, holomorphic on the open box image, with primitive `F` continuous up to the boundary,
`−(i/2)·∮_{∂box} F̄·h dz = (∬_box ‖h‖² : ℝ)`. Interior weakening of `boundaryForm_eq_area`. -/
theorem boundaryForm_eq_area_interior
    (hhc : ContinuousOn h (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)))
    (hFc : ContinuousOn F (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)))
    (hh : ∀ z ∈ wCLM '' (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1), HasDerivAt h (deriv h z) z)
    (hF : ∀ z ∈ wCLM '' (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1), HasDerivAt F (h z) z) :
    -(Complex.I / 2) * boundaryForm h F
      = ((∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖h (wCLM (x, y))‖ ^ 2 : ℝ) : ℂ) := by
  -- `boundaryForm h F` is *definitionally* the explicit boundary expression in the Green bridge,
  -- so we may ascribe the bridge's type directly.
  have hbridge : (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, (‖h (wCLM (x, y))‖ ^ 2 : ℂ))
      = -(Complex.I / 2) * boundaryForm h F :=
    integral_normSq_eq_boundary_interior hhc hFc hh hF
  have hcast : ∀ x : ℝ, (∫ y in (0:ℝ)..1, (‖h (wCLM (x, y))‖ ^ 2 : ℂ))
      = ((∫ y in (0:ℝ)..1, ‖h (wCLM (x, y))‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    push_cast; ring
  rw [← hbridge]
  simp_rw [hcast]
  exact intervalIntegral.integral_ofReal

/-- **Box-level Riemann positivity, interior form (rung 4).** For `h` continuous on the closed
box image, holomorphic on the open box image, with primitive `F` continuous up to the boundary:
if `h` is nonzero somewhere in the open box then `−(i/2)·∮_{∂box} F̄·h dz` is a strictly positive
real. Interior weakening of `boundaryForm_pos`. -/
theorem boundaryForm_pos_interior
    (hhc : ContinuousOn h (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)))
    (hFc : ContinuousOn F (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)))
    (hh : ∀ z ∈ wCLM '' (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1), HasDerivAt h (deriv h z) z)
    (hF : ∀ z ∈ wCLM '' (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1), HasDerivAt F (h z) z)
    (p₀ : ℝ × ℝ) (hp₀ : p₀ ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) (hp₀ne : h (wCLM p₀) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ -(Complex.I / 2) * boundaryForm h F = (c : ℂ) := by
  refine ⟨∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖h (wCLM (x, y))‖ ^ 2, ?_,
    boundaryForm_eq_area_interior hhc hFc hh hF⟩
  -- positivity from `integral_normSq_pos` (after rewriting `wMap → wCLM`)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => h (wMap p)) (Icc 0 1 ×ˢ Icc 0 1) := by
    rw [wMap_eq_wCLM]
    exact hhc.comp wCLM.continuous.continuousOn (Set.mapsTo_image _ _)
  have hp₀ne' : h (wMap p₀) ≠ 0 := by rw [wMap_eq_wCLM]; exact hp₀ne
  have hpos := integral_normSq_pos h hcont p₀ hp₀ hp₀ne'
  rwa [wMap_eq_wCLM] at hpos

end InteriorGreen

/-! ## Rung 5: R2 positive-definiteness, interior form -/

/-- **Riemann's second bilinear relation (positive-definiteness) from the boundary word, interior
form (rung 5).** Same conclusion as `riemann_R2_posDef_of_boundaryWord`, but the pullbacks `h_j`
and primitives `F_i` are only required to be continuous on the closed box image and holomorphic
(resp. primitives) on the open box image — the regularity a geometric cut chart at genus ≥ 2 can
actually supply. -/
theorem riemann_R2_posDef_of_boundaryWord_interior {g : ℕ}
    (A B : Matrix (Fin g) (Fin g) ℂ) (h F : Fin g → ℂ → ℂ)
    (hhc : ∀ i, ContinuousOn (h i) (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)))
    (hFc : ∀ i, ContinuousOn (F i) (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)))
    (hh : ∀ i, ∀ z ∈ wCLM '' (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1), HasDerivAt (h i) (deriv (h i) z) z)
    (hF : ∀ i, ∀ z ∈ wCLM '' (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1), HasDerivAt (F i) (h i z) z)
    (boundaryWord : ∀ i j,
      (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ)) i j
        = - boundaryForm (h j) (F i))
    (nondeg : ∀ v : Fin g → ℂ, v ≠ 0 →
      ∃ p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1, (∑ j, v j * h j (wCLM p)) ≠ 0) :
    (Complex.I • (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ))).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · -- Hermitian: `(I • (AᵀB̄ − BᵀĀ))ᴴ = I • (AᵀB̄ − BᵀĀ)`, since `(AᵀB̄ − BᵀĀ)ᴴ = −(AᵀB̄ − BᵀĀ)`.
    show (Complex.I • (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ)))ᴴ
      = Complex.I • (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ))
    rw [Matrix.conjTranspose_smul,
      show (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ))ᴴ
          = -(Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ)) from ?_]
    · rw [RCLike.star_def, Complex.conj_I, smul_neg, neg_smul, neg_neg]
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, star_sub, star_sum, star_mul',
        RCLike.star_def, Complex.conj_conj]
      rw [neg_sub]; congr 1 <;> exact Finset.sum_congr rfl (fun x _ => by ring)
  · -- positivity: `vᴴ (I • (AᵀB̄ − BᵀĀ)) v = −i·boundaryForm (h_v) (F_v) = 2·∬‖h_v‖² > 0`.
    intro v hv
    -- (a) the quadratic form expanded over entries
    have hexp : star v ⬝ᵥ ((Complex.I •
          (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ))) *ᵥ v)
        = ∑ i, ∑ j, (starRingEnd ℂ) (v i) *
            (Complex.I • (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ))) i j * v j := by
      rw [dotProduct]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by simp [Pi.star_apply, mul_assoc])
    -- (b) collapse to the boundary form via the per-entry boundary word + bilinearity
    have key : star v ⬝ᵥ ((Complex.I •
          (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ))) *ᵥ v)
        = -Complex.I * boundaryForm (fun z => ∑ j, v j * h j z) (fun z => ∑ i, v i * F i z) := by
      rw [hexp, boundaryForm_combo v h F hhc hFc, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Matrix.smul_apply, smul_eq_mul, boundaryWord i j]; ring
    -- (c) the interior Green-positivity bridge: `−(i/2)·boundaryForm (h_v) (F_v) = c > 0`
    obtain ⟨p₀, hp₀, hp₀ne⟩ := nondeg v hv
    have hhvc : ContinuousOn (fun z => ∑ j, v j * h j z) (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)) :=
      continuousOn_finsetSum _ (fun j _ => continuousOn_const.mul (hhc j))
    have hFvc : ContinuousOn (fun z => ∑ i, v i * F i z) (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)) :=
      continuousOn_finsetSum _ (fun i _ => continuousOn_const.mul (hFc i))
    have hhv : ∀ z ∈ wCLM '' (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1),
        HasDerivAt (fun z => ∑ j, v j * h j z) (deriv (fun z => ∑ j, v j * h j z) z) z := by
      intro z hz
      have hd : HasDerivAt (fun z => ∑ j, v j * h j z) (∑ j, v j * deriv (h j) z) z :=
        HasDerivAt.fun_sum (fun j _ => (hh j z hz).const_mul (v j))
      rwa [hd.deriv]
    have hFv : ∀ z ∈ wCLM '' (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1),
        HasDerivAt (fun z => ∑ i, v i * F i z) ((fun z => ∑ j, v j * h j z) z) z :=
      fun z hz => HasDerivAt.fun_sum (fun i _ => (hF i z hz).const_mul (v i))
    obtain ⟨c, hc, hceq⟩ := boundaryForm_pos_interior hhvc hFvc hhv hFv p₀ hp₀ hp₀ne
    rw [key, show -Complex.I * boundaryForm (fun z => ∑ j, v j * h j z) (fun z => ∑ i, v i * F i z)
          = 2 * (-(Complex.I / 2) *
              boundaryForm (fun z => ∑ j, v j * h j z) (fun z => ∑ i, v i * F i z)) from by ring,
      hceq, show (2 : ℂ) * (c : ℂ) = ((2 * c : ℝ) : ℂ) from by push_cast; ring]
    exact_mod_cast (by positivity : (0:ℝ) < 2 * c)

end Jacobians
