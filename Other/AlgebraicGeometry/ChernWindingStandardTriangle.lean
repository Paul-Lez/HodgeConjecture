/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingCochain
public import Other.AlgebraicTopology.EuclideanLocalHomology
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The winding number of the identity around the standard punctured boundary class

This file computes the number that fixes the sign in the normalisation obligation
`ChernWindingChart.NormalizesCoclass`.

The repository's generator of `H₁(ℝ² ∖ {0}; ℚ)` is
`AlgebraicTopology.Singular.standardPuncturedBoundaryClass 1`, the class of the oriented boundary
`∑ᵢ (-1)ⁱ dᵢ` of the standard affine `2`-simplex, whose vertices are `(1,0)`, `(0,1)` and
`(-1,-1)` and whose barycentre is the origin.  Identifying `ℝ²` with `ℂ` by
`v ↦ v 0 + v 1 · I`, this file proves

  `ChernWinding.windingPeriod complexCoordinate _ (standardPuncturedBoundaryClass 1) = 1`.

So the repository's orientation of the punctured plane and the winding number
`(1/2πi) ∮ d log z` agree: **the sign is `+1`, not `−1`**.

The computation is elementary.  Each face of the triangle is an affine segment; on each of them a
suitable rotation of the principal branch of `Complex.log` is a continuous logarithm
(`ChernWinding.logIncrement_of_slitPlane`), so the three increments are differences of principal
logarithms, and their alternating sum is `2πi`:

  `Log I + (Log (-1 + I) - Log 1) - (Log (-1 - I) - Log 1) = iπ/2 + 3iπ/4 + 3iπ/4 = 2πi`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Simplicial AlgebraicTopology.Singular

namespace ChernWinding

/-! ### Increments computed by a rotated principal branch -/

/-- If a rotation `c · γ` of a nowhere vanishing path avoids the branch cut of the principal
logarithm, the logarithmic increment of `γ` is the difference of the principal logarithms of the
rotated endpoints. -/
theorem logIncrement_of_slitPlane {A : Type*} [TopologicalSpace A] [SimplyConnectedSpace A]
    [LocallyPathConnectedSpace A] (γ : C(A, ℂ)) (hγ : ∀ a, γ a ≠ 0) (c : ℂ) (hc : c ≠ 0)
    (hslit : ∀ a, c * γ a ∈ Complex.slitPlane) (a b : A) :
    logIncrement γ hγ a b = Complex.log (c * γ b) - Complex.log (c * γ a) := by
  have hcont : Continuous fun t : A => Complex.log (c * γ t) - Complex.log c :=
    (Continuous.clog (continuous_const.mul γ.continuous) hslit).sub continuous_const
  have hexp : ∀ t : A, Complex.exp ((⟨_, hcont⟩ : C(A, ℂ)) t) = γ t := by
    intro t
    show Complex.exp (Complex.log (c * γ t) - Complex.log c) = γ t
    rw [Complex.exp_sub, Complex.exp_log (mul_ne_zero hc (hγ t)), Complex.exp_log hc,
      mul_div_cancel_left₀ _ hc]
  rw [logIncrement_eq γ hγ ⟨_, hcont⟩ hexp]
  show (Complex.log (c * γ b) - Complex.log c) - (Complex.log (c * γ a) - Complex.log c) = _
  ring

/-! ### The standard triangle -/

/-- The identification of the standard real plane with `ℂ`. -/
def complexCoordinateFun (v : StandardRealModel 2) : ℂ := v 0 + v 1 * Complex.I

@[simp] theorem complexCoordinateFun_re (v : StandardRealModel 2) :
    (complexCoordinateFun v).re = v 0 := by simp [complexCoordinateFun]

@[simp] theorem complexCoordinateFun_im (v : StandardRealModel 2) :
    (complexCoordinateFun v).im = v 1 := by simp [complexCoordinateFun]

theorem continuous_complexCoordinateFun : Continuous complexCoordinateFun := by
  unfold complexCoordinateFun
  fun_prop

theorem complexCoordinateFun_ne_zero {v : StandardRealModel 2} (hv : v ≠ 0) :
    complexCoordinateFun v ≠ 0 := by
  intro h
  refine hv (funext fun j => ?_)
  have h0 : (complexCoordinateFun v).re = 0 := by rw [h]; simp
  have h1 : (complexCoordinateFun v).im = 0 := by rw [h]; simp
  rw [complexCoordinateFun_re] at h0
  rw [complexCoordinateFun_im] at h1
  fin_cases j
  · simpa using h0
  · simpa using h1

/-- The identification of the punctured real plane with the punctured complex line. -/
def complexCoordinate : C((standardPuncturedPair 2).snd, ℂ) :=
  ⟨fun v => complexCoordinateFun v.1,
    continuous_complexCoordinateFun.comp continuous_subtype_val⟩

theorem complexCoordinate_ne_zero (v : (standardPuncturedPair 2).snd) :
    complexCoordinate v ≠ 0 :=
  complexCoordinateFun_ne_zero v.2

/-- The coordinates of the image of a point of the standard `1`-simplex under a face map. -/
theorem map_succAbove_apply (i : Fin 3) (t : stdSimplex ℝ (Fin 2)) (k : Fin 3) :
    (stdSimplex.map i.succAbove t : Fin 3 → ℝ) k =
      ∑ j ∈ Finset.univ.filter (fun j : Fin 2 => i.succAbove j = k), (t : Fin 2 → ℝ) j := by
  simpa using FunOnFinite.linearMap_apply_apply ℝ ℝ i.succAbove (t : Fin 2 → ℝ) k

/-- The complex coordinate of a point of the `i`-th face of the standard triangle. -/
theorem complexCoordinate_faceMap (i : Fin 3) (t : stdSimplex ℝ (Fin 2)) :
    complexCoordinate (standardFaceMap 1 i t) =
      complexCoordinateFun (standardAffineSimplex 2 (stdSimplex.map i.succAbove t)) := rfl

theorem map_succAbove_val (i : Fin 3) (t : stdSimplex ℝ (Fin 2)) (k : Fin 3) :
    (stdSimplex.map i.succAbove t : Fin 3 → ℝ) k =
      (if i.succAbove 0 = k then (t : Fin 2 → ℝ) 0 else 0) +
      (if i.succAbove 1 = k then (t : Fin 2 → ℝ) 1 else 0) := by
  rw [map_succAbove_apply, Finset.sum_filter, Fin.sum_univ_two]

theorem affineSimplex_two (s : stdSimplex ℝ (Fin 3)) :
    complexCoordinateFun (standardAffineSimplex 2 s) =
      (((s : Fin 3 → ℝ) 0 - (s : Fin 3 → ℝ) 2 : ℝ) : ℂ) +
        (((s : Fin 3 → ℝ) 1 - (s : Fin 3 → ℝ) 2 : ℝ) : ℂ) * Complex.I := rfl

/-- The `0`-th face: the segment from `I` to `-1 - I`. -/
theorem complexCoordinate_face_zero (t : stdSimplex ℝ (Fin 2)) :
    complexCoordinate (standardFaceMap 1 0 t) =
      ((-(t : Fin 2 → ℝ) 1 : ℝ) : ℂ) +
        ((((t : Fin 2 → ℝ) 0 - (t : Fin 2 → ℝ) 1 : ℝ)) : ℂ) * Complex.I := by
  have h0 : (0 : Fin 3).succAbove 0 = 1 := by decide
  have h1 : (0 : Fin 3).succAbove 1 = 2 := by decide
  rw [complexCoordinate_faceMap, affineSimplex_two]
  simp only [map_succAbove_val, h0, h1, Fin.reduceEq, reduceIte]
  push_cast
  ring

/-- The `1`-st face: the segment from `1` to `-1 - I`. -/
theorem complexCoordinate_face_one (t : stdSimplex ℝ (Fin 2)) :
    complexCoordinate (standardFaceMap 1 1 t) =
      ((((t : Fin 2 → ℝ) 0 - (t : Fin 2 → ℝ) 1 : ℝ)) : ℂ) +
        ((-(t : Fin 2 → ℝ) 1 : ℝ) : ℂ) * Complex.I := by
  have h0 : (1 : Fin 3).succAbove 0 = 0 := by decide
  have h1 : (1 : Fin 3).succAbove 1 = 2 := by decide
  rw [complexCoordinate_faceMap, affineSimplex_two]
  simp only [map_succAbove_val, h0, h1, Fin.reduceEq, reduceIte]
  push_cast
  ring

/-- The `2`-nd face: the segment from `1` to `I`. -/
theorem complexCoordinate_face_two (t : stdSimplex ℝ (Fin 2)) :
    complexCoordinate (standardFaceMap 1 2 t) =
      (((t : Fin 2 → ℝ) 0 : ℝ) : ℂ) + (((t : Fin 2 → ℝ) 1 : ℝ) : ℂ) * Complex.I := by
  have h0 : (2 : Fin 3).succAbove 0 = 0 := by decide
  have h1 : (2 : Fin 3).succAbove 1 = 1 := by decide
  rw [complexCoordinate_faceMap, affineSimplex_two]
  simp only [map_succAbove_val, h0, h1, Fin.reduceEq, reduceIte]
  push_cast
  ring

/-! ### Two values of the principal logarithm -/

theorem arcsin_one_div_sqrt_two : Real.arcsin (1 / Real.sqrt 2) = Real.pi / 4 := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e : (1 : ℝ) / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp
    linarith [hs]
  rw [e, ← Real.sin_pi_div_four, Real.arcsin_sin] <;> nlinarith [Real.pi_pos]

theorem norm_neg_one_add_I : ‖(-1 + Complex.I : ℂ)‖ = Real.sqrt 2 := by
  rw [Complex.norm_def, Complex.normSq_apply]
  norm_num

theorem norm_neg_one_sub_I : ‖(-1 - Complex.I : ℂ)‖ = Real.sqrt 2 := by
  rw [Complex.norm_def, Complex.normSq_apply]
  norm_num

theorem arg_neg_one_add_I : (-1 + Complex.I : ℂ).arg = -(Real.pi / 4) + Real.pi := by
  rw [Complex.arg_of_re_neg_of_im_nonneg (by norm_num) (by norm_num), norm_neg_one_add_I]
  norm_num [← arcsin_one_div_sqrt_two, ← Real.arcsin_neg, neg_div]

theorem arg_neg_one_sub_I : (-1 - Complex.I : ℂ).arg = Real.pi / 4 - Real.pi := by
  rw [Complex.arg_of_re_neg_of_im_neg (by norm_num) (by norm_num), norm_neg_one_sub_I]
  norm_num [← arcsin_one_div_sqrt_two]

/-- The difference of the principal logarithms at the two lower vertices of the triangle. -/
theorem log_neg_one_add_I_sub_log_neg_one_sub_I :
    Complex.log (-1 + Complex.I) - Complex.log (-1 - Complex.I) =
      ((3 * Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re, norm_neg_one_add_I, norm_neg_one_sub_I]
  · simp only [Complex.sub_im, Complex.log_im, arg_neg_one_add_I, arg_neg_one_sub_I,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re]
    ring

/-! ### The three increments -/

theorem simplexMap_standardFaceSimplex (i : Fin 3) :
    simplexMap (standardFaceSimplex 1 i) = standardFaceMap 1 i :=
  Equiv.apply_symm_apply _ _

theorem simplexPullback_standardFaceSimplex (i : Fin 3) :
    simplexPullback complexCoordinate (standardFaceSimplex 1 i) =
      complexCoordinate.comp (standardFaceMap 1 i) :=
  congrArg complexCoordinate.comp (simplexMap_standardFaceSimplex i)

/-- The increment of `log z` along a face of the standard triangle, computed by a rotated
principal branch. -/
theorem simplexIncrement_standardFace (i : Fin 3) (c : ℂ) (hc : c ≠ 0)
    (hslit : ∀ t : stdSimplex ℝ (Fin 2),
      c * complexCoordinate (standardFaceMap 1 i t) ∈ Complex.slitPlane) :
    simplexIncrement complexCoordinate complexCoordinate_ne_zero (standardFaceSimplex 1 i) =
      Complex.log (c * complexCoordinate (standardFaceMap 1 i (stdSimplex.vertex 1))) -
        Complex.log (c * complexCoordinate (standardFaceMap 1 i (stdSimplex.vertex 0))) := by
  rw [simplexIncrement, logIncrement_congr _
    (fun t => complexCoordinate_ne_zero (standardFaceMap 1 i t))
    (simplexPullback_standardFaceSimplex i)]
  exact logIncrement_of_slitPlane _ _ c hc hslit _ _

@[simp] theorem vertex_zero_zero :
    ((stdSimplex.vertex (0 : Fin 2) : stdSimplex ℝ (Fin 2)) : Fin 2 → ℝ) 0 = 1 := by
  simp [stdSimplex.vertex_coe]

@[simp] theorem vertex_zero_one :
    ((stdSimplex.vertex (0 : Fin 2) : stdSimplex ℝ (Fin 2)) : Fin 2 → ℝ) 1 = 0 := by
  simp [stdSimplex.vertex_coe]

@[simp] theorem vertex_one_zero :
    ((stdSimplex.vertex (1 : Fin 2) : stdSimplex ℝ (Fin 2)) : Fin 2 → ℝ) 0 = 0 := by
  simp [stdSimplex.vertex_coe]

@[simp] theorem vertex_one_one :
    ((stdSimplex.vertex (1 : Fin 2) : stdSimplex ℝ (Fin 2)) : Fin 2 → ℝ) 1 = 1 := by
  simp [stdSimplex.vertex_coe]

theorem simplexIncrement_face_two_eq :
    simplexIncrement complexCoordinate complexCoordinate_ne_zero (standardFaceSimplex 1 2) =
      Complex.log Complex.I := by
  have hslit : ∀ t : stdSimplex ℝ (Fin 2),
      (1 : ℂ) * complexCoordinate (standardFaceMap 1 2 t) ∈ Complex.slitPlane := by
    intro t
    rw [one_mul, complexCoordinate_face_two, Complex.mem_slitPlane_iff]
    have h01 := stdSimplex.add_eq_one t
    rcases eq_or_lt_of_le (stdSimplex.zero_le t 0) with h | h
    · right
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, Complex.ofReal_im]
      intro hz
      simp only [mul_one, mul_zero, add_zero, zero_add] at hz
      rw [← h] at h01
      simp only [zero_add] at h01
      rw [h01] at hz
      exact one_ne_zero hz
    · left
      simpa using h
  rw [simplexIncrement_standardFace 2 1 one_ne_zero hslit, one_mul, one_mul,
    complexCoordinate_face_two, complexCoordinate_face_two]
  norm_num

theorem simplexIncrement_face_one_eq :
    simplexIncrement complexCoordinate complexCoordinate_ne_zero (standardFaceSimplex 1 1) =
      Complex.log (-1 - Complex.I) := by
  have hslit : ∀ t : stdSimplex ℝ (Fin 2),
      (1 : ℂ) * complexCoordinate (standardFaceMap 1 1 t) ∈ Complex.slitPlane := by
    intro t
    rw [one_mul, complexCoordinate_face_one, Complex.mem_slitPlane_iff]
    have h01 := stdSimplex.add_eq_one t
    rcases eq_or_lt_of_le (stdSimplex.zero_le t 1) with h | h
    · left
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im]
      rw [← h] at h01 ⊢
      simp only [add_zero] at h01
      simp [h01]
    · right
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re]
      simp only [mul_one, mul_zero, add_zero, zero_add]
      linarith
  rw [simplexIncrement_standardFace 1 1 one_ne_zero hslit, one_mul, one_mul,
    complexCoordinate_face_one, complexCoordinate_face_one]
  norm_num
  rw [sub_eq_add_neg]

theorem simplexIncrement_face_zero_eq :
    simplexIncrement complexCoordinate complexCoordinate_ne_zero (standardFaceSimplex 1 0) =
      Complex.log (-1 + Complex.I) := by
  have hslit : ∀ t : stdSimplex ℝ (Fin 2),
      (-Complex.I) * complexCoordinate (standardFaceMap 1 0 t) ∈ Complex.slitPlane := by
    intro t
    rw [complexCoordinate_face_zero, Complex.mem_slitPlane_iff]
    have h01 := stdSimplex.add_eq_one t
    rcases eq_or_lt_of_le (stdSimplex.zero_le t 1) with h | h
    · left
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
        Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
      rw [← h] at h01 ⊢
      simp only [add_zero] at h01
      simp [h01]
    · right
      simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
        Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re]
      simp only [neg_zero, zero_mul, mul_zero, mul_one, sub_zero, neg_neg, add_zero,
        zero_add, neg_mul, one_mul]
      linarith
  rw [simplexIncrement_standardFace 0 (-Complex.I) (by simp) hslit,
    complexCoordinate_face_zero, complexCoordinate_face_zero]
  norm_num
  congr 1
  apply Complex.ext <;> simp

/-! ### The winding number of the boundary class -/

/-- The alternating sum of the three increments around the standard triangle is `2πi`. -/
theorem sum_simplexIncrement_standardFace :
    ∑ i : Fin 3, (-1 : ℂ) ^ (i : ℕ) *
        simplexIncrement complexCoordinate complexCoordinate_ne_zero
          (standardFaceSimplex 1 i) = twoPiI := by
  rw [Fin.sum_univ_three, simplexIncrement_face_zero_eq, simplexIncrement_face_one_eq,
    simplexIncrement_face_two_eq, Complex.log_I, twoPiI]
  have h := log_neg_one_add_I_sub_log_neg_one_sub_I
  push_cast at h
  norm_num
  linear_combination h

set_option backward.isDefEq.respectTransparency false in
/-- **The winding number of the repository's generator of `H₁(ℝ² ∖ {0}; ℚ)` is `+1`.**

The sign is positive: the orientation used by `standardPuncturedBoundaryClass` — hence by
`standardLocalClass`, `standardComplexLocalClass`, `chartNormalProjectionCoclass` and
`cycleComponentSmoothSupportCoclassSection` — is the one for which the winding number
`(1/2πi) ∮ d log z` of the complex coordinate is `+1`. -/
theorem windingPeriod_standardPuncturedBoundaryClass :
    windingPeriod complexCoordinate complexCoordinate_ne_zero
      (standardPuncturedBoundaryClass 1) = 1 := by
  have hlift : standardPuncturedBoundaryCycle 1 ≫
      (singularChains (standardPuncturedPair 2).snd).iCycles 1 =
      standardSubspaceBoundaryChain 1 :=
    HomologicalComplex.liftCycles_i _ _ _ _ _
  have h1 : windingPeriod complexCoordinate complexCoordinate_ne_zero
      (standardPuncturedBoundaryClass 1) =
      ((standardPuncturedBoundaryCycle 1 ≫
        (singularChains (standardPuncturedPair 2).snd).iCycles 1 ≫
        windingCochain complexCoordinate complexCoordinate_ne_zero).hom) 1 := by
    rw [← homologyπ_comp_windingPeriodHom]
    rfl
  have hterm : ∀ i : Fin 3,
      (((-1 : ℤ) ^ (i : ℕ) • standardSubspaceFaceChain 1 i) ≫
          windingCochain complexCoordinate complexCoordinate_ne_zero) =
        scalarHomDiv ((-1 : ℂ) ^ (i : ℕ) *
          simplexIncrement complexCoordinate complexCoordinate_ne_zero
            (standardFaceSimplex 1 i)) := by
    intro i
    rw [Preadditive.zsmul_comp]
    rw [show (standardSubspaceFaceChain 1 i ≫
        windingCochain complexCoordinate complexCoordinate_ne_zero) =
      scalarHom (simplexIncrement complexCoordinate complexCoordinate_ne_zero
        (standardFaceSimplex 1 i) / twoPiI) from
      ιChainComplex_comp_windingCochain complexCoordinate complexCoordinate_ne_zero
        (standardFaceSimplex 1 i)]
    rw [scalarHomDiv_apply,
      show ((-1 : ℂ) ^ (i : ℕ) * simplexIncrement complexCoordinate complexCoordinate_ne_zero
          (standardFaceSimplex 1 i)) / twoPiI =
        (((-1 : ℤ) ^ (i : ℕ) : ℤ) : ℂ) *
          (simplexIncrement complexCoordinate complexCoordinate_ne_zero
            (standardFaceSimplex 1 i) / twoPiI) by push_cast; ring]
    exact (scalarHom_zsmul _ _).symm
  rw [h1, ← Category.assoc, hlift, standardSubspaceBoundaryChain, Preadditive.sum_comp]
  simp_rw [hterm]
  rw [← map_sum scalarHomDiv, sum_simplexIncrement_standardFace, scalarHomDiv_apply,
    div_self twoPiI_ne_zero]
  simp [LinearMap.toSpanSingleton]

end ChernWinding
