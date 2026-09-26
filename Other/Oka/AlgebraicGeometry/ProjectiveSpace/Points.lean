/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.Basic

/-!
# Points of projective space with values in a field

Let `φ : R →+* K` be a ring map to a field. A vector `z ∈ Kⁿ` gives the point `evalPoint φ z` of
`𝔸ⁿ_R = Spec R[Y₀, …, Yₙ₋₁]`, the kernel of evaluation at `z`. For `v ∈ Kⁿ⁺¹` with `vᵢ ≠ 0`, the
standard chart `i` sends the point of the dehomogenised vector `(v_{i.succAbove m} / vᵢ)ₘ` to a
point of `ℙₒ(n; R)` which lies in `U j` exactly when `vⱼ ≠ 0`
(`chart_base_evalPoint_mem_U_iff`), and which does not depend on the chart
(`chart_base_evalPoint_eq`): these are the chart transition maps `z ↦ (zₖ / zⱼ)` in coordinates.

The proof of independence goes through the degree-zero localisation at `Xᵢ Xⱼ`: evaluation at
`v` is defined on `A_(x)` for every `x` not vanishing at `v` (`awayEval`), and it is compatible
with `HomogeneousLocalization.awayMap`, so both charts factor through `Spec A_(Xᵢ Xⱼ)`
(`Proj.SpecMap_awayMap_awayι`).
-/

@[expose] public section

open CategoryTheory MvPolynomial HomogeneousLocalization

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.ProjectiveSpace

variable {n : ℕ} {R : Type u} [CommRing R] {K : Type*} [Field K] (φ : R →+* K)

local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) R

/-- The point of `𝔸ⁿ_R = Spec R[Y₀, …, Yₙ₋₁]` given by `z ∈ Kⁿ`: the kernel of evaluation at `z`
(through `φ : R →+* K`). -/
noncomputable def evalPoint (z : Fin n → K) : Spec (.of (MvPolynomial (Fin n) R)) :=
  show PrimeSpectrum (MvPolynomial (Fin n) R) from
    ⟨RingHom.ker (eval₂Hom φ z), RingHom.ker_isPrime _⟩

lemma evalPoint_asIdeal (z : Fin n → K) :
    (show PrimeSpectrum (MvPolynomial (Fin n) R) from evalPoint φ z).asIdeal =
      RingHom.ker (eval₂Hom φ z) :=
  rfl

lemma mem_evalPoint_asIdeal_iff (z : Fin n → K) (p : MvPolynomial (Fin n) R) :
    p ∈ (show PrimeSpectrum (MvPolynomial (Fin n) R) from evalPoint φ z).asIdeal ↔
      eval₂ φ z p = 0 :=
  RingHom.mem_ker

/-- For surjective `φ`, distinct vectors give distinct points of `𝔸ⁿ_R`. -/
lemma evalPoint_injective (hφ : Function.Surjective φ) :
    Function.Injective (evalPoint (n := n) φ) := by
  intro z z' h
  funext m
  obtain ⟨r, hr⟩ := hφ (z m)
  have h1 : X m - C r ∈ (show PrimeSpectrum (MvPolynomial (Fin n) R) from evalPoint φ z).asIdeal :=
    (mem_evalPoint_asIdeal_iff φ z _).2 (by simp [hr])
  rw [h, mem_evalPoint_asIdeal_iff] at h1
  simp only [eval₂_sub, eval₂_X, eval₂_C] at h1
  rw [← hr]
  exact (sub_eq_zero.1 h1).symm

/-- The dehomogenisation `(v_{i.succAbove m} / vᵢ)ₘ` of `v ∈ Kⁿ⁺¹` at the index `i`. -/
def dehomogenizeVec (i : Fin (n + 1)) (v : Fin (n + 1) → K) : Fin n → K :=
  fun m ↦ v (i.succAbove m) / v i

lemma dehomogenizeVec_smul (i : Fin (n + 1)) (v : Fin (n + 1) → K) {c : K} (hc : c ≠ 0) :
    dehomogenizeVec i (c • v) = dehomogenizeVec i v := by
  funext m
  simp only [dehomogenizeVec, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hc

@[simp]
lemma dehomogenizeVec_insertNth (i : Fin (n + 1)) (z : Fin n → K) :
    dehomogenizeVec i (Fin.insertNth i 1 z) = z := by
  funext m
  simp [dehomogenizeVec]

/-- Evaluating the dehomogenisation of `Xⱼ` at the dehomogenised vector gives `vⱼ / vᵢ`. -/
lemma eval₂_dehomogenize_X (i j : Fin (n + 1)) (v : Fin (n + 1) → K) (hi : v i ≠ 0) :
    eval₂ φ (dehomogenizeVec i v) (dehomogenize R i (X j)) = v j / v i := by
  obtain rfl | ⟨m, rfl⟩ := Fin.eq_self_or_eq_succAbove i j
  · simp [div_self hi]
  · simp [dehomogenizeVec]

/-- **The chart `i` sends the point of `v` into `U j` exactly when `vⱼ ≠ 0`.** -/
lemma chart_base_evalPoint_mem_U_iff (i j : Fin (n + 1)) (v : Fin (n + 1) → K) (hi : v i ≠ 0) :
    (chart (R := R) i).base (evalPoint φ (dehomogenizeVec i v)) ∈ U n R j ↔ v j ≠ 0 := by
  change evalPoint φ (dehomogenizeVec i v) ∈ chart i ⁻¹ᵁ U n R j ↔ _
  rw [chart_preimage_U]
  change dehomogenize R i (X j) ∉
      (show PrimeSpectrum (MvPolynomial (Fin n) R) from
        evalPoint φ (dehomogenizeVec i v)).asIdeal ↔ _
  rw [mem_evalPoint_asIdeal_iff, eval₂_dehomogenize_X φ i j v hi]
  simp [hi]

variable {φ}

/-- Evaluation at `v` on the degree-zero localisation `A_(x)`, for `x` not vanishing at `v`. -/
noncomputable def awayEval (v : Fin (n + 1) → K) (x : MvPolynomial (Fin (n + 1)) R)
    (hx : eval₂ φ v x ≠ 0) : Away 𝒜 x →+* K :=
  (Localization.awayLift (eval₂Hom φ v) x (by simpa using hx.isUnit)).comp
    (algebraMap (Away 𝒜 x) (Localization.Away x))

/-- The point of `Spec A_(x)` given by evaluation at `v`. -/
noncomputable def awayPoint (v : Fin (n + 1) → K) (x : MvPolynomial (Fin (n + 1)) R)
    (hx : eval₂ φ v x ≠ 0) : PrimeSpectrum (Away 𝒜 x) :=
  ⟨RingHom.ker (awayEval v x hx), RingHom.ker_isPrime _⟩

lemma awayEval_comp_awayMap (v : Fin (n + 1) → K) {f g x : MvPolynomial (Fin (n + 1)) R}
    {e : ℕ} (hg : g ∈ 𝒜 e) (hx : x = f * g) (hf : eval₂ φ v f ≠ 0)
    (hx' : eval₂ φ v x ≠ 0) :
    (awayEval v x hx').comp (awayMap 𝒜 hg hx) = awayEval v f hf := by
  have key : (Localization.awayLift (eval₂Hom φ v) x (by simpa using hx'.isUnit)).comp
      (Localization.awayLift (algebraMap _ (Localization.Away x)) f
        (isUnit_of_dvd_unit (map_dvd _ ⟨_, hx⟩) (IsLocalization.Away.algebraMap_isUnit x))) =
      Localization.awayLift (eval₂Hom φ v) f (by simpa using hf.isUnit) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
    ext b
    · simp only [RingHom.coe_comp, Function.comp_apply]
      rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
    · simp only [RingHom.coe_comp, Function.comp_apply]
      rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
  ext a
  simp only [awayEval, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, val_awayMap]
  exact congrArg (fun F : Localization.Away f →+* K ↦ F a.val) key

lemma awayEval_comp_toAwayX (v : Fin (n + 1) → K) (i : Fin (n + 1)) (hi : eval₂ φ v (X i) ≠ 0) :
    (awayEval v (X i) hi).comp (toAwayX R i) = eval₂Hom φ (dehomogenizeVec i v) := by
  have hi' : v i ≠ 0 := by simpa using hi
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun m ↦ ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply, toAwayX_C, awayEval, awayXBase,
      HomogeneousLocalization.algebraMap_apply, coe_eval₂Hom, eval₂_C]
    change Localization.awayLift _ _ _ (Localization.mk _ 1) = _
    rw [Localization.mk_one_eq_algebraMap, IsLocalization.Away.lift_eq]
    simp [MvPolynomial.algebraMap_eq]
  · simp only [RingHom.coe_comp, Function.comp_apply, toAwayX_X, awayEval,
      HomogeneousLocalization.algebraMap_apply, val_awayXDiv, coe_eval₂Hom, eval₂_X]
    rw [Localization.awayLift_mk (v := (v i)⁻¹) (hv := by simp [hi'])]
    simp [dehomogenizeVec, div_eq_mul_inv]

lemma eval₂Hom_comp_fromAwayX (v : Fin (n + 1) → K) (i : Fin (n + 1))
    (hi : eval₂ φ v (X i) ≠ 0) :
    (eval₂Hom φ (dehomogenizeVec i v)).comp (fromAwayX R i) = awayEval v (X i) hi := by
  rw [← awayEval_comp_toAwayX v i hi]
  ext a
  simp

/-- The chart `i` at the point of `v` is the image of `awayPoint v (X i)` under `Proj.awayι`. -/
lemma chart_base_evalPoint (v : Fin (n + 1) → K) (i : Fin (n + 1)) (hi : eval₂ φ v (X i) ≠ 0) :
    (chart (R := R) i).base (evalPoint φ (dehomogenizeVec i v)) =
      (Proj.awayι 𝒜 (X i) (X_mem_homogeneousSubmodule_one i) Nat.one_pos).base
        (awayPoint v (X i) hi) := by
  rw [chart, Scheme.Hom.comp_apply]
  congr 1
  refine PrimeSpectrum.ext ?_
  change Ideal.comap _ (RingHom.ker _) = RingHom.ker _
  rw [RingHom.comap_ker, ← eval₂Hom_comp_fromAwayX v i hi]
  congr 2
  ext a
  simp

lemma awayι_base_awayPoint_eq_mul (v : Fin (n + 1) → K) {f g x : MvPolynomial (Fin (n + 1)) R}
    {e : ℕ} (hf' : f ∈ 𝒜 1) (hg : g ∈ 𝒜 e) (hx : x = f * g) (hf : eval₂ φ v f ≠ 0)
    (hx' : eval₂ φ v x ≠ 0) :
    (Proj.awayι 𝒜 f hf' Nat.one_pos).base (awayPoint v f hf) =
      (Proj.awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded hf' hg)
        (Nat.one_pos.trans_le (Nat.le_add_right 1 e))).base (awayPoint v x hx') := by
  rw [← Proj.SpecMap_awayMap_awayι 𝒜 (f_deg := hf') (hm := Nat.one_pos) (g_deg := hg)
    (hx := hx), Scheme.Hom.comp_apply]
  congr 1
  refine PrimeSpectrum.ext ?_
  change RingHom.ker _ = Ideal.comap _ (RingHom.ker _)
  rw [RingHom.comap_ker]
  congr 1
  exact (awayEval_comp_awayMap v hg hx hf hx').symm

variable (φ)

/-- **The chart transition maps in coordinates**: for `vᵢ ≠ 0` and `vⱼ ≠ 0`, the charts `i` and
`j` send the dehomogenisations of `v` at `i` and at `j` to the same point of `ℙₒ(n; R)`. -/
lemma chart_base_evalPoint_eq (i j : Fin (n + 1)) (v : Fin (n + 1) → K) (hi : v i ≠ 0)
    (hj : v j ≠ 0) :
    (chart (R := R) i).base (evalPoint φ (dehomogenizeVec i v)) =
      (chart (R := R) j).base (evalPoint φ (dehomogenizeVec j v)) := by
  have hi' : eval₂ φ v (X i : MvPolynomial (Fin (n + 1)) R) ≠ 0 := by simpa using hi
  have hj' : eval₂ φ v (X j : MvPolynomial (Fin (n + 1)) R) ≠ 0 := by simpa using hj
  have hij : eval₂ φ v (X i * X j : MvPolynomial (Fin (n + 1)) R) ≠ 0 := by simp [hi, hj]
  rw [chart_base_evalPoint v i hi', chart_base_evalPoint v j hj',
    awayι_base_awayPoint_eq_mul v (X_mem_homogeneousSubmodule_one i)
      (X_mem_homogeneousSubmodule_one j) rfl hi' hij,
    awayι_base_awayPoint_eq_mul v (X_mem_homogeneousSubmodule_one j)
      (X_mem_homogeneousSubmodule_one i) (mul_comm _ _) hj' hij]

end AlgebraicGeometry.ProjectiveSpace

end
