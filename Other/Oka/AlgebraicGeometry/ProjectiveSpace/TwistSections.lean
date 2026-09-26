/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.Twist
public import Other.Oka.RingTheory.MvPolynomial.LaurentAway

/-!
# Sections of the twisting sheaves over the standard opens and global sections

Let `A = R[X₀, …, Xₙ]` and, for a finite set `I` of indices, `X_I = ∏_{j ∈ I} Xⱼ`. For `I`
nonempty, the sections of `O(k)` over `UI I = D₊(X_I)` are the homogeneous elements of degree `k`
of `A[1 / X_I]` (`MvPolynomial.awayDegree R I k`): a section `s` corresponds to `Xᵢᵏ · sᵢ` for any
`i ∈ I`, where `sᵢ ∈ Γ(𝒪, UI I) ≅ A_(X_I)` is its `i`-th component. Under this identification
restrictions are the localisation maps `A[1 / X_I] → A[1 / X_J]` (`MvPolynomial.awayRestr`), so
the Čech complex of `O(k)` for the standard cover is the one of
`Other/Oka/RingTheory/MvPolynomial/CechProjectiveAway.lean`.

For `n ≥ 1`, the global sections of `O(d)` are the homogeneous polynomials of degree `d`, and
`O(k)` has no nonzero global sections for `k < 0`.

## Main definitions and results

- `ProjectiveSpace.sectionsUIEquiv I k hI : Γ(O(k), UI I) ≃+ awayDegree R I k`, with
  `sectionsUIEquiv_apply` (the formula in any chart `i ∈ I`), `sectionsUIEquiv_smul`
  (compatibility with the action of `Γ(𝒪, UI I) ≅ A_(X_I)`) and `sectionsUIEquiv_res`
  (restriction is `awayRestr`).
- `ProjectiveSpace.globalSectionsEquiv hn d : Γ(O(d), ⊤) ≃+ A_d` for `n ≥ 1`, with
  `sectionsUIEquiv_globalSectionsEquiv_symm` (`p ↦ p / Xᵢᵈ` on `Uᵢ`).
- `ProjectiveSpace.globalSections_eq_zero`: `Γ(O(k), ⊤) = 0` for `k < 0`, `n ≥ 1`.
-/

@[expose] public section

open CategoryTheory MvPolynomial HomogeneousLocalization TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry.ProjectiveSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.ProjectiveSpace

variable {n : ℕ} {R : Type u} [CommRing R]

local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) R

section Units

/-- `Xⱼ / Xᵢ` as a unit over any `W ≤ Uᵢ ∩ Uⱼ`. -/
noncomputable def xDivUnit (i j : Fin (n + 1)) (W : ℙₒ(n; R).Opens) (hW : W ≤ U n R i ⊓ U n R j) :
    Γ(ℙₒ(n; R), W)ˣ where
  val := xDiv i j |ₒ W
  inv := xDiv j i |ₒ W
  val_inv := by rw [xDiv_mul_xDiv i j i W hW, xDiv_self, ores_one]
  inv_val := by rw [xDiv_mul_xDiv j i j W (by order), xDiv_self, ores_one]

lemma cocycle_zpow_g_res (k : ℤ) (i j : Fin (n + 1)) (W : ℙₒ(n; R).Opens)
    (hW : W ≤ U n R i ⊓ U n R j) :
    ((cocycle n R ^ k).g i j |ₒ W) =
      ((xDivUnit i j W hW ^ k : Γ(ℙₒ(n; R), W)ˣ) : Γ(ℙₒ(n; R), W)) := by
  induction k using Int.induction_on with
  | zero => simp only [zpow_zero, Cocycle.one_g, ores_one, Units.val_one]
  | succ k ih =>
    rw [zpow_add_one, Cocycle.mul_g, ores_mul, ih, zpow_add_one, Units.val_mul]
    simp only [cocycle_g, ores_res]
    rfl
  | pred k ih =>
    rw [zpow_sub_one, Cocycle.mul_g, ores_mul, ih, zpow_sub_one, Units.val_mul, Cocycle.inv_g,
      cocycle_g, ores_res, ores_res]
    rfl

end Units

section UI

variable {I : Finset (Fin (n + 1))}

variable (I) in
/-- The sections of `𝒪` over `UI I = D₊(X_I)` are the degree-zero part `A_(X_I)` of
`A[1 / X_I]`, `X_I = ∏_{j ∈ I} Xⱼ`. -/
noncomputable def sectionsUIRingEquiv (hI : I.Nonempty) :
    Γ(ℙₒ(n; R), UI n R I) ≃+* Away 𝒜 (∏ j ∈ I, X j) :=
  (Proj.basicOpenIsoAway 𝒜 _ (prod_X_mem_homogeneousSubmodule I)
    (Finset.card_pos.mpr hI)).commRingCatIsoToRingEquiv.symm

lemma sectionsUIRingEquiv_symm_apply (hI : I.Nonempty) (a : Away 𝒜 (∏ j ∈ I, X j)) :
    (sectionsUIRingEquiv I hI).symm a = Proj.awayToSection 𝒜 _ a :=
  rfl

variable (R I) in
/-- `X_I = ∏_{j ∈ I} Xⱼ` as an element of `A = R[X₀, …, Xₙ]`. -/
noncomputable abbrev prodX : MvPolynomial (Fin (n + 1)) R := ∏ j ∈ I, X j

variable (I) in
/-- The ring map `Γ(ℙₒ(n; R), UI I) ≅ A_(X_I) ⊆ A[1 / X_I]`. -/
noncomputable def toAway (hI : I.Nonempty) :
    Γ(ℙₒ(n; R), UI n R I) →+* Localization.Away (prodX R I) :=
  (algebraMap (Away 𝒜 (prodX R I)) _).comp (sectionsUIRingEquiv I hI).toRingHom

lemma toAway_injective (hI : I.Nonempty) : Function.Injective (toAway (R := R) I hI) :=
  (val_injective _).comp (sectionsUIRingEquiv I hI).injective

lemma toAway_awayToSection (hI : I.Nonempty) (a : Away 𝒜 (prodX R I)) :
    toAway I hI (Proj.awayToSection 𝒜 _ a) = a.val := by
  rw [← sectionsUIRingEquiv_symm_apply hI]
  simp [toAway]

variable (R) in
/-- `Xᵢ` is a unit in `A[1 / X_I]` for `i ∈ I`. -/
noncomputable def xUnit {i : Fin (n + 1)} (hi : i ∈ I) : (Localization.Away (prodX R I))ˣ :=
  (isUnit_of_dvd_unit (map_dvd (algebraMap _ _) (Finset.dvd_prod_of_mem X hi))
    (IsLocalization.Away.algebraMap_isUnit (prodX R I))).unit

@[simp]
lemma val_xUnit {i : Fin (n + 1)} (hi : i ∈ I) :
    (xUnit R hi : Localization.Away (prodX R I)) =
      algebraMap (MvPolynomial (Fin (n + 1)) R) (Localization.Away (prodX R I)) (X i) :=
  rfl

lemma toAway_xDiv (hI : I.Nonempty) {i : Fin (n + 1)} (hi : i ∈ I) (j : Fin (n + 1)) :
    toAway I hI (TopCat.Presheaf.restrictOpen (xDiv i j) (UI n R I) (UI_le_U hi)) *
      algebraMap (MvPolynomial (Fin (n + 1)) R) (Localization.Away (prodX R I)) (X i) =
        algebraMap (MvPolynomial (Fin (n + 1)) R) (Localization.Away (prodX R I)) (X j) := by
  have hx := (Finset.mul_prod_erase I (fun j ↦ (X j : MvPolynomial (Fin (n + 1)) R)) hi).symm
  have hg := prod_X_mem_homogeneousSubmodule (R := R) (I.erase i)
  have := xDiv_res i j hg hx
  rw [this, toAway_awayToSection, awayXDiv, awayMap_mk, Away.val_mk,
    ← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, pow_one, mul_one]
  rw [hx]
  ring

lemma units_map_toAway_xDivUnit (hI : I.Nonempty) {i j : Fin (n + 1)} (hi : i ∈ I) (hj : j ∈ I)
    (h : UI n R I ≤ U n R i ⊓ U n R j) :
    Units.map (toAway I hI).toMonoidHom (xDivUnit i j (UI n R I) h) =
      xUnit R hj * (xUnit R hi)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  ext
  exact toAway_xDiv hI hi j

section Algebra

variable {i : Fin (n + 1)} (hi : i ∈ I)

include hi in
lemma card_erase_add_one : (I.erase i).card + 1 = I.card :=
  Finset.card_erase_add_one hi

include hi in
lemma prodX_eq : prodX R I = X i * prodX R (I.erase i) :=
  (Finset.mul_prod_erase I (fun j ↦ (X j : MvPolynomial (Fin (n + 1)) R)) hi).symm

variable (R I) in
/-- `X_Iᵐ` as an element of the submonoid of powers of `X_I`. -/
noncomputable def powX (m : ℕ) : Submonoid.powers (prodX R I) :=
  ⟨prodX R I ^ m, pow_mem (Submonoid.mem_powers _) m⟩

@[simp]
lemma val_powX (m : ℕ) : (powX R I m : MvPolynomial (Fin (n + 1)) R) = prodX R I ^ m :=
  rfl

lemma mk_eq_mk_of {a c : MvPolynomial (Fin (n + 1)) R} {b d : Submonoid.powers (prodX R I)}
    (h : (d : MvPolynomial (Fin (n + 1)) R) * a = b * c) :
    (Localization.mk a b : Localization.Away (prodX R I)) = Localization.mk c d := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; exact h⟩

lemma algebraMap_mul_mk (q a : MvPolynomial (Fin (n + 1)) R) (b : Submonoid.powers (prodX R I)) :
    algebraMap _ (Localization.Away (prodX R I)) q * Localization.mk a b =
      Localization.mk (q * a) b := by
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul]

lemma val_xUnit_pow (t : ℕ) :
    ((xUnit R hi ^ (t : ℤ) : (Localization.Away (prodX R I))ˣ) : Localization.Away (prodX R I)) =
      algebraMap (MvPolynomial (Fin (n + 1)) R) _ (X i ^ t) := by
  rw [zpow_natCast, Units.val_pow_eq_pow_val, val_xUnit, map_pow]

lemma mem_homogeneousSubmodule_iff_degree {d : ℕ} {p : MvPolynomial (Fin (n + 1)) R} :
    p ∈ 𝒜 d ↔ ∀ e, p.coeff e ≠ 0 → (e.degree : ℤ) = d := by
  rw [mem_homogeneousSubmodule]
  exact isHomogeneous_iff_forall_degree

/-- The elements `Xᵢᵏ · (p / X_Iᵐ)` with `p` homogeneous of degree `m · card I` are homogeneous of
degree `k`. -/
lemma xUnit_zpow_mul_mk_mem (k : ℤ) (m : ℕ) {p : MvPolynomial (Fin (n + 1)) R}
    (hp : p ∈ 𝒜 (m • I.card)) :
    ((xUnit R hi ^ k : (Localization.Away (prodX R I))ˣ) : Localization.Away (prodX R I)) *
      Localization.mk p (powX R I m) ∈ awayDegree R I k := by
  have hc := card_erase_add_one hi
  obtain ⟨t, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [val_xUnit_pow, algebraMap_mul_mk, mem_awayDegree_iff]
    refine ⟨m, _, fun e he ↦ ?_, rfl⟩
    have hXt : X i ^ t ∈ 𝒜 t := by
      simpa using SetLike.pow_mem_graded t (X_mem_homogeneousSubmodule_one (R := R) i)
    have hq : X i ^ t * p ∈ 𝒜 (t + m • I.card) := SetLike.mul_mem_graded hXt hp
    rw [mem_homogeneousSubmodule_iff_degree.mp hq e he]
    simp only [smul_eq_mul]
    push_cast
    ring
  · have hg := prod_X_mem_homogeneousSubmodule (R := R) (I.erase i)
    have hq : prodX R (I.erase i) ^ t * p ∈ 𝒜 (t • (I.erase i).card + m • I.card) :=
      SetLike.mul_mem_graded (SetLike.pow_mem_graded t hg) hp
    have key : ((xUnit R hi ^ (-(t : ℤ)) : (Localization.Away (prodX R I))ˣ) :
        Localization.Away (prodX R I)) * Localization.mk p (powX R I m) =
        Localization.mk (prodX R (I.erase i) ^ t * p) (powX R I (m + t)) := by
      rw [zpow_neg, Units.inv_mul_eq_iff_eq_mul, val_xUnit_pow, algebraMap_mul_mk]
      apply mk_eq_mk_of
      simp only [val_powX]
      rw [prodX_eq hi]
      ring
    rw [key, mem_awayDegree_iff]
    refine ⟨m + t, _, fun e he ↦ ?_, rfl⟩
    rw [mem_homogeneousSubmodule_iff_degree.mp hq e he]
    simp only [smul_eq_mul]
    push_cast
    rw [← hc]
    push_cast
    ring

/-- Conversely, every homogeneous element of degree `k` of `A[1 / X_I]` is `Xᵢᵏ · a` for some
`a ∈ A_(X_I)`. -/
lemma exists_xUnit_zpow_mul_val_eq (k : ℤ) {y : Localization.Away (prodX R I)}
    (hy : y ∈ awayDegree R I k) :
    ∃ a : Away 𝒜 (prodX R I), ((xUnit R hi ^ k : (Localization.Away (prodX R I))ˣ) :
      Localization.Away (prodX R I)) * a.val = y := by
  have hc := card_erase_add_one hi
  obtain ⟨m, p, hp, rfl⟩ := (mem_awayDegree_iff y).mp hy
  by_cases h0 : p = 0
  · exact ⟨0, by simp [h0, Localization.mk_zero]⟩
  obtain ⟨e₀, he₀⟩ := MvPolynomial.ne_zero_iff.mp h0
  have hd := hp e₀ he₀
  have hX := prod_X_mem_homogeneousSubmodule (R := R) I
  obtain ⟨t, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · have hg := prod_X_mem_homogeneousSubmodule (R := R) (I.erase i)
    have hpd : p ∈ 𝒜 (t + m * I.card) := mem_homogeneousSubmodule_iff_degree.mpr fun e he ↦ by
      rw [hp e he]
      push_cast
      ring
    have hq : p * prodX R (I.erase i) ^ t ∈ 𝒜 ((m + t) • I.card) := by
      have := SetLike.mul_mem_graded hpd (SetLike.pow_mem_graded t hg)
      convert this using 2
      rw [smul_eq_mul, smul_eq_mul, ← hc]
      ring
    refine ⟨Away.mk 𝒜 hX (m + t) _ hq, ?_⟩
    rw [Away.val_mk, val_xUnit_pow, algebraMap_mul_mk]
    apply mk_eq_mk_of
    have hx := prodX_eq (R := R) hi
    simp only [prodX] at hx ⊢
    rw [hx]
    ring
  · have hpd : p ∈ 𝒜 (m * I.card - t) := mem_homogeneousSubmodule_iff_degree.mpr fun e he ↦ by
      rw [hp e he]
      have : (0 : ℤ) ≤ e₀.degree := Int.natCast_nonneg _
      omega
    have hq : X i ^ t * p ∈ 𝒜 (m • I.card) := by
      have hXt : X i ^ t ∈ 𝒜 t := by
        simpa using SetLike.pow_mem_graded t (X_mem_homogeneousSubmodule_one (R := R) i)
      have := SetLike.mul_mem_graded hXt hpd
      convert this using 2
      have : (0 : ℤ) ≤ e₀.degree := Int.natCast_nonneg _
      rw [smul_eq_mul]
      omega
    refine ⟨Away.mk 𝒜 hX m _ hq, ?_⟩
    rw [Away.val_mk, zpow_neg, Units.inv_mul_eq_iff_eq_mul, val_xUnit_pow, algebraMap_mul_mk]

end Algebra

variable (k : ℤ)

/-- The section of `O(k)` over `UI I` as an element of `A[1 / X_I]`, computed in the chart
`i ∈ I`: `s ↦ Xᵢᵏ · sᵢ`. It does not depend on `i` (`sectionsUIAux_eq`). -/
noncomputable def sectionsUIAux (hI : I.Nonempty) {i : Fin (n + 1)} (hi : i ∈ I)
    (s : Γ(twistingSheaf n R k, UI n R I)) : Localization.Away (prodX R I) :=
  ((xUnit R hi ^ k : (Localization.Away (prodX R I))ˣ) : Localization.Away (prodX R I)) *
    toAway I hI (unitSectionsEquiv _ _ (twistSectionsEquiv (cocycle n R ^ k) i (UI_le_U hi) s))

lemma sectionsUIAux_eq (hI : I.Nonempty) {i j : Fin (n + 1)} (hi : i ∈ I) (hj : j ∈ I)
    (s : Γ(twistingSheaf n R k, UI n R I)) :
    sectionsUIAux k hI hi s = sectionsUIAux k hI hj s := by
  have h : UI n R I ≤ U n R i ⊓ U n R j := le_inf (UI_le_U hi) (UI_le_U hj)
  unfold sectionsUIAux
  rw [twistSectionsEquiv_change (cocycle n R ^ k) i (UI_le_U hi) j (UI_le_U hj) s,
    cocycle_zpow_g_res k i j _ h]
  change _ * toAway I hI (_ * _) = _
  rw [map_mul, ← mul_assoc]
  congr 1
  have e : toAway I hI ((xDivUnit i j (UI n R I) h ^ k : Γ(ℙₒ(n; R), UI n R I)ˣ) :
      Γ(ℙₒ(n; R), UI n R I)) =
      ((Units.map (toAway I hI).toMonoidHom (xDivUnit i j (UI n R I) h) ^ k :
        (Localization.Away (prodX R I))ˣ) : Localization.Away (prodX R I)) := by
    rw [← map_zpow]
    rfl
  rw [e, units_map_toAway_xDivUnit hI hi hj h, ← Units.val_mul, mul_zpow, inv_zpow,
    mul_left_comm, mul_inv_cancel, mul_one]

variable (I) in
/-- **Sections of `O(k)` over `UI I = D₊(X_I)` as elements of `A[1 / X_I]`**: `s ↦ Xᵢᵏ · sᵢ` for
any `i ∈ I` (`sectionsUI_eq`), where `sᵢ ∈ Γ(𝒪, UI I) ≅ A_(X_I)` is the `i`-th component. -/
noncomputable def sectionsUI (hI : I.Nonempty) :
    Γ(twistingSheaf n R k, UI n R I) →+ Localization.Away (prodX R I) where
  toFun := sectionsUIAux k hI (I.min'_mem hI)
  map_zero' := by
    rw [sectionsUIAux, LinearEquiv.map_zero, LinearEquiv.map_zero, map_zero, mul_zero]
  map_add' s t := by
    rw [sectionsUIAux, sectionsUIAux, sectionsUIAux, LinearEquiv.map_add, LinearEquiv.map_add,
      map_add, mul_add]

lemma sectionsUI_eq (hI : I.Nonempty) {i : Fin (n + 1)} (hi : i ∈ I)
    (s : Γ(twistingSheaf n R k, UI n R I)) :
    sectionsUI I k hI s = ((xUnit R hi ^ k : (Localization.Away (prodX R I))ˣ) :
      Localization.Away (prodX R I)) *
        toAway I hI (unitSectionsEquiv _ _
          (twistSectionsEquiv (cocycle n R ^ k) i (UI_le_U hi) s)) :=
  sectionsUIAux_eq k hI (I.min'_mem hI) hi s

lemma sectionsUI_injective (hI : I.Nonempty) :
    Function.Injective (sectionsUI (R := R) I k hI) := by
  intro s t h
  rw [sectionsUI_eq k hI (I.min'_mem hI), sectionsUI_eq k hI (I.min'_mem hI)] at h
  exact (twistSectionsEquiv _ _ _).injective ((unitSectionsEquiv _ _).injective
    (toAway_injective hI ((Units.mul_right_inj _).mp h)))

lemma sectionsUI_smul (hI : I.Nonempty) (r : Γ(ℙₒ(n; R), UI n R I))
    (s : Γ(twistingSheaf n R k, UI n R I)) :
    sectionsUI I k hI (r • s) = toAway I hI r * sectionsUI I k hI s := by
  rw [sectionsUI_eq k hI (I.min'_mem hI), sectionsUI_eq k hI (I.min'_mem hI),
    LinearEquiv.map_smul, LinearEquiv.map_smul, smul_eq_mul, map_mul, mul_left_comm]

section Restriction

variable {J : Finset (Fin (n + 1))} (hIJ : I ⊆ J)
include hIJ

lemma UI_antitone : UI n R J ≤ UI n R I := by
  rw [UI_eq_iInf, UI_eq_iInf]
  exact iInf₂_mono' fun j hj ↦ ⟨j, hIJ hj, le_rfl⟩

lemma toAway_res (hI : I.Nonempty) (r : Γ(ℙₒ(n; R), UI n R I)) :
    toAway J (hI.mono hIJ) (TopCat.Presheaf.restrictOpen r (UI n R J) (UI_antitone hIJ)) =
      awayRestr R hIJ (toAway I hI r) := by
  obtain ⟨a, rfl⟩ := (sectionsUIRingEquiv I hI).symm.surjective r
  have hx : prodX R J = prodX R I * prodX R (J \ I) :=
    by rw [mul_comm]; exact (Finset.prod_sdiff hIJ).symm
  have hg := prod_X_mem_homogeneousSubmodule (R := R) (J \ I)
  have := congr($(Proj.awayMap_awayToSection 𝒜 hg hx) a)
  rw [sectionsUIRingEquiv_symm_apply, toAway_awayToSection]
  refine ((congrArg (toAway J (hI.mono hIJ)) this.symm).trans ?_)
  erw [toAway_awayToSection]
  exact val_awayMap 𝒜 hg hx a

lemma awayRestr_algebraMap (p : MvPolynomial (Fin (n + 1)) R) :
    awayRestr R hIJ (algebraMap _ _ p) = algebraMap _ _ p :=
  IsLocalization.Away.lift_eq _ (isUnit_algebraMap_prod_X hIJ) p

lemma units_map_awayRestr_xUnit {i : Fin (n + 1)} (hi : i ∈ I) :
    Units.map (awayRestr R hIJ).toMonoidHom (xUnit R hi) = xUnit R (hIJ hi) := by
  ext
  exact awayRestr_algebraMap hIJ (X i)

/-- **Restriction of sections of `O(k)` from `UI I` to `UI J`** (`I ⊆ J`) is the localisation map
`A[1 / X_I] → A[1 / X_J]`. -/
lemma sectionsUI_res (hI : I.Nonempty) (s : Γ(twistingSheaf n R k, UI n R I)) :
    sectionsUI J k (hI.mono hIJ) (TopCat.Presheaf.restrictOpen s (UI n R J) (UI_antitone hIJ)) =
      awayRestr R hIJ (sectionsUI I k hI s) := by
  have hi := I.min'_mem hI
  rw [sectionsUI_eq k (hI.mono hIJ) (hIJ hi), sectionsUI_eq k hI hi, map_mul,
    twistSectionsEquiv_res _ _ (UI_le_U hi) (UI_antitone hIJ), unitSectionsEquiv_res,
    toAway_res hIJ hI]
  congr 1
  rw [← units_map_awayRestr_xUnit hIJ hi, ← map_zpow]
  rfl

end Restriction

lemma sectionsUI_mem (hI : I.Nonempty) (s : Γ(twistingSheaf n R k, UI n R I)) :
    sectionsUI I k hI s ∈ awayDegree R I k := by
  have hi := I.min'_mem hI
  rw [sectionsUI_eq k hI hi]
  obtain ⟨m, p, hp, hr⟩ := Away.mk_surjective 𝒜 (prod_X_mem_homogeneousSubmodule (R := R) I)
    (sectionsUIRingEquiv I hI (unitSectionsEquiv _ _
      (twistSectionsEquiv (cocycle n R ^ k) _ (UI_le_U hi) s)))
  have : toAway I hI (unitSectionsEquiv _ _
      (twistSectionsEquiv (cocycle n R ^ k) _ (UI_le_U hi) s)) =
      Localization.mk p (powX R I m) := by
    rw [toAway, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ← hr]
    rfl
  rw [this]
  exact xUnit_zpow_mul_mk_mem hi k m hp

lemma sectionsUI_surjective (hI : I.Nonempty) {y : Localization.Away (prodX R I)}
    (hy : y ∈ awayDegree R I k) : ∃ s, sectionsUI I k hI s = y := by
  have hi := I.min'_mem hI
  obtain ⟨a, ha⟩ := exists_xUnit_zpow_mul_val_eq hi k hy
  refine ⟨(twistSectionsEquiv (cocycle n R ^ k) _ (UI_le_U hi)).symm
    ((unitSectionsEquiv _ _).symm ((sectionsUIRingEquiv I hI).symm a)), ?_⟩
  rw [sectionsUI_eq k hI hi, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, ← ha]
  congr 1
  simp [toAway]

variable (I) in
/-- **Sections of `O(k)` over `UI I = D₊(X_I)`** (`I` nonempty): they are the homogeneous
elements of degree `k` of `A[1 / X_I]`, `A = R[X₀, …, Xₙ]`, via `s ↦ Xᵢᵏ · sᵢ` for any `i ∈ I`
(`sectionsUIEquiv_apply`). Restrictions correspond to localisation maps
(`sectionsUIEquiv_res`). -/
noncomputable def sectionsUIEquiv (hI : I.Nonempty) :
    Γ(twistingSheaf n R k, UI n R I) ≃+ awayDegree R I k :=
  AddEquiv.ofBijective ((sectionsUI I k hI).codRestrict _ (sectionsUI_mem k hI))
    ⟨fun _ _ h ↦ sectionsUI_injective k hI (congrArg Subtype.val h), fun y ↦
      (sectionsUI_surjective k hI y.2).imp fun _ h ↦ Subtype.ext h⟩

lemma sectionsUIEquiv_apply (hI : I.Nonempty) {i : Fin (n + 1)} (hi : i ∈ I)
    (s : Γ(twistingSheaf n R k, UI n R I)) :
    (sectionsUIEquiv I k hI s : Localization.Away (prodX R I)) =
      ((xUnit R hi ^ k : (Localization.Away (prodX R I))ˣ) : Localization.Away (prodX R I)) *
        toAway I hI (unitSectionsEquiv _ _
          (twistSectionsEquiv (cocycle n R ^ k) i (UI_le_U hi) s)) :=
  sectionsUI_eq k hI hi s

lemma sectionsUIEquiv_smul (hI : I.Nonempty) (r : Γ(ℙₒ(n; R), UI n R I))
    (s : Γ(twistingSheaf n R k, UI n R I)) :
    (sectionsUIEquiv I k hI (r • s) : Localization.Away (prodX R I)) =
      toAway I hI r * sectionsUIEquiv I k hI s :=
  sectionsUI_smul k hI r s

/-- **Restriction of sections of `O(k)`** from `UI I` to `UI J` (`I ⊆ J`) is the localisation map
`A[1 / X_I] → A[1 / X_J]`. -/
lemma sectionsUIEquiv_res {J : Finset (Fin (n + 1))} (hIJ : I ⊆ J) (hI : I.Nonempty)
    (s : Γ(twistingSheaf n R k, UI n R I)) :
    (sectionsUIEquiv J k (hI.mono hIJ)
        (TopCat.Presheaf.restrictOpen s (UI n R J) (UI_antitone hIJ)) :
          Localization.Away (prodX R J)) =
      awayRestr R hIJ (sectionsUIEquiv I k hI s) :=
  sectionsUI_res k hIJ hI s

end UI

section Global

variable (k : ℤ)

lemma UI_pair (i j : Fin (n + 1)) : UI n R {i, j} = UI n R {i} ⊓ UI n R {j} := by
  rw [UI_eq_iInf, UI_singleton, UI_singleton, Finset.iInf_insert, Finset.iInf_singleton]

lemma iSup_UI_singleton : ⨆ i : Fin (n + 1), UI n R {i} = ⊤ := by
  simp_rw [UI_singleton]
  exact iSup_U n R

/-- The Laurent coefficients of a global section of `O(k)`, computed on the chart `Uᵢ`; they do
not depend on `i` (`globalCoeff_eq`). -/
noncomputable def globalCoeff (i : Fin (n + 1)) :
    Γ(twistingSheaf n R k, ⊤) →+ ((Fin (n + 1) →₀ ℤ) →₀ R) where
  toFun s := awayCoeff R {i} (sectionsUIEquiv {i} k (Finset.singleton_nonempty i)
    (TopCat.Presheaf.restrictOpen s (UI n R {i}) le_top))
  map_zero' := by rw [mres_zero, map_zero, ZeroMemClass.coe_zero, map_zero]
  map_add' s t := by rw [mres_add, map_add, AddMemClass.coe_add, map_add]

lemma globalCoeff_eq_of_mem (i : Fin (n + 1)) (J : Finset (Fin (n + 1))) (hi : i ∈ J)
    (s : Γ(twistingSheaf n R k, ⊤)) :
    globalCoeff k i s = awayCoeff R J (sectionsUIEquiv J k ⟨i, hi⟩
      (TopCat.Presheaf.restrictOpen s (UI n R J) le_top)) := by
  have h : ({i} : Finset (Fin (n + 1))) ⊆ J := Finset.singleton_subset_iff.mpr hi
  change awayCoeff R {i} _ = _
  rw [← awayCoeff_awayRestr h, ← sectionsUIEquiv_res k h, mres_res]

lemma globalCoeff_eq (i j : Fin (n + 1)) (s : Γ(twistingSheaf n R k, ⊤)) :
    globalCoeff k i s = globalCoeff k j s := by
  rw [globalCoeff_eq_of_mem k i {i, j} (by simp), globalCoeff_eq_of_mem k j {i, j} (by simp)]

lemma globalCoeff_mem_laurentPart_singleton (i : Fin (n + 1)) (s : Γ(twistingSheaf n R k, ⊤)) :
    globalCoeff k i s ∈ laurentPart R {i} k :=
  (awayCoeff_mem_laurentPart_iff _).mpr (Subtype.property _)

lemma globalCoeff_mem_laurentPart (hn : 1 ≤ n) (s : Γ(twistingSheaf n R k, ⊤)) :
    globalCoeff k 0 s ∈ laurentPart R ∅ k := by
  rw [mem_laurentPart]
  intro a ha
  have h₀ := mem_laurentPart.mp (globalCoeff_mem_laurentPart_singleton k 0 s) a ha
  rw [globalCoeff_eq k 0 (Fin.last n)] at ha
  have h₁ := mem_laurentPart.mp (globalCoeff_mem_laurentPart_singleton k (Fin.last n) s) a ha
  refine ⟨fun j hj ↦ ?_, h₀.2⟩
  have e₀ := Finset.mem_singleton.mp (h₀.1 hj)
  have e₁ := Finset.mem_singleton.mp (h₁.1 hj)
  have := congrArg Fin.val (e₀.symm.trans e₁)
  simp only [Fin.val_zero, Fin.val_last] at this
  omega

lemma globalCoeff_injective (i : Fin (n + 1)) :
    Function.Injective (globalCoeff (R := R) k i) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  have h (j : Fin (n + 1)) : TopCat.Presheaf.restrictOpen s (UI n R {j}) le_top = 0 := by
    rw [globalCoeff_eq k i j] at hs
    apply (sectionsUIEquiv {j} k (Finset.singleton_nonempty j)).injective
    rw [map_zero]
    exact Subtype.ext (awayCoeff_injective _ (hs.trans (map_zero _).symm))
  refine mres_eq_of_locally_eq _ (fun j ↦ UI n R {j}) iSup_UI_singleton.ge (fun _ ↦ le_top) s 0
    fun j ↦ ?_
  rw [h j, mres_zero]

/-- **`O(k)` has no nonzero global sections for `k < 0`** (`n ≥ 1`). -/
lemma globalSections_eq_zero (hn : 1 ≤ n) (hk : k < 0) (s : Γ(twistingSheaf n R k, ⊤)) :
    s = 0 := by
  refine globalCoeff_injective k 0 ?_
  rw [map_zero]
  ext a
  by_contra ha
  obtain ⟨h₁, h₂⟩ := mem_laurentPart.mp (globalCoeff_mem_laurentPart k hn s) a ha
  have : 0 ≤ a.degree := by
    rw [Finsupp.degree]
    refine Finset.sum_nonneg fun j _ ↦ not_lt.mp fun hj ↦ ?_
    simpa using h₁ (mem_negSupp.mpr hj)
  omega

variable (R) in
/-- The Laurent coefficients of a polynomial, as an additive map on `A_k`. -/
noncomputable def polyCoeff (d : ℕ) : 𝒜 d →+ ((Fin (n + 1) →₀ ℤ) →₀ R) :=
  (AddMonoidAlgebra.coeffAddEquiv (R := R) (M := Fin (n + 1) →₀ ℤ)).toAddMonoidHom.comp
    ((toLaurent (Fin (n + 1)) R).toRingHom.toAddMonoidHom.comp (𝒜 d).subtype.toAddMonoidHom)

lemma polyCoeff_apply (d : ℕ) (p : 𝒜 d) :
    polyCoeff R d p = (toLaurent (Fin (n + 1)) R p).coeff :=
  rfl

lemma polyCoeff_injective (d : ℕ) : Function.Injective (polyCoeff (n := n) R d) :=
  fun _ _ h ↦ Subtype.ext (toLaurent_injective ((AddMonoidAlgebra.coeffAddEquiv).injective h))

/-- The global section of `O(d)` defined by a homogeneous polynomial `p` of degree `d`: on the
chart `Uᵢ` it is `p / Xᵢᵈ`. -/
lemma exists_globalSection (d : ℕ) (p : 𝒜 d) :
    ∃ s : Γ(twistingSheaf n R d, ⊤), ∀ i : Fin (n + 1),
      (sectionsUIEquiv {i} d (Finset.singleton_nonempty i)
        (TopCat.Presheaf.restrictOpen s (UI n R {i}) le_top) : Localization.Away (prodX R {i})) =
        algebraMap _ _ (p : MvPolynomial (Fin (n + 1)) R) := by
  have hp : (p : MvPolynomial (Fin (n + 1)) R).IsHomogeneous d := p.2
  let t (i : Fin (n + 1)) : Γ(twistingSheaf n R d, UI n R {i}) :=
    (sectionsUIEquiv {i} d (Finset.singleton_nonempty i)).symm
      ⟨_, algebraMap_mem_awayDegree {i} hp⟩
  have ht (i : Fin (n + 1)) : (sectionsUIEquiv {i} d (Finset.singleton_nonempty i) (t i) :
      Localization.Away (prodX R {i})) = algebraMap _ _ (p : MvPolynomial (Fin (n + 1)) R) := by
    simp [t]
  have key (i j : Fin (n + 1)) : TopCat.Presheaf.restrictOpen (t i) (UI n R {i, j})
      (UI_antitone (by simp)) = TopCat.Presheaf.restrictOpen (t j) (UI n R {i, j})
      (UI_antitone (by simp)) := by
    apply (sectionsUIEquiv {i, j} d ⟨i, by simp⟩).injective
    apply Subtype.ext
    rw [sectionsUIEquiv_res d (by simp : ({i} : Finset _) ⊆ {i, j}) (Finset.singleton_nonempty i),
      sectionsUIEquiv_res d (by simp : ({j} : Finset _) ⊆ {i, j}) (Finset.singleton_nonempty j),
      ht, ht,
      awayRestr_algebraMap, awayRestr_algebraMap]
  obtain ⟨s, hs, -⟩ := mres_existsUnique_gluing (twistingSheaf n R d) (fun i ↦ UI n R {i})
    iSup_UI_singleton.ge (fun _ ↦ le_top) t fun i j ↦ by
      apply mres_injective_of_le _ (UI_pair (R := R) i j).le (UI_pair (R := R) i j).ge
      simp only [mres_res]
      exact key i j
  exact ⟨s, fun i ↦ by rw [hs i, ht]⟩

lemma range_globalCoeff (hn : 1 ≤ n) (d : ℕ) :
    (globalCoeff (R := R) (n := n) d 0).range = (polyCoeff R d).range := by
  ext F
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨p, hp, hpF⟩ := exists_toLaurent_coeff_eq _ (globalCoeff_mem_laurentPart d hn s)
    exact ⟨⟨p, hp⟩, hpF⟩
  · rintro ⟨p, rfl⟩
    obtain ⟨s, hs⟩ := exists_globalSection d p
    refine ⟨s, ?_⟩
    change awayCoeff R {0} _ = _
    rw [hs 0, awayCoeff_apply, awayToLaurent_algebraMap]
    rfl

/-- **Global sections of `O(d)`** on `ℙₒ(n; R)`, `n ≥ 1`: they are the homogeneous polynomials of
degree `d`; the section attached to `p` is `p / Xᵢᵈ` on the chart `Uᵢ`
(`globalSectionsEquiv_symm_apply`). -/
noncomputable def globalSectionsEquiv (hn : 1 ≤ n) (d : ℕ) :
    Γ(twistingSheaf n R d, ⊤) ≃+ 𝒜 d :=
  (AddMonoidHom.ofInjective (globalCoeff_injective (R := R) (n := n) d 0)).trans
    ((AddEquiv.addSubgroupCongr (range_globalCoeff hn d)).trans
      (AddMonoidHom.ofInjective (polyCoeff_injective (n := n) (R := R) d)).symm)

lemma globalCoeff_globalSectionsEquiv_symm (hn : 1 ≤ n) (d : ℕ) (p : 𝒜 d) :
    globalCoeff d 0 ((globalSectionsEquiv (R := R) hn d).symm p) = polyCoeff R d p := by
  unfold globalSectionsEquiv
  rw [AddEquiv.symm_trans_apply, AddEquiv.symm_trans_apply, AddEquiv.symm_symm]
  set x := (AddEquiv.addSubgroupCongr (range_globalCoeff (R := R) hn d)).symm
    (AddMonoidHom.ofInjective (polyCoeff_injective (n := n) (R := R) d) p)
  have := congrArg Subtype.val
    ((AddMonoidHom.ofInjective (globalCoeff_injective (R := R) (n := n) d 0)).apply_symm_apply x)
  rw [AddMonoidHom.ofInjective_apply] at this
  rw [this]
  rfl

lemma sectionsUIEquiv_globalSectionsEquiv_symm (hn : 1 ≤ n) (d : ℕ) (p : 𝒜 d)
    (i : Fin (n + 1)) :
    (sectionsUIEquiv {i} d (Finset.singleton_nonempty i)
      (TopCat.Presheaf.restrictOpen ((globalSectionsEquiv (R := R) hn d).symm p) (UI n R {i})
        le_top) : Localization.Away (prodX R {i})) =
      algebraMap _ _ (p : MvPolynomial (Fin (n + 1)) R) := by
  apply awayCoeff_injective {i}
  change globalCoeff d i _ = _
  rw [globalCoeff_eq d i 0, globalCoeff_globalSectionsEquiv_symm, polyCoeff_apply,
    awayCoeff_apply, awayToLaurent_algebraMap]

end Global

end AlgebraicGeometry.ProjectiveSpace

end
