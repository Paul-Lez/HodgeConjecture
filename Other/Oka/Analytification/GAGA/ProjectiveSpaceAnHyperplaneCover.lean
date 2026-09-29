/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.ProjectiveSpaceGAGA3
public import Other.Oka.Analytification.GAGA.TwistTransition
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.LinearSubst

/-!
# The translates of the hyperplane cover `ℙⁿ⁺¹_an`

Every point `[v]` of `ℙⁿ⁺¹_an` lies on the image of the hyperplane `ℙⁿ_an = {Xₙ₊₁ = 0}` under the
analytification of an automorphism of `ℙⁿ⁺¹` induced by a linear substitution
(`ComplexAnalytic.projectiveSpaceAn.hyperplaneTranslatesCover`): if `vₖ ≠ 0` for some `k ≤ n` use
the shear `Xₙ₊₁ ↦ Xₙ₊₁ - (vₙ₊₁ / vₖ) Xₖ`, otherwise `[v] = [0 : ⋯ : 0 : 1]` and we use the swap
`X₀ ↔ Xₙ₊₁`.

The criterion (`mem_range_of_linearSubst`): for an automorphism `g` induced by a linear
substitution `ψ` with `ψ Xₖ = Xⱼ`, `vⱼ ≠ 0` and `(ψ Xₙ₊₁)(v) = 0`, the point `(g^an)⁻¹ [v]` lies on
the hyperplane. Indeed its image in `ℙⁿ⁺¹` lies in `Uₖ`, and the germ there of the local equation
`Xₙ₊₁ / Xₖ` of the hyperplane pulls back along `g⁻¹` to `ψ(Xₙ₊₁) / Xⱼ`, which vanishes at `[v]`;
off the hyperplane its germ would be a unit.

Consequently, GAGA-3 on `ℙⁿ` holds given only finite-dimensionality of `H¹` of coherent sheaves
(`ComplexAnalytic.gaga₃_projectiveSpace`).
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpace

universe u

noncomputable section

namespace ComplexAnalytic.projectiveSpaceAn

attribute [local instance] MvPolynomial.gradedAlgebra

variable {N : ℕ}

/-- The automorphism of `ℙᴺ` over `ℂ` induced by a linear substitution `ψ`; its inverse pulls
`Xᵢ` back to `ψ Xᵢ`. -/
def linearSubstAut (ψ : MvPolynomial (Fin (N + 1)) (ULift.{u} ℂ) ≃ₐ[ULift.{u} ℂ]
      MvPolynomial (Fin (N + 1)) (ULift.{u} ℂ))
    (hψ : IsLinearSubst ψ.toAlgHom) (hψ' : IsLinearSubst ψ.symm.toAlgHom) :
    projectiveSpace.{u} N ≅ projectiveSpace.{u} N :=
  (ObjectProperty.fullyFaithfulι _).preimageIso (Over.isoMk (linearSubstIso ψ hψ hψ')
    (linearSubstMap_toSpec ψ.symm hψ' (by simpa using hψ)))

lemma linearSubstAut_inv_hom_left (ψ : MvPolynomial (Fin (N + 1)) (ULift.{u} ℂ) ≃ₐ[ULift.{u} ℂ]
      MvPolynomial (Fin (N + 1)) (ULift.{u} ℂ))
    (hψ : IsLinearSubst ψ.toAlgHom) (hψ' : IsLinearSubst ψ.symm.toAlgHom) :
    (linearSubstAut ψ hψ hψ').inv.hom.left = linearSubstMap ψ hψ :=
  rfl

/-- The value at `v` of `p / Xⱼ` is `p(v) / vⱼ`. -/
lemma awayEval_mk_X (v : Fin (N + 1) → ℂ) (j : Fin (N + 1)) (hj : eval₂ φ.{u} v (X j) ≠ 0)
    (p : MvPolynomial (Fin (N + 1)) (ULift.{u} ℂ))
    (hp : p ∈ homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℂ) (1 • 1)) :
    awayEval (φ := φ.{u}) v (X j) hj (Away.mk (homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℂ))
      (X_mem_homogeneousSubmodule_one j) 1 p hp) =
      eval₂ φ.{u} v p / v j := by
  have hj' : v j ≠ 0 := by simpa using hj
  have hv : eval₂Hom φ.{u} v (X j) * (v j)⁻¹ = 1 := by
    simp [hj']
  simp only [awayEval, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  rw [Localization.awayLift_mk (v := (v j)⁻¹) (hv := hv)]
  simp [div_eq_mul_inv]

variable {n : ℕ}

/-- **A criterion for lying on the hyperplane**: a point of `ℙⁿ⁺¹_an` over `Uₖ` at which the germ
of `Xₙ₊₁ / Xₖ` is not a unit lies on the hyperplane `ℙⁿ_an`. -/
theorem mem_range_hyperplaneLRS_of_not_isUnit (z : projectiveSpaceAn.{u} (n + 1))
    (k : Fin (n + 1 + 1)) (hz : (πLRS (n + 1)).base z ∈ U (n + 1) (ULift.{u} ℂ) k)
    (h : ¬ IsUnit (ℙₒ(n + 1; ULift.{u} ℂ).presheaf.germ _ _ hz (xDiv k (Fin.last _)))) :
    z ∈ Set.range (hyperplaneLRS.{u} n).base := by
  by_contra hz'
  have htop := (hyperplaneLRS.{u} n).pushforwardStalkIdeal_eq_top
    isClosedEmbedding_hyperplaneLRS.isClosed_range z hz'
  rw [pushforwardStalkIdeal_eq k z hz, Ideal.span_singleton_eq_top] at htop
  haveI : IsLocalHom ((πLRS (n + 1)).stalkMap z).hom := (πLRS (n + 1)).prop z
  exact h ((isUnit_map_iff ((πLRS (n + 1)).stalkMap z).hom _).1 htop)

/-- **Points on translates of the hyperplane**: let `ψ` be a linear substitution with
`ψ Xₖ = Xⱼ`, and `v` with `vⱼ ≠ 0` and `(ψ Xₙ₊₁)(v) = 0`. Then `(g^an)⁻¹ [v]` lies on the
hyperplane, for the automorphism `g` induced by `ψ`. -/
theorem mem_range_of_linearSubst
    (ψ : MvPolynomial (Fin (n + 1 + 1)) (ULift.{u} ℂ) ≃ₐ[ULift.{u} ℂ]
      MvPolynomial (Fin (n + 1 + 1)) (ULift.{u} ℂ))
    (hψ : IsLinearSubst ψ.toAlgHom) (hψ' : IsLinearSubst ψ.symm.toAlgHom)
    (v : Fin (n + 1 + 1) → ℂ) (hv : v ≠ 0) {k j : Fin (n + 1 + 1)} (hkj : ψ (X k) = X j)
    (hj : v j ≠ 0) (h0 : eval₂ φ.{u} v (ψ (X (Fin.last _))) = 0) :
    (autAn (linearSubstAut ψ hψ hψ').symm).base (pointOfVec.{u} v hv) ∈
      Set.range (hyperplaneLRS.{u} n).base := by
  set y := pointOfVec.{u} v hv
  set f := linearSubstMap ψ hψ
  have hnat : (πLRS (n + 1)).base ((autAn (linearSubstAut ψ hψ hψ').symm).base y) =
      f.base ((πLRS (n + 1)).base y) :=
    congrArg (fun g ↦ g.base y) (analytificationπLRS_naturality (linearSubstAut ψ hψ hψ').inv)
  have hp : (πLRS (n + 1)).base y ∈ U (n + 1) (ULift.{u} ℂ) j := π_pointOfVec_mem_U v hv j hj
  have hpre := linearSubstMap_preimage_U ψ hψ hkj
  have hfp : f.base ((πLRS (n + 1)).base y) ∈ U (n + 1) (ULift.{u} ℂ) k := by
    have : (πLRS (n + 1)).base y ∈ f ⁻¹ᵁ U (n + 1) (ULift.{u} ℂ) k := by rw [hpre]; exact hp
    exact this
  refine mem_range_hyperplaneLRS_of_not_isUnit _ k (hnat ▸ hfp) ?_
  intro hu
  -- transport the unit along the stalk map of `f`
  have key : ∀ (q : ℙₒ(n + 1; ULift.{u} ℂ)) (hq : q ∈ U (n + 1) (ULift.{u} ℂ) k),
      q = f.base ((πLRS (n + 1)).base y) →
      IsUnit (ℙₒ(n + 1; ULift.{u} ℂ).presheaf.germ _ q hq (xDiv k (Fin.last _))) →
      IsUnit (ℙₒ(n + 1; ULift.{u} ℂ).presheaf.germ _ _ hfp (xDiv k (Fin.last _))) := by
    rintro q hq rfl h
    exact h
  have hu' := key _ _ hnat hu
  have hu₂ := hu'.map (f.stalkMap ((πLRS (n + 1)).base y)).hom
  rw [Scheme.Hom.germ_stalkMap_apply] at hu₂
  have hres : ℙₒ(n + 1; ULift.{u} ℂ).presheaf.germ (f ⁻¹ᵁ U (n + 1) (ULift.{u} ℂ) k)
      ((πLRS (n + 1)).base y) hfp (f.app _ (xDiv k (Fin.last _))) =
      ℙₒ(n + 1; ULift.{u} ℂ).presheaf.germ (U (n + 1) (ULift.{u} ℂ) j) _ hp
        (f.appLE _ _ hpre.ge (xDiv k (Fin.last _))) :=
    (TopCat.Presheaf.germ_res_apply _ (homOfLE hpre.ge) _ hp _).symm
  rw [hres, linearSubstMap_appLE_xDiv ψ hψ hkj] at hu₂
  -- the germ is not a unit: its value at `[v]` is `(ψ Xₙ₊₁)(v) / vⱼ = 0`
  refine ((eval_c_app_eq_zero_iff (πLRS (n + 1)) y hp _).1 ?_) hu₂
  have hj' : eval₂ φ.{u} v (X j) ≠ 0 := by rwa [eval₂_φ_X]
  refine (eval_π_awayToSection v hv j hj _).trans ?_
  rw [awayEval_mk_X v j hj', h0, zero_div]

/-- **The translates of the hyperplane cover `ℙⁿ⁺¹_an`.** -/
theorem hyperplaneTranslatesCover (n : ℕ) : HyperplaneTranslatesCover.{u} n := by
  intro y
  obtain ⟨v, hv, rfl⟩ := pointOfVec_surjective y
  by_cases h : ∃ k : Fin (n + 1), v k.castSucc ≠ 0
  · obtain ⟨k, hk⟩ := h
    have hne : k.castSucc ≠ Fin.last (n + 1) := (Fin.castSucc_lt_last k).ne
    let c : ULift.{u} ℂ := ULift.up (-(v (Fin.last _) / v k.castSucc))
    let ψ := shearEquiv (ULift.{u} ℂ) hne c
    have hψ : IsLinearSubst ψ.toAlgHom := isLinearSubst_shearAlgHom _ _ c
    have hψ' : IsLinearSubst ψ.symm.toAlgHom := isLinearSubst_shearAlgHom _ _ (-c)
    refine ⟨linearSubstAut ψ hψ hψ', _, mem_range_of_linearSubst ψ hψ hψ' v hv
      (k := k.castSucc) (j := k.castSucc) (shearAlgHom_X_of_ne c hne) hk ?_,
      autAn_inv_base_autAn_base (linearSubstAut ψ hψ hψ').symm _⟩
    change eval₂ φ.{u} v (shearAlgHom (ULift.{u} ℂ) _ _ c (X (Fin.last _))) = 0
    rw [shearAlgHom_X_self]
    have : (ULift.ringEquiv c : ℂ) = -(v (Fin.last _) / v k.castSucc) := rfl
    simp only [eval₂_add, eval₂_mul, eval₂_X, eval₂_C, φ, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, this]
    field_simp
    ring
  · push Not at h
    have hlast : v (Fin.last (n + 1)) ≠ 0 := by
      intro h0
      refine hv (funext fun i ↦ ?_)
      induction i using Fin.lastCases with
      | last => exact h0
      | cast k => exact h k
    let ψ := renameEquiv (ULift.{u} ℂ) (Equiv.swap (0 : Fin (n + 1 + 1)) (Fin.last (n + 1)))
    have hψ : IsLinearSubst ψ.toAlgHom := isLinearSubst_renameEquiv _
    have hψ' : IsLinearSubst ψ.symm.toAlgHom := by
      simpa [ψ] using isLinearSubst_renameEquiv (R := ULift.{u} ℂ)
        (Equiv.swap (0 : Fin (n + 1 + 1)) (Fin.last (n + 1)))
    refine ⟨linearSubstAut ψ hψ hψ', _, mem_range_of_linearSubst ψ hψ hψ' v hv
      (k := 0) (j := Fin.last _) (by simp [ψ]) hlast ?_,
      autAn_inv_base_autAn_base (linearSubstAut ψ hψ hψ').symm _⟩
    simpa [ψ] using h 0

/-- **Serre's GAGA-3 on `ℙⁿ`, given Cartan–Serre**: if `H¹(ℙⁿ_an, M)` is finite-dimensional for
every `n` and every coherent analytic `M`, then every coherent analytic sheaf on `ℙⁿ_an` is
isomorphic to the analytification of a coherent algebraic sheaf on `ℙⁿ`. -/
theorem _root_.ComplexAnalytic.gaga₃_projectiveSpace
    (hFin : ∀ (n : ℕ)
      (M : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf),
      M.IsCoherent → FiniteDimensional ℂ (LocallyRingedSpace.H M 1)) (n : ℕ)
    (M : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf)
    (hM : M.IsCoherent) :
    ∃ F : SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf,
      F.IsCoherent ∧ Nonempty ((analytificationModules (projectiveSpace.{u} n)).obj F ≅ M) :=
  gaga₃_of_hyperplaneTranslatesCover hFin hyperplaneTranslatesCover n M hM

end ComplexAnalytic.projectiveSpaceAn

end
