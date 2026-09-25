/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.PointJetDerivation
public import Other.AlgebraicGeometry.CartierLocalForm
public import Other.AlgebraicGeometry.Smooth.RegularLocal
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.PointwiseDimension
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Point-jet detection at a smooth complex point

The localized analytic first jet detects every algebraic germ outside the square of the
maximal ideal.  The proof identifies the residue field with `ℂ`, transfers the regular-local
cotangent dimension across that equivalence, and applies the cotangent detection lemma.
-/

@[expose] public noncomputable section
open CategoryTheory Topology TopologicalSpace Opposite
open IsLocalRing
open scoped Manifold
namespace AlgebraicGeometry.ComplexPoint.Affine
open AlgebraicGeometry.ComplexPoint Point
variable (X : Over (Spec ↧ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]
variable {x : X.left} (D : LocalEtaleCoordinates X d x)

noncomputable local instance : Algebra ℂ (localSectionRing X d D) :=
  (D.coordinateRingHomOnOpen.comp MvPolynomial.C).toAlgebra

private lemma pointJet_basis (v : PointJet d) :
    v = ∑ i : Fin d, v (Pi.single i (1 : ℂ)) • ContinuousLinearMap.proj i := by
  ext w
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hw : w = ∑ i : Fin d, w i • Pi.single i (1 : ℂ) := by
    ext j
    calc
      w j = ∑ i, (Pi.single i (w i) : Fin d → ℂ) j :=
        (Fintype.sum_pi_single j w).symm
      _ = ∑ i, w i * (Pi.single i (1 : ℂ) : Fin d → ℂ) j := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases h : i = j <;> simp [h]
      _ = (∑ i, w i • Pi.single i (1 : ℂ)) j := by
        simp [Finset.sum_apply, smul_eq_mul]
  conv_lhs => rw [hw]
  rw [map_sum]
  simp [smul_eq_mul, mul_comm]

private lemma coordinate_standardSmooth {x : X.left} (D : LocalEtaleCoordinates X d x) :
    (algebraMap ℂ (localSectionRing X d D)).IsStandardSmoothOfRelativeDimension d := by
  let hcoord0 : D.coordinateRingHomOnOpen.IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.mp
      D.coordinateRingHomOnOpen_etale
  have hcomposite :
      RingHom.IsStandardSmoothOfRelativeDimension d
        (D.coordinateRingHomOnOpen.comp MvPolynomial.C) := by
    simpa only [zero_add] using hcoord0.comp (by
      rw [show (MvPolynomial.C : ℂ →+* MvPolynomial (Fin d) ℂ) =
        algebraMap ℂ (MvPolynomial (Fin d) ℂ) from rfl]
      rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
      let P : Algebra.SubmersivePresentation ℂ (MvPolynomial (Fin d) ℂ)
          (Fin d) Empty :=
        { toPreSubmersivePresentation :=
            { toPresentation :=
                { toGenerators := Algebra.Generators.mvPolynomial ℂ (Fin d)
                  relation := Empty.elim
                  span_range_relation_eq_ker := by
                    rw [Algebra.Generators.ker_mvPolynomial]
                    simp }
              map := Empty.elim
              map_inj := fun a ↦ a.elim }
          jacobian_isUnit := by
            rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
              Matrix.det_isEmpty]
            simpa only [map_one] using
              (isUnit_one : IsUnit (1 : MvPolynomial (Fin d) ℂ)) }
      exact P.isStandardSmoothOfRelativeDimension (by
        simp [Algebra.Presentation.dimension]))
  change RingHom.IsStandardSmoothOfRelativeDimension d
    (D.coordinateRingHomOnOpen.comp MvPolynomial.C)
  exact hcomposite

theorem localizedPointJetDerivation_ne_zero_of_not_mem_square
    (z : ComplexPoint X) (hz : z.underlying ∈ D.neighborhood) :
    let q := RingHom.ker (residueAlgHom X d D z hz).toRingHom
    letI : q.IsPrime := RingHom.ker_isPrime (residueAlgHom X d D z hz).toRingHom
    IsRegularLocalRing (Localization.AtPrime q) →
    ringKrullDim (Localization.AtPrime q) = d →
    (∀ i : Fin d,
      localizedPointJetDerivation X d D z hz
        (algebraMap (localSectionRing X d D) (Localization.AtPrime q)
          (D.coordinateRingHomOnOpen (MvPolynomial.X i))) =
      ContinuousLinearMap.proj i) →
    ∀ (a : localSectionRing X d D),
      algebraMap (localSectionRing X d D) (Localization.AtPrime q) a ∈
        maximalIdeal (Localization.AtPrime q) →
      algebraMap (localSectionRing X d D) (Localization.AtPrime q) a ∉
        (maximalIdeal (Localization.AtPrime q)) ^ 2 →
      localizedPointJetDerivation X d D z hz
        (algebraMap (localSectionRing X d D) (Localization.AtPrime q) a) ≠ 0 := by
  dsimp
  let : (RingHom.ker (residueAlgHom X d D z hz).toRingHom).IsPrime :=
    RingHom.ker_isPrime (residueAlgHom X d D z hz).toRingHom
  change IsRegularLocalRing (Localization.AtPrime
      (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) →
      ringKrullDim (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) = d →
      (∀ i : Fin d,
        localizedPointJetDerivation X d D z hz
          (algebraMap (localSectionRing X d D) (Localization.AtPrime
            (RingHom.ker (residueAlgHom X d D z hz).toRingHom))
            (D.coordinateRingHomOnOpen (MvPolynomial.X i))) =
        ContinuousLinearMap.proj i) →
      ∀ (a : localSectionRing X d D),
        algebraMap (localSectionRing X d D) (Localization.AtPrime
          (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) a ∈
          maximalIdeal (Localization.AtPrime
            (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) →
        algebraMap (localSectionRing X d D) (Localization.AtPrime
          (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) a ∉
          (maximalIdeal (Localization.AtPrime
            (RingHom.ker (residueAlgHom X d D z hz).toRingHom))) ^ 2 →
        localizedPointJetDerivation X d D z hz
          (algebraMap (localSectionRing X d D) (Localization.AtPrime
            (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) a) ≠ 0
  intro hreg hdim hcoord a ha ha2
  let : IsRegularLocalRing (Localization.AtPrime
      (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) := hreg
  let : IsScalarTower ℂ (localSectionRing X d D)
      (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    change algebraMap ℂ (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) c =
      algebraMap (localSectionRing X d D) (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom))
        (D.coordinateRingHomOnOpen (MvPolynomial.C c))
    rfl
  let : IsCentralScalar ℂ (PointJet d) :=
    { op_smul_eq_smul := by
        intro c m
        ext i
        simp }
  let : CommRing (TrivSqZeroExt ℂ (PointJet d)) := inferInstance
  let : Algebra ℂ (TrivSqZeroExt ℂ (PointJet d)) := inferInstance
  let g := localizedPointJetAlgHom X d D z hz
  let u := (TrivSqZeroExt.fstHom ℂ ℂ (PointJet d)).comp g
  let : Module (Localization.AtPrime
      (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) (PointJet d) :=
    Module.compHom (PointJet d) u.toRingHom
  let : IsScalarTower ℂ (Localization.AtPrime
      (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) (PointJet d) := by
    constructor
    intro c r v
    change u (c • r) • v = c • u r • v
    rw [map_smul]
    simp only [smul_eq_mul, smul_smul]
  have hu : Function.Surjective u := by
    intro c
    refine ⟨algebraMap ℂ (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) c, ?_⟩
    exact u.commutes c
  have hker : RingHom.ker u.toRingHom = maximalIdeal (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) :=
    IsLocalRing.ker_eq_maximalIdeal u.toRingHom hu
  have htriv : ∀ r : Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom),
      r ∈ maximalIdeal (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) → ∀ v : PointJet d, r • v = 0 := by
    intro r hr v
    have hr0 : u r = 0 := by
      apply RingHom.mem_ker.mp
      have hr' : r ∈ RingHom.ker u.toRingHom := hker.symm ▸ hr
      exact RingHom.mem_ker.mp hr'
    change u r • v = 0
    rw [hr0]
    exact (zero_smul ℂ v)
  have hsurj : Function.Surjective
      (Derivation.cotangentMap (localizedPointJetDerivation X d D z hz) htriv) := by
    intro v
    let xi (i : Fin d) : Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom) :=
      algebraMap (localSectionRing X d D)
          (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom))
          (D.coordinateRingHomOnOpen (MvPolynomial.X i)) -
        algebraMap ℂ (Localization.AtPrime
          (RingHom.ker (residueAlgHom X d D z hz).toRingHom))
          (u (algebraMap (localSectionRing X d D)
            (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom))
            (D.coordinateRingHomOnOpen (MvPolynomial.X i))))
    have hxi (i : Fin d) : xi i ∈ maximalIdeal (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) := by
      rw [← hker]
      apply RingHom.mem_ker.mpr
      change u (_ - _) = 0
      rw [map_sub, u.commutes]
      simp
    have hδxi (i : Fin d) :
        localizedPointJetDerivation X d D z hz (xi i) =
          ContinuousLinearMap.proj i := by
      let A := algebraMap (localSectionRing X d D)
        (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom))
        (D.coordinateRingHomOnOpen (MvPolynomial.X i))
      let B := algebraMap ℂ (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) (u A)
      change localizedPointJetDerivation X d D z hz (A - B) = _
      have hsub := (localizedPointJetDerivation X d D z hz).map_sub A B
      rw [hsub, hcoord i, Derivation.map_algebraMap]
      simp
    refine ⟨∑ i : Fin d, v (Pi.single i (1 : ℂ)) •
      (maximalIdeal (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom))).toCotangent
          ⟨xi i, hxi i⟩, ?_⟩
    rw [map_sum]
    simp only [map_smul, Derivation.cotangentMap_toCotangent, hδxi]
    exact (pointJet_basis d v).symm
  let : IsScalarTower ℂ (IsLocalRing.ResidueField (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))
      (IsLocalRing.CotangentSpace (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom))) := by
    constructor
    intro c k v
    calc
      (c • k) • v = (algebraMap ℂ (IsLocalRing.ResidueField (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom))) c * k) • v := by rw [Algebra.smul_def]
      _ = algebraMap ℂ (IsLocalRing.ResidueField (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom))) c • (k • v) := by rw [mul_smul]
      _ = algebraMap (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) (IsLocalRing.ResidueField (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))
          (algebraMap ℂ (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) c) • (k • v) := by
        rw [IsScalarTower.algebraMap_apply ℂ (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom))
          (IsLocalRing.ResidueField (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))]
      _ = (algebraMap ℂ (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) c) • (k • v) := by
        rw [@IsScalarTower.algebraMap_smul (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom))
          (IsLocalRing.ResidueField (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))
          (IsLocalRing.CotangentSpace (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))
          _ _ _ _ _ _ (algebraMap ℂ (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) c) (k • v)]
      _ = c • (k • v) := by
        rw [@IsScalarTower.algebraMap_smul ℂ (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom))
          (IsLocalRing.CotangentSpace (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))
          _ _ _ _ _ _ c (k • v)]
  have he : IsLocalRing.ResidueField (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) ≃ₐ[ℂ] ℂ := by
    letI : IsLocalHom u.toRingHom := IsLocalHom.of_surjective u.toRingHom hu
    let e0 : IsLocalRing.ResidueField (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) →ₐ[ℂ] ℂ :=
      { __ := IsLocalRing.ResidueField.lift u.toRingHom
        commutes' := by
          intro c
          change IsLocalRing.ResidueField.lift u.toRingHom
            (IsLocalRing.residue (Localization.AtPrime
              (RingHom.ker (residueAlgHom X d D z hz).toRingHom))
              ((algebraMap ℂ (Localization.AtPrime
                (RingHom.ker (residueAlgHom X d D z hz).toRingHom))) c)) = _
          rw [IsLocalRing.ResidueField.lift_residue_apply]
          exact u.commutes c }
    have he0_inj : Function.Injective e0 := by
      intro aa bb hab
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective
        (R := Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) aa
      obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective
        (R := Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) bb
      have hrs : u r = u s := by
        change IsLocalRing.ResidueField.lift u.toRingHom
            (IsLocalRing.residue (Localization.AtPrime
              (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) r) =
          IsLocalRing.ResidueField.lift u.toRingHom
            (IsLocalRing.residue (Localization.AtPrime
              (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) s) at hab
        rw [IsLocalRing.ResidueField.lift_residue_apply,
          IsLocalRing.ResidueField.lift_residue_apply] at hab
        exact hab
      apply sub_eq_zero.mp
      rw [← map_sub]
      apply (IsLocalRing.residue_eq_zero_iff
        (R := Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom))
        (r - s)).mpr
      rw [← hker]
      apply RingHom.mem_ker.mpr
      rw [map_sub]
      exact sub_eq_zero.mpr hrs
    have he0_surj : Function.Surjective e0 := by
      intro c
      refine ⟨algebraMap ℂ (IsLocalRing.ResidueField (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom))) c, ?_⟩
      exact e0.commutes c
    exact AlgEquiv.ofBijective e0 ⟨he0_inj, he0_surj⟩
  have hfin : Module.finrank ℂ
      (IsLocalRing.CotangentSpace (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom))) = d := by
    have hκ := (IsRegularLocalRing.iff_finrank_cotangentSpace
      (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom))).mp hreg
    rw [hdim] at hκ
    let b := Module.Free.chooseBasis (IsLocalRing.ResidueField (Localization.AtPrime
      (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))
      (IsLocalRing.CotangentSpace (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))
    let hscalar : ∀ (c : IsLocalRing.ResidueField (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))
        (x : IsLocalRing.CotangentSpace (Localization.AtPrime
          (RingHom.ker (residueAlgHom X d D z hz).toRingHom))),
        he c • x = c • x := by
      intro c x
      rw [← @IsScalarTower.algebraMap_smul ℂ
        (IsLocalRing.ResidueField (Localization.AtPrime
          (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))
        (IsLocalRing.CotangentSpace (Localization.AtPrime
          (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))
        _ _ _ _ _ _ (he c) x]
      congr 1
      apply he.injective
      rw [he.commutes]
      simp
    let b' := b.mapCoeffs he.toRingEquiv hscalar
    let : FiniteDimensional ℂ (IsLocalRing.CotangentSpace (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom))) :=
      Module.Finite.of_basis b'
    calc
      Module.finrank ℂ (IsLocalRing.CotangentSpace (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom))) =
          Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime
            (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))
            (IsLocalRing.CotangentSpace (Localization.AtPrime
              (RingHom.ker (residueAlgHom X d D z hz).toRingHom))) := by
        rw [Module.finrank_eq_card_basis b', Module.finrank_eq_card_basis b]
      _ = d := by exact_mod_cast hκ
  let bκ := Module.Free.chooseBasis (IsLocalRing.ResidueField (Localization.AtPrime
    (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))
    (IsLocalRing.CotangentSpace (Localization.AtPrime
      (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))
  let hscalar : ∀ (c : IsLocalRing.ResidueField (Localization.AtPrime
      (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))
      (x : IsLocalRing.CotangentSpace (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom))),
      he c • x = c • x := by
    intro c x
    rw [← @IsScalarTower.algebraMap_smul ℂ
      (IsLocalRing.ResidueField (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))
      (IsLocalRing.CotangentSpace (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))
      _ _ _ _ _ _ (he c) x]
    congr 1
    apply he.injective
    rw [he.commutes]
    simp
  let bℂ := bκ.mapCoeffs he.toRingEquiv hscalar
  let : FiniteDimensional ℂ (IsLocalRing.CotangentSpace (Localization.AtPrime
      (RingHom.ker (residueAlgHom X d D z hz).toRingHom))) :=
    Module.Finite.of_basis bℂ
  exact Derivation.ne_zero_of_mem_maximalIdeal_of_not_mem_square
    (localizedPointJetDerivation X d D z hz) htriv hsurj (by
      rw [hfin]
      exact (by
        dsimp [PointJet]
        let e := (ContinuousLinearEquiv.piRing (𝕜 := ℂ) (E := ℂ) (Fin d)).toLinearEquiv
        rw [e.finrank_eq]
        exact (Module.finrank_fin_fun ℂ).symm)) _ ha ha2

noncomputable def residuePrimeIdeal (z : ComplexPoint X)
    (hz : z.underlying ∈ D.neighborhood) : Ideal (localSectionRing X d D) :=
  letI : IsAffine D.neighborhood.toScheme := D.isAffine
  let z' := (ComplexPoint.openHomeomorph X D.neighborhood).symm ⟨z, hz⟩
  let hU := isAffineOpen_top D.neighborhood.toScheme
  (hU.primeIdealOf ⟨z'.underlying, trivial⟩).asIdeal

theorem residueAlgHom_ker_eq_residuePrimeIdeal (z : ComplexPoint X)
    (hz : z.underlying ∈ D.neighborhood) :
    RingHom.ker (residueAlgHom X d D z hz).toRingHom = residuePrimeIdeal X d D z hz := by
  let z' := (ComplexPoint.openHomeomorph X D.neighborhood).symm ⟨z, hz⟩
  let : IsAffine D.neighborhood.toScheme := D.isAffine
  let hU := isAffineOpen_top D.neighborhood.toScheme
  let P := hU.primeIdealOf ⟨z'.underlying, trivial⟩
  let : P.asIdeal.IsPrime := P.isPrime
  have heq : RingHom.ker (residueAlgHom X d D z hz).toRingHom = P.asIdeal := by
    ext a
    change residueAlgHom X d D z hz a = 0 ↔ _
    rw [residueAlgHom, D.pointAlgHomHomeomorph_apply]
    have hz' : z' ∈ Point.overOpen (⊤ : D.neighborhood.toScheme.Opens) := trivial
    constructor
    · intro hzero
      by_contra hnot
      have hunit : IsUnit (D.neighborhood.toScheme.presheaf.germ ⊤
          z'.underlying hz' a) :=
        (hU.isUnit_germ_iff_notMem ⟨z'.underlying, hz'⟩ a).mpr hnot
      have hopen : z'.underlying ∈ D.neighborhood.toScheme.basicOpen a :=
        (Scheme.mem_basicOpen _ _ z'.underlying hz').mpr hunit
      have hne : Point.evaluate ⊤ a z' ≠ 0 :=
        (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
          (X := ComplexPoint.openScheme X D.neighborhood) (U := ⊤) a z' hz').mp hopen
      exact hne hzero
    · intro hmem
      by_contra hne
      have hopen : z'.underlying ∈ D.neighborhood.toScheme.basicOpen a :=
        (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
          (X := ComplexPoint.openScheme X D.neighborhood) (U := ⊤) a z' hz').mpr hne
      have hunit : IsUnit (D.neighborhood.toScheme.presheaf.germ ⊤
          z'.underlying hz' a) :=
        (Scheme.mem_basicOpen _ _ z'.underlying hz').mp hopen
      exact (hU.isUnit_germ_iff_notMem ⟨z'.underlying, hz'⟩ a).mp hunit hmem
  exact heq

theorem localizedPointJetDerivation_ne_zero_of_not_mem_square_coordinate
    (z : ComplexPoint X) :
    let D := ComplexPoint.localEtaleCoordinates X d z
    let hz : z.underlying ∈ D.neighborhood := D.mem
    let q := RingHom.ker (residueAlgHom X d D z hz).toRingHom
    letI : q.IsPrime := RingHom.ker_isPrime (residueAlgHom X d D z hz).toRingHom
    ∀ (a : localSectionRing X d D),
      algebraMap (localSectionRing X d D) (Localization.AtPrime q) a ∈
        maximalIdeal (Localization.AtPrime q) →
      algebraMap (localSectionRing X d D) (Localization.AtPrime q) a ∉
        (maximalIdeal (Localization.AtPrime q)) ^ 2 →
      localizedPointJetDerivation X d D z hz
        (algebraMap (localSectionRing X d D) (Localization.AtPrime q) a) ≠ 0 := by
  dsimp
  let D := ComplexPoint.localEtaleCoordinates X d z
  let hz : z.underlying ∈ D.neighborhood := D.mem
  let : (RingHom.ker (residueAlgHom X d D z hz).toRingHom).IsPrime :=
    RingHom.ker_isPrime (residueAlgHom X d D z hz).toRingHom
  change ∀ (a : localSectionRing X d D),
      algebraMap (localSectionRing X d D) (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) a ∈
        maximalIdeal (Localization.AtPrime
          (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) →
      algebraMap (localSectionRing X d D) (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) a ∉
        (maximalIdeal (Localization.AtPrime
          (RingHom.ker (residueAlgHom X d D z hz).toRingHom))) ^ 2 →
      localizedPointJetDerivation X d D z hz
        (algebraMap (localSectionRing X d D) (Localization.AtPrime
          (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) a) ≠ 0
  have hres : Function.Surjective (residueAlgHom X d D z hz) := by
    intro c
    refine ⟨algebraMap ℂ (localSectionRing X d D) c, ?_⟩
    exact (residueAlgHom X d D z hz).commutes c
  let : (RingHom.ker (residueAlgHom X d D z hz).toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (residueAlgHom X d D z hz).toRingHom hres
  have hstd := coordinate_standardSmooth X d D
  have hreg : IsRegularLocalRing (Localization.AtPrime
      (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) :=
    hstd.isRegularLocalRing_atPrime _
  have hdim : ringKrullDim (Localization.AtPrime
      (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) = d := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      (RingHom.ker (residueAlgHom X d D z hz).toRingHom)
      (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom))]
    exact_mod_cast hstd.height_eq_of_isMaximal
      (RingHom.ker (residueAlgHom X d D z hz).toRingHom)
  intro a ha ha2
  exact localizedPointJetDerivation_ne_zero_of_not_mem_square X d D z hz hreg hdim
    (fun i => localizedPointJetDerivation_coordinate X d z i) a ha ha2
end AlgebraicGeometry.ComplexPoint.Affine
