/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSmoothness
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Affine geometry of the explicit cubic's self-product
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct

namespace AlgebraicGeometry.ExplicitEllipticCandidate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Formation of the hypersurface coordinate ring commutes with extension of scalars. -/
def hypersurfaceBaseChangeEquiv {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (f : MvPolynomial (Fin 2) R) :
    S ⊗[R] HypersurfaceRing f ≃ₐ[S] HypersurfaceRing (f.map (algebraMap R S)) := by
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S (MvPolynomial (Fin 2) R) S
    (Ideal.span (Set.range (fun _ : Unit => f)))).trans
      (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S) ?_)
  simp only [Ideal.map_span, Set.range_const, Set.image_singleton]
  congr 1
  ext x
  simp [Algebra.TensorProduct.includeRight]

/-- The two-variable polynomial ring in the variable order used for Weierstrass equations. -/
def bivariateRingEquiv (R : Type*) [CommRing R] :
    MvPolynomial (Fin 2) R ≃+* Polynomial (Polynomial R) :=
  ((MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin 2) 1)).toRingEquiv.trans
    (MvPolynomial.finSuccEquiv R 1).toRingEquiv).trans
      (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingEquiv)

@[simp]
theorem bivariateRingEquiv_X_zero (R : Type*) [CommRing R] :
    bivariateRingEquiv R (X 0) = Polynomial.C Polynomial.X := by
  simp only [bivariateRingEquiv, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
    renameEquiv_apply, rename_X, Equiv.swap_apply_left, Polynomial.mapEquiv_apply]
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv R 1 (X (Fin.succ (0 : Fin 1)))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ]
  simp [MvPolynomial.uniqueAlgEquiv]

@[simp]
theorem bivariateRingEquiv_X_one (R : Type*) [CommRing R] :
    bivariateRingEquiv R (X 1) = Polynomial.X := by
  simp [bivariateRingEquiv, MvPolynomial.finSuccEquiv_X_zero]

/-- The same short Weierstrass equation over any coefficient ring. -/
def shortEquation (R : Type*) [CommRing R] : WeierstrassCurve R := ⟨0, 0, 0, -1, 0⟩

/-- The first chart, after extension of scalars, is the Weierstrass affine coordinate ring. -/
def zChartBaseChangeCoordinateEquiv (S : Type*) [CommRing S] [Algebra ℂ S] :
    HypersurfaceRing ((chartEquation (Equiv.refl (Fin 3))).map (algebraMap ℂ S)) ≃+*
      (shortEquation S).toAffine.CoordinateRing := by
  apply Ideal.quotientEquiv _ _ (bivariateRingEquiv S)
  rw [Ideal.map_span]
  simp only [Set.range_const, Set.image_singleton]
  congr 1
  simp [shortEquation, WeierstrassCurve.Affine.polynomial]
  ring

/-- The first affine curve chart stays integral after tensoring with any integral complex algebra. -/
theorem zChartTensor_isDomain (S : Type*) [CommRing S] [IsDomain S] [Algebra ℂ S] :
    IsDomain (S ⊗[ℂ] HypersurfaceRing (chartEquation (Equiv.refl (Fin 3)))) := by
  let E := (hypersurfaceBaseChangeEquiv (R := ℂ) (S := S)
    (chartEquation (Equiv.refl (Fin 3)))).toRingEquiv.trans (zChartBaseChangeCoordinateEquiv S)
  exact E.toMulEquiv.isDomain _

/-- A fixed isomorphism from the actual chart to its polynomial quotient. -/
def curveChartHypersurfaceIso (e : Equiv.Perm (Fin 3))
    (hp : (Ideal.span {chartEquation e}).IsPrime) :
    curveChart e ≅ Spec (CommRingCat.of (HypersurfaceRing (chartEquation e))) :=
  (exists_curveChartIsoHypersurface e hp).choose

/-- The chosen affine quotient isomorphism respects the curve's complex structure morphism. -/
theorem curveChartHypersurfaceIso_over (e : Equiv.Perm (Fin 3))
    (hp : (Ideal.span {chartEquation e}).IsPrime) :
    (curveChartHypersurfaceIso e hp).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (HypersurfaceRing (chartEquation e)))) =
        (curveToPlane ⁻¹ᵁ ambientChart e).ι ≫ curveToBase := by
  rw [← curveChartToSpec_toBase, (exists_curveChartIsoHypersurface e hp).choose_spec,
    Category.assoc, ← Spec.map_comp]
  rfl

/-- The product of two actual affine curve charts is the spectrum of their tensor product. -/
def curveChartProductIso (e d : Equiv.Perm (Fin 3))
    (he : (Ideal.span {chartEquation e}).IsPrime)
    (hd : (Ideal.span {chartEquation d}).IsPrime) :
    pullback ((curveToPlane ⁻¹ᵁ ambientChart e).ι ≫ curveToBase)
      ((curveToPlane ⁻¹ᵁ ambientChart d).ι ≫ curveToBase) ≅
        Spec (CommRingCat.of (HypersurfaceRing (chartEquation e) ⊗[ℂ]
          HypersurfaceRing (chartEquation d))) := by
  refine asIso (pullback.map _ _
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (HypersurfaceRing (chartEquation e)))))
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (HypersurfaceRing (chartEquation d)))))
    (curveChartHypersurfaceIso e he).hom (curveChartHypersurfaceIso d hd).hom (𝟙 _) ?_ ?_) ≪≫
      pullbackSpecIso ℂ (HypersurfaceRing (chartEquation e)) (HypersurfaceRing (chartEquation d))
  · simpa using (curveChartHypersurfaceIso_over e he).symm
  · simpa using (curveChartHypersurfaceIso_over d hd).symm

/-- The open subscheme where both factors lie in the `Z` affine chart. -/
def surfaceZChart : Scheme := pullback ((chart 2).ι ≫ curveToBase) ((chart 2).ι ≫ curveToBase)

/-- The natural open embedding of this product chart in the constructed self-product. -/
def surfaceZChartToSurface : surfaceZChart ⟶ surface :=
  pullback.map _ _ curveToBase curveToBase (chart 2).ι (chart 2).ι (𝟙 _)
    (by simp) (by simp)

instance : IsOpenImmersion surfaceZChartToSurface := by
  dsimp only [surfaceZChartToSurface]
  infer_instance

/-- The actual `Z × Z` chart of the self-product is integral. -/
instance surfaceZChart_isIntegral : IsIntegral surfaceZChart := by
  have : IsDomain (HypersurfaceRing (chartEquation (Equiv.refl (Fin 3)))) := by
    dsimp only [HypersurfaceRing]
    rw [Set.range_const]
    let := chartEquation_z_prime
    infer_instance
  have := zChartTensor_isDomain (HypersurfaceRing (chartEquation (Equiv.refl (Fin 3))))
  exact IsIntegral.of_isIso
    (curveChartProductIso (Equiv.refl (Fin 3)) (Equiv.refl (Fin 3))
      chartEquation_z_prime chartEquation_z_prime).inv

/-- Domain preservation by tensor product passes from an integral algebra to its fraction field. -/
theorem tensorFraction_isDomain {k A K S : Type*} [Field k] [CommRing A] [IsDomain A]
    [Field K] [CommRing S] [IsDomain S] [Algebra k A] [Algebra k K] [Algebra A K]
    [IsScalarTower k A K] [IsFractionRing A K] [Algebra k S]
    [IsDomain (S ⊗[k] A)] : IsDomain (S ⊗[k] K) := by
  let φ : S ⊗[k] A →ₐ[S] S ⊗[k] K :=
    Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom k A K)
  let : Algebra (S ⊗[k] A) (S ⊗[k] K) := φ.toAlgebra
  have : IsScalarTower S (S ⊗[k] A) (S ⊗[k] K) :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have := IsLocalization.tensorProduct_tensorProduct_right k S (nonZeroDivisors A) K
    (by ext a; rfl)
  apply IsLocalization.isDomain_of_le_nonZeroDivisors
    (R := S ⊗[k] A)
    (M := (nonZeroDivisors A).map (Algebra.TensorProduct.includeRight (R := k) (A := S)))
    (S ⊗[k] K)
  rintro x ⟨a, ha, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  have hi : Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[k] S ⊗[k] A) :=
    Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap k S))
  simpa only [map_zero] using hi.ne (mem_nonZeroDivisors_iff_ne_zero.mp ha)

/-- Scalars act on sections through the curve's specified structure morphism. -/
def curveScalar (U : curve.Opens) : ℂ →+* Γ(curve, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ curveToBase.appTop ≫
    curve.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom

instance (U : curve.Opens) : Algebra ℂ Γ(curve, U) := (curveScalar U).toAlgebra

instance : Nonempty (⊤ : curve.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩

instance : Algebra ℂ curve.functionField :=
  ((curve.germToFunctionField ⊤).hom.comp (curveScalar ⊤)).toAlgebra

instance curve_functionField_scalarTower (U : curve.Opens) [Nonempty U] :
    IsScalarTower ℂ Γ(curve, U) curve.functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  change (curve.germToFunctionField ⊤).hom.comp (curveScalar ⊤) =
    (curve.germToFunctionField U).hom.comp (curveScalar U)
  change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ curveToBase.appTop ≫
      curve.presheaf.map (homOfLE (show (⊤ : curve.Opens) ≤ ⊤ from le_top)).op ≫
        curve.germToFunctionField ⊤).hom =
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ curveToBase.appTop ≫
      curve.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ curve.germToFunctionField U).hom
  congr 1
  simp [Scheme.germToFunctionField]

/-- The explicit polynomial quotient agrees with sections on the actual affine chart. -/
def curveChartGlobalEquiv (e : Equiv.Perm (Fin 3))
    (hp : (Ideal.span {chartEquation e}).IsPrime) :
    HypersurfaceRing (chartEquation e) ≃+* Γ(curve, curveToPlane ⁻¹ᵁ ambientChart e) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (HypersurfaceRing (chartEquation e)))).symm ≪≫
    asIso (curveChartHypersurfaceIso e hp).hom.appTop ≪≫
      (curveToPlane ⁻¹ᵁ ambientChart e).topIso).commRingCatIsoToRingEquiv

/-- The affine-coordinate equivalence respects scalars from the original complex base. -/
theorem curveChartGlobalEquiv_commutes (e : Equiv.Perm (Fin 3))
    (hp : (Ideal.span {chartEquation e}).IsPrime) (r : ℂ) :
    curveChartGlobalEquiv e hp (algebraMap ℂ _ r) = curveScalar _ r := by
  let U := curveToPlane ⁻¹ᵁ ambientChart e
  let E : U.toScheme ≅ Spec (CommRingCat.of (HypersurfaceRing (chartEquation e))) :=
    curveChartHypersurfaceIso e hp
  have h : (Spec.map (CommRingCat.ofHom (algebraMap ℂ
      (HypersurfaceRing (chartEquation e))))).appTop ≫ E.hom.appTop =
        curveToBase.appTop ≫ U.ι.appTop := by
    exact congrArg Scheme.Hom.appTop (curveChartHypersurfaceIso_over e hp)
  have ht : U.ι.appTop ≫ U.topIso.hom =
      curve.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
    simp [Scheme.Opens.topIso, ← Functor.map_comp]
  have hc : CommRingCat.ofHom (algebraMap ℂ (HypersurfaceRing (chartEquation e))) ≫
      (Scheme.ΓSpecIso _).inv ≫ E.hom.appTop ≫ U.topIso.hom =
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ curveToBase.appTop ≫
          curve.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc]
    rw [← Category.assoc (Spec.map _).appTop E.hom.appTop U.topIso.hom, h,
      Category.assoc, ht]
  exact congrArg (fun g => g r) hc

/-- The section-ring equivalence as a complex-algebra equivalence. -/
def curveChartGlobalAlgEquiv (e : Equiv.Perm (Fin 3))
    (hp : (Ideal.span {chartEquation e}).IsPrime) :
    HypersurfaceRing (chartEquation e) ≃ₐ[ℂ] Γ(curve, curveToPlane ⁻¹ᵁ ambientChart e) :=
  AlgEquiv.ofRingEquiv (curveChartGlobalEquiv_commutes e hp)

/-- The curve's function field remains a domain after tensoring with any integral complex algebra. -/
theorem curveFunctionFieldTensor_isDomain (S : Type*) [CommRing S] [IsDomain S] [Algebra ℂ S] :
    IsDomain (S ⊗[ℂ] curve.functionField) := by
  let U := curveToPlane ⁻¹ᵁ ambientChart (Equiv.refl (Fin 3))
  have : Nonempty U := inferInstanceAs (Nonempty (chart 2).toScheme)
  have : IsFractionRing Γ(curve, U) curve.functionField :=
    functionField_isFractionRing_of_isAffineOpen curve U (chart_isAffineOpen 2)
  have : IsDomain (S ⊗[ℂ] HypersurfaceRing (chartEquation (Equiv.refl (Fin 3)))) :=
    zChartTensor_isDomain S
  have : IsDomain (S ⊗[ℂ] Γ(curve, U)) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := ℂ) (A₁ := S))
      (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime).symm).toRingEquiv.toMulEquiv.isDomain _
  exact tensorFraction_isDomain (A := Γ(curve, U))

/-- Every actual affine curve chart stays integral after tensoring with an integral complex algebra. -/
theorem curveChartTensor_isDomain (e : Equiv.Perm (Fin 3))
    (hp : (Ideal.span {chartEquation e}).IsPrime)
    (S : Type*) [CommRing S] [IsDomain S] [Algebra ℂ S]
    [Nonempty (curveToPlane ⁻¹ᵁ ambientChart e)] :
    IsDomain (S ⊗[ℂ] HypersurfaceRing (chartEquation e)) := by
  have := curveFunctionFieldTensor_isDomain S
  let U := curveToPlane ⁻¹ᵁ ambientChart e
  let φ : HypersurfaceRing (chartEquation e) →ₐ[ℂ] curve.functionField :=
    (IsScalarTower.toAlgHom ℂ Γ(curve, U) curve.functionField).comp
      (curveChartGlobalAlgEquiv e hp).toAlgHom
  have hi : Function.Injective φ :=
    (curve.germToFunctionField_injective U).comp (curveChartGlobalAlgEquiv e hp).injective
  let ψ : S ⊗[ℂ] HypersurfaceRing (chartEquation e) →ₐ[ℂ] S ⊗[ℂ] curve.functionField :=
    Algebra.TensorProduct.map (AlgHom.id ℂ S) φ
  apply Function.Injective.isDomain ψ.toRingHom.toMonoidWithZeroHom
  exact Module.Flat.lTensor_preserves_injective_linearMap φ.toLinearMap hi

/-- Products of the actual affine curve charts are integral. -/
theorem curveChartProduct_isIntegral (e d : Equiv.Perm (Fin 3))
    (he : (Ideal.span {chartEquation e}).IsPrime)
    (hd : (Ideal.span {chartEquation d}).IsPrime)
    [Nonempty (curveToPlane ⁻¹ᵁ ambientChart d)] :
    IsIntegral (pullback ((curveToPlane ⁻¹ᵁ ambientChart e).ι ≫ curveToBase)
      ((curveToPlane ⁻¹ᵁ ambientChart d).ι ≫ curveToBase)) := by
  have : IsDomain (HypersurfaceRing (chartEquation e)) := by
    dsimp only [HypersurfaceRing]
    rw [Set.range_const]
    let := he
    infer_instance
  have := curveChartTensor_isDomain d hd (HypersurfaceRing (chartEquation e))
  exact IsIntegral.of_isIso (curveChartProductIso e d he hd).inv

/-- The standard two-chart cover of the curve. -/
def curveTwoChartCover : curve.OpenCover := curve.openCoverOfIsOpenCover
    (fun i : Fin 2 => ![chart 1, chart 2] i) (by
      apply top_unique
      rw [← chart_one_sup_chart_two]
      exact sup_le (le_iSup (fun i : Fin 2 => ![chart 1, chart 2] i) 0)
        (le_iSup (fun i : Fin 2 => ![chart 1, chart 2] i) 1))

/-- The resulting four-chart open cover of the actual self-product. -/
def surfaceChartCover : surface.OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight curveTwoChartCover curveTwoChartCover curveToBase curveToBase

instance surfaceChartCover_isIntegral (ij : surfaceChartCover.I₀) :
    IsIntegral (surfaceChartCover.X ij) := by
  have : Nonempty (curveToPlane ⁻¹ᵁ ambientChart (Equiv.swap (1 : Fin 3) 2)) :=
    inferInstanceAs (Nonempty (chart 1).toScheme)
  have : Nonempty (curveToPlane ⁻¹ᵁ ambientChart (Equiv.refl (Fin 3))) :=
    inferInstanceAs (Nonempty (chart 2).toScheme)
  change Fin 2 × Fin 2 at ij
  rcases ij with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  · exact curveChartProduct_isIntegral (Equiv.swap (1 : Fin 3) 2) (Equiv.swap (1 : Fin 3) 2)
      chartEquation_y_prime chartEquation_y_prime
  · exact curveChartProduct_isIntegral (Equiv.swap (1 : Fin 3) 2) (Equiv.refl (Fin 3))
      chartEquation_y_prime chartEquation_z_prime
  · exact curveChartProduct_isIntegral (Equiv.refl (Fin 3)) (Equiv.swap (1 : Fin 3) 2)
      chartEquation_z_prime chartEquation_y_prime
  · exact curveChartProduct_isIntegral (Equiv.refl (Fin 3)) (Equiv.refl (Fin 3))
      chartEquation_z_prime chartEquation_z_prime

instance surface_isReduced : IsReduced surface := IsReduced.of_openCover surface surfaceChartCover

/-- A point of the self-product whose two factors lie in both affine curve charts. -/
def surfaceOverlapPoint : surface :=
  (Scheme.Pullback.exists_preimage_pullback (f := curveToBase) (g := curveToBase)
    overlapPoint.underlying overlapPoint.underlying rfl).choose

@[simp]
theorem surfaceOverlapPoint_fst : pullback.fst curveToBase curveToBase surfaceOverlapPoint =
    overlapPoint.underlying :=
  (Scheme.Pullback.exists_preimage_pullback (f := curveToBase) (g := curveToBase)
    overlapPoint.underlying overlapPoint.underlying rfl).choose_spec.1

@[simp]
theorem surfaceOverlapPoint_snd : pullback.snd curveToBase curveToBase surfaceOverlapPoint =
    overlapPoint.underlying :=
  (Scheme.Pullback.exists_preimage_pullback (f := curveToBase) (g := curveToBase)
    overlapPoint.underlying overlapPoint.underlying rfl).choose_spec.2

/-- The four integral product charts have a common point. -/
theorem surfaceOverlapPoint_mem_chartRange (ij : surfaceChartCover.I₀) :
    surfaceOverlapPoint ∈ (surfaceChartCover.f ij).opensRange := by
  change surfaceOverlapPoint ∈ Set.range (surfaceChartCover.f ij)
  change Fin 2 × Fin 2 at ij
  rcases ij with ⟨i, j⟩
  change surfaceOverlapPoint ∈ Set.range (pullback.map
    (curveTwoChartCover.f i ≫ curveToBase) (curveTwoChartCover.f j ≫ curveToBase)
    curveToBase curveToBase (curveTwoChartCover.f i) (curveTwoChartCover.f j) (𝟙 base)
    (by simp) (by simp))
  rw [Scheme.Pullback.range_map]
  simp only [Set.mem_inter_iff, Set.mem_preimage, surfaceOverlapPoint_fst, surfaceOverlapPoint_snd]
  have hm (i : Fin 2) : overlapPoint.underlying ∈ Set.range (curveTwoChartCover.f i) := by
    change overlapPoint.underlying ∈ Set.range (![chart 1, chart 2] i).ι
    rw [Scheme.Opens.range_ι]
    fin_cases i
    · change overlapPoint.underlying ∈ chart 1
      change (curvePoint _ _ _).underlying ∈ chart 1
      apply (curvePoint_mem_chart_iff _ _ _ 1).2
      intro h
      have := congrArg Complex.re h
      norm_num at this
    · change overlapPoint.underlying ∈ chart 2
      change (curvePoint _ _ _).underlying ∈ chart 2
      exact (curvePoint_mem_chart_iff _ _ _ 2).2 one_ne_zero
  exact ⟨hm i, hm j⟩

/-- The integral product charts with a common point make the self-product irreducible. -/
instance surface_irreducibleSpace : IrreducibleSpace surface := by
  let U (i : surfaceChartCover.I₀) := (surfaceChartCover.f i).opensRange
  have hpair : Pairwise (fun i j => ¬ Disjoint (U i) (U j)) := by
    intro i j _ hd
    have hm : surfaceOverlapPoint ∈ U i ⊓ U j :=
      ⟨surfaceOverlapPoint_mem_chartRange i, surfaceOverlapPoint_mem_chartRange j⟩
    rw [disjoint_iff.mp hd] at hm
    exact hm
  have hp (i : surfaceChartCover.I₀) : PreirreducibleSpace (U i) := by
    apply Subtype.preirreducibleSpace
    change IsPreirreducible (Set.range (surfaceChartCover.f i))
    rw [← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ (X := surfaceChartCover.X i)).image
      (surfaceChartCover.f i) (surfaceChartCover.f i).continuous.continuousOn
  have := PreirreducibleSpace.of_isOpenCover hpair surfaceChartCover.iSup_opensRange hp
  exact ⟨⟨surfaceOverlapPoint⟩⟩

/-- The constructed self-product of the explicit projective cubic is an integral scheme. -/
instance surface_isIntegral : IsIntegral surface :=
  isIntegral_of_irreducibleSpace_of_isReduced surface

end AlgebraicGeometry.ExplicitEllipticCandidate
