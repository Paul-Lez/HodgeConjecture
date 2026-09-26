/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicAnalyticSpace
public import Other.AlgebraicGeometry.ComplexPointClosedPointEquiv
public import Other.Oka.Analytification.Scheme
public import Other.Oka.Analytification.RET.ClosedPoints
public import Other.Oka.AnalyticSpace.LocalIso
public import Other.Oka.Analytification.GAGA.StalkFlat

/-! The project-specific holomorphic model agrees with Oka's canonical analytification. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

/-- Identify the repository's `Spec ℂ` convention with Oka's lifted convention. -/
def specComplexULiftIso :
    Spec (CommRingCat.of ℂ) ≅ ComplexAnalytic.Specℂ.{0} :=
  Scheme.Spec.mapIso ULift.ringEquiv.toCommRingCatIso.op

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- Regard the smooth scheme as an Oka scheme locally of finite type over `ℂ`. -/
def toSchemeLFTℂ : ComplexAnalytic.SchemeLFTℂ.{0} :=
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  ⟨Over.mk (X.hom ≫ (specComplexULiftIso).hom),
    show LocallyOfFiniteType (X.hom ≫ (specComplexULiftIso).hom) from inferInstance⟩

theorem toSchemeLFTℂ_isProper [IsProjective X.hom] :
    IsProper (toSchemeLFTℂ X d).obj.hom := by
  change IsProper (X.hom ≫ (specComplexULiftIso).hom)
  infer_instance

/-- The algebra structure on global regular functions induced by `X ⟶ Spec ℂ`. -/
def algebraicAlgebraMap :
    ℂ →+* LocallyRingedSpace.Γ.obj (op X.left.toLocallyRingedSpace) :=
  ((ΓSpec.locallyRingedSpaceAdjunction.homEquiv X.left.toLocallyRingedSpace
    (op ↧ℂ)).symm X.hom.toLRSHom).unop.hom

lemma algebraicAlgebraMap_eq_appTop :
    algebraicAlgebraMap X =
      X.hom.appTop.hom.comp (Scheme.ΓSpecIso ↧ℂ).inv.hom := by
  simp only [algebraicAlgebraMap, Functor.rightOp_obj, LocallyRingedSpace.Γ_obj]
  rfl

def pulledHolomorphicAlgebraMap :
    ℂ →+* (holomorphicLocallyRingedSpace X d).presheaf.obj (op ⊤) :=
  LocallyRingedSpace.comapAlgMap (analytificationToAlgebraic X d) (algebraicAlgebraMap X)

set_option backward.isDefEq.respectTransparency.types false in
lemma evaluate_algebraicAlgebraMap (z : ComplexPoint X) (c : ℂ) :
    Point.evaluate ⊤ (algebraicAlgebraMap X c) z = c := by
  rw [evaluate_top_eq_appTop, algebraicAlgebraMap_eq_appTop]
  have hzapp : X.hom.appTop ≫ z.left.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Over.w z]
    rfl
  have hzval := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hzapp)
    ((Scheme.ΓSpecIso ↧ℂ).inv c)
  change (Scheme.ΓSpecIso ↧ℂ).hom
    (z.left.appTop (X.hom.appTop ((Scheme.ΓSpecIso ↧ℂ).inv c))) = c
  rw [show z.left.appTop (X.hom.appTop ((Scheme.ΓSpecIso ↧ℂ).inv c)) =
    (Scheme.ΓSpecIso ↧ℂ).inv c by exact hzval]
  simp

lemma pulledHolomorphicAlgebraMap_eq :
    pulledHolomorphicAlgebraMap X d = ContMDiffMap.C := by
  ext c
  apply ContMDiffMap.ext
  intro z
  exact evaluate_algebraicAlgebraMap X z c

lemma analytificationToAlgebraic_isCLinear :
    ComplexAnalytic.IsCLinearHom (analytificationToAlgebraic X d)
      ContMDiffMap.C (algebraicAlgebraMap X) := by
  rw [← pulledHolomorphicAlgebraMap_eq X d]
  exact ComplexAnalytic.isCLinearHom_comapAlgMap _ _

set_option backward.isDefEq.respectTransparency.types false in
lemma algebraicStructure_eq_toSpecOfAlgebraMap :
    (X.hom ≫ (specComplexULiftIso).hom).toLRSHom =
      X.left.toLocallyRingedSpace.toSpecOfAlgMap
        (ComplexAnalytic.uliftAlgMap (algebraicAlgebraMap X)) := by
  have hX : X.left.toLocallyRingedSpace.toSpecOfAlgMap (algebraicAlgebraMap X) =
      X.hom.toLRSHom := by
    rw [LocallyRingedSpace.toSpecOfAlgMap_eq_homEquiv]
    exact (ΓSpec.locallyRingedSpaceAdjunction.homEquiv
      X.left.toLocallyRingedSpace (op ↧ℂ)).apply_symm_apply X.hom.toLRSHom
  change X.hom.toLRSHom ≫
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom ULift.ringEquiv.toRingHom) = _
  rw [← hX]
  change (X.left.toΓSpec ≫
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraicAlgebraMap X))) ≫
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom ULift.ringEquiv.toRingHom) =
    X.left.toΓSpec ≫ Spec.locallyRingedSpaceMap
      (CommRingCat.ofHom ((algebraicAlgebraMap X).comp ULift.ringEquiv.toRingHom))
  calc
    _ = X.left.toΓSpec ≫
        (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraicAlgebraMap X)) ≫
          Spec.locallyRingedSpaceMap
            (CommRingCat.ofHom ULift.ringEquiv.toRingHom)) := by rw [Category.assoc]
    _ = X.left.toΓSpec ≫ Spec.locallyRingedSpaceMap
        (CommRingCat.ofHom ULift.ringEquiv.toRingHom ≫
          CommRingCat.ofHom (algebraicAlgebraMap X)) := by
      rw [Spec.locallyRingedSpaceMap_comp]
    _ = _ := by
      apply congrArg (fun q ↦ X.left.toΓSpec ≫ Spec.locallyRingedSpaceMap q)
      exact (CommRingCat.ofHom_comp ULift.ringEquiv.toRingHom
        (algebraicAlgebraMap X)).symm

/-- The project-specific holomorphic comparison, as a morphism over Oka's `Spec ℂ`. -/
def holomorphicAnalytificationπ :
    ComplexAnalytic.AnalyticSpace.toOverSpec.obj (holomorphicAnalyticSpace X d) ⟶
      ComplexAnalytic.schemeToOverSpec.obj (toSchemeLFTℂ X d).obj :=
  Over.homMk (analytificationToAlgebraic X d) <| by
    change analytificationToAlgebraic X d ≫
        (X.hom ≫ (specComplexULiftIso).hom).toLRSHom =
      (holomorphicLocallyRingedSpace X d).toSpecOfAlgMap
        (ComplexAnalytic.uliftAlgMap ContMDiffMap.C)
    rw [algebraicStructure_eq_toSpecOfAlgebraMap X]
    exact (ComplexAnalytic.isCLinearHom_iff_comp_toSpecOfAlgMap
      (analytificationToAlgebraic X d) ContMDiffMap.C
      (algebraicAlgebraMap X)).1
        (analytificationToAlgebraic_isCLinear X d)

/-- The canonical map from the project-specific holomorphic model to Oka's analytification. -/
def comparisonToCanonical :
    holomorphicAnalyticSpace X d ⟶
      ComplexAnalytic.analytification.obj (toSchemeLFTℂ X d) :=
  (ComplexAnalytic.isAnalytification_analytificationπ (toSchemeLFTℂ X d)).lift
    (holomorphicAnalytificationπ X d)

@[reassoc (attr := simp)]
lemma comparisonToCanonical_fac :
    ComplexAnalytic.AnalyticSpace.toOverSpec.map (comparisonToCanonical X d) ≫
        ComplexAnalytic.analytificationπ (toSchemeLFTℂ X d) =
      holomorphicAnalytificationπ X d :=
  (ComplexAnalytic.isAnalytification_analytificationπ (toSchemeLFTℂ X d)).lift_fac _

lemma analytificationπ_comparisonToCanonical_base (z : ComplexPoint X) :
    (ComplexAnalytic.analytificationπ (toSchemeLFTℂ X d)).left.base
        ((comparisonToCanonical X d).toLRSHom.base z) = z.underlying := by
  have h := congrArg (fun f ↦ f.left.base z) (comparisonToCanonical_fac X d)
  exact h

lemma comparisonToCanonical_base_injective_of_analytificationπ_base_injective
    (hπ : Function.Injective
      (ComplexAnalytic.analytificationπ (toSchemeLFTℂ X d)).left.base) :
    Function.Injective (comparisonToCanonical X d).toLRSHom.base := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  letI : LocallyOfFiniteType X.hom := inferInstance
  intro z w hzw
  apply (complexPointEquivClosedPoint X).injective
  apply Subtype.ext
  change z.underlying = w.underlying
  rw [← analytificationπ_comparisonToCanonical_base X d z,
    ← analytificationπ_comparisonToCanonical_base X d w, hzw]

lemma comparisonToCanonical_base_surjective_of_range_analytificationπ_base
    (hπ : Function.Injective
      (ComplexAnalytic.analytificationπ (toSchemeLFTℂ X d)).left.base)
    (hrange : Set.range
      (ComplexAnalytic.analytificationπ (toSchemeLFTℂ X d)).left.base =
        closedPoints X.left) :
    Function.Surjective (comparisonToCanonical X d).toLRSHom.base := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  letI : LocallyOfFiniteType X.hom := inferInstance
  intro y
  have hyClosed : IsClosed
      ({(ComplexAnalytic.analytificationπ (toSchemeLFTℂ X d)).left.base y} :
        Set X.left) := by
    have hy : (ComplexAnalytic.analytificationπ (toSchemeLFTℂ X d)).left.base y ∈
        Set.range (ComplexAnalytic.analytificationπ (toSchemeLFTℂ X d)).left.base :=
      ⟨y, rfl⟩
    rw [hrange] at hy
    exact hy
  let z : ComplexPoint X := (complexPointEquivClosedPoint X).symm
    ⟨(ComplexAnalytic.analytificationπ (toSchemeLFTℂ X d)).left.base y, hyClosed⟩
  refine ⟨z, hπ ?_⟩
  rw [analytificationπ_comparisonToCanonical_base X d z]
  exact congrArg Subtype.val <|
    (complexPointEquivClosedPoint X).apply_symm_apply
      ⟨(ComplexAnalytic.analytificationπ (toSchemeLFTℂ X d)).left.base y, hyClosed⟩

lemma comparisonToCanonical_base_bijective_of_closedPoints
    (hπ : Function.Injective
      (ComplexAnalytic.analytificationπ (toSchemeLFTℂ X d)).left.base)
    (hrange : Set.range
      (ComplexAnalytic.analytificationπ (toSchemeLFTℂ X d)).left.base =
        closedPoints X.left) :
    Function.Bijective (comparisonToCanonical X d).toLRSHom.base :=
  ⟨comparisonToCanonical_base_injective_of_analytificationπ_base_injective X d hπ,
    comparisonToCanonical_base_surjective_of_range_analytificationπ_base X d hπ hrange⟩

theorem comparisonToCanonical_base_bijective :
    Function.Bijective (comparisonToCanonical X d).toLRSHom.base :=
  comparisonToCanonical_base_bijective_of_closedPoints X d
    (ComplexAnalytic.analytificationπ_base_injective (toSchemeLFTℂ X d))
    (ComplexAnalytic.range_analytificationπ_base (toSchemeLFTℂ X d))

/-- Local chart compatibility upgrades the canonical comparison to an isomorphism. -/
theorem comparisonToCanonical_isIso
    [ComplexAnalytic.AnalyticSpace.IsLocalIso (comparisonToCanonical X d)] :
    IsIso (comparisonToCanonical X d) :=
  ComplexAnalytic.AnalyticSpace.isIso_of_isLocalIso_of_bijective _
    (comparisonToCanonical_base_bijective X d)

/-- Once the chart comparison is local, the project-specific map has Oka's universal property. -/
theorem holomorphicAnalytificationπ_isAnalytification
    [ComplexAnalytic.AnalyticSpace.IsLocalIso (comparisonToCanonical X d)] :
    ComplexAnalytic.IsAnalytification (holomorphicAnalytificationπ X d) := by
  letI : IsIso (comparisonToCanonical X d) := comparisonToCanonical_isIso X d
  rw [← comparisonToCanonical_fac X d]
  exact (ComplexAnalytic.isAnalytification_analytificationπ (toSchemeLFTℂ X d)).of_iso_source
    (asIso (comparisonToCanonical X d))

set_option backward.isDefEq.respectTransparency.types false in
/-- Oka's local GAGA theorem supplies faithful flatness for the holomorphic comparison. -/
theorem faithfullyFlat_stalkMap_holomorphicAnalytificationπ
    [ComplexAnalytic.AnalyticSpace.IsLocalIso (comparisonToCanonical X d)]
    (z : ComplexPoint X) :
    ((analytificationToPresheafedSpace X d).stalkMap z).hom.FaithfullyFlat := by
  have h := ComplexAnalytic.faithfullyFlat_stalkMap_of_isAnalytification
    (holomorphicAnalytificationπ_isAnalytification X d)
    (ComplexAnalytic.exists_iso_specOver_overRestrict (toSchemeLFTℂ X d)) z
  change ((analytificationToAlgebraic X d).stalkMap z).hom.FaithfullyFlat at h
  exact h

end AlgebraicGeometry.ComplexPoint
