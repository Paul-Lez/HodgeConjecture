/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.Algebra.Homology.DerivedCategory.MappingConeConnectingNaturality
public import HodgeConjecture.Other.AlgebraicGeometry.DerivedSupportRationalConeComparison
public import HodgeConjecture.Other.AlgebraicGeometry.HypercohomologyGlobalSectionsShift

/-! # Support-forgetting in the actual rational injective model -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ)

local instance rationalConeForgetSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf structureMap) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf structureMap)

instance ambientRationalInjectiveComplex_isKInjective :
    (ambientRationalInjectiveComplex structureMap).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ 0

/-- Ordinary rational cohomology computed by the actual ambient rational
injective resolution. This has the ordinary augmentation normalization. -/
def rationalCohomologyAddEquivAmbientInjectiveHomology (n : ℤ) :
    FieldCohomology ℚ structureMap n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X structureMap))
        (ambientRationalInjectiveComplex structureMap)).homology n := by
  let e : FieldCohomology ℚ structureMap n ≃+
      Hypercohomology structureMap (ambientRationalInjectiveComplex structureMap) n :=
    { toEquiv := Localization.SmallShiftedHom.postcompEquiv
        (ambientRationalInjectiveAugmentation structureMap)
        ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)
      map_add' α β := (hypercohomologyMap structureMap
        (ambientRationalInjectiveAugmentation structureMap) n).map_add α β }
  exact e.trans (hypercohomologyAddEquivGlobalSectionsKInjective structureMap _ n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma hypercohomologyAddEquivDerived_comp_shifted
    {K L : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ}
    (s n n' : ℤ) (h : s + n = n') (g : K ⟶ L⟦s⟧)
    (x : Hypercohomology structureMap K n) :
    hypercohomologyAddEquivDerived structureMap L n'
      (x.comp (Localization.SmallShiftedHom.mk
        (analyticQuasiIsomorphisms structureMap) g) h) =
    (hypercohomologyAddEquivDerived structureMap K n x).comp
      (ShiftedHom.map g DerivedCategory.Q) h := by
  change Localization.SmallShiftedHom.equiv _ DerivedCategory.Q _ = _
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma hypercohomologyMap_comp_shifted
    {K L K' L' : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ}
    (s n n' : ℤ) (h : s + n = n')
    (a : K ⟶ K') (b : L ⟶ L') (g : K ⟶ L⟦s⟧) (g' : K' ⟶ L'⟦s⟧)
    (hab : a ≫ g' = g ≫ b⟦s⟧') (x : Hypercohomology structureMap K n) :
    hypercohomologyMap structureMap b n'
      (x.comp (Localization.SmallShiftedHom.mk
        (analyticQuasiIsomorphisms structureMap) g) h) =
    (hypercohomologyMap structureMap a n x).comp
      (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms structureMap) g') h := by
  apply (hypercohomologyAddEquivDerived structureMap L' n').injective
  rw [hypercohomologyAddEquivDerived_naturality,
    hypercohomologyAddEquivDerived_comp_shifted,
    hypercohomologyAddEquivDerived_comp_shifted,
    hypercohomologyAddEquivDerived_naturality]
  exact ShiftedHom.comp_commSq s n n' h _ _ _ _
    (ShiftedHom.map_commSq s a b g g' hab DerivedCategory.Q) _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original support-forgetting map, after replacing the ambient
constant sheaf by its actual injective resolution, is the actual cone
connecting homology map. -/
lemma rationalCohomologyAddEquivAmbientInjectiveHomology_forgetSupport_cone
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) (n : ℤ)
    (x : RationalCohomologyWithSupport structureMap Z n) :
    rationalCohomologyAddEquivAmbientInjectiveHomology structureMap n
      (forgetSupport structureMap Z n x) =
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
      (ShiftedHom.map
        (CochainComplex.mappingCone.triangle
          (ambientRationalInjectiveRestriction structureMap Z hZ)).mor₃
        ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X structureMap))).mapHomologicalComplex (.up ℤ)))
      (n - 1) n (by omega)
      (rationalSupportAddEquivAmbientInjectiveConeGlobalSections structureMap Z hZ n x) := by
  change hypercohomologyAddEquivGlobalSectionsKInjective structureMap _ n
    (hypercohomologyMap structureMap (ambientRationalInjectiveAugmentation structureMap) n
      (x.comp (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms structureMap)
        (CochainComplex.mappingCone.triangle
          (rationalRestrictionComplexInt structureMap Z)).mor₃) (by omega))) = _
  exact (congrArg (hypercohomologyAddEquivGlobalSectionsKInjective structureMap
    (ambientRationalInjectiveComplex structureMap) n)
    (hypercohomologyMap_comp_shifted _ 1 (n - 1) n (by omega)
    (rationalSupportConeToAmbientInjectiveCone structureMap Z hZ) _ _ _
    (rationalSupportConeToAmbientInjectiveCone_connecting structureMap Z hZ) x)).trans
    (hypercohomologyAddEquivGlobalSectionsKInjective_shifted_naturality
      structureMap
        (CochainComplex.mappingCone (ambientRationalInjectiveRestriction structureMap Z hZ))
        (ambientRationalInjectiveComplex structureMap) 1 (n - 1) n (by omega) _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The normalized support equivalence intertwines the existing
`forgetSupport` with the actual inclusion of supported injective sections.
No compatibility or choice of a sign is supplied as an input. -/
lemma rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) (n : ℤ)
    (x : RationalCohomologyWithSupport structureMap Z n) :
    rationalCohomologyAddEquivAmbientInjectiveHomology structureMap n
      (forgetSupport structureMap Z n x) =
    HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X structureMap)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (ambientRationalInjectiveComplex structureMap)).f n
      (rationalSupportAddEquivSupportedInjectiveHomology structureMap Z hZ n x) := by
  let Y := TopCat.of (ComplexPoint X structureMap)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U ⊤
    (ambientRationalInjectiveComplex structureMap)
  let b := ambientRationalInjectiveRestriction structureMap Z hZ
  let c := actualSupportConeToAmbientInjectiveGlobalCone structureMap Z hZ
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0
  let e := CochainComplex.mappingCone.mapHomologicalComplexIso b Γ
  let y := rationalSupportAddEquivAmbientInjectiveConeGlobalSections structureMap Z hZ n x
  let : QuasiIso (CochainComplex.mappingCocone.shiftedLiftShortComplex S) :=
    CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y U ⊤ _)
  have hc : HomologicalComplex.homologyMap c (n - 1) ≫
      H.shiftMap (CochainComplex.mappingCone.triangle
        ((Γ.mapHomologicalComplex (.up ℤ)).map b)).mor₃ (n - 1) n (by omega) =
      H.shiftMap (CochainComplex.mappingCone.triangle S.g).mor₃ (n - 1) n (by omega) := by
    change (H.shift (n - 1)).map c ≫ _ = _
    rw [← Functor.shiftMap_comp', actualSupportConeToAmbientInjectiveGlobalCone_connecting]
  have hc' : inv (HomologicalComplex.homologyMap c (n - 1)) ≫
      H.shiftMap (CochainComplex.mappingCone.triangle S.g).mor₃ (n - 1) n (by omega) =
      H.shiftMap (CochainComplex.mappingCone.triangle
        ((Γ.mapHomologicalComplex (.up ℤ)).map b)).mor₃ (n - 1) n (by omega) := by
    rw [← hc, IsIso.inv_hom_id_assoc]
  have hl := CochainComplex.mappingCocone.inv_homologyMap_shiftedLiftShortComplex_connecting
    S (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y U ⊤ _)
    (n - 1) n (by omega)
  have he := CochainComplex.mappingCone.mapHomologicalComplexIso_homology_connecting
    b Γ (n - 1) n (by omega)
  rw [rationalCohomologyAddEquivAmbientInjectiveHomology_forgetSupport_cone]
  change H.shiftMap (ShiftedHom.map (CochainComplex.mappingCone.triangle b).mor₃
      (Γ.mapHomologicalComplex (.up ℤ))) (n - 1) n (by omega) y =
    HomologicalComplex.homologyMap S.f n
      (-(((H.shiftIso 1 (n - 1) n (by omega)).hom.app S.X₁)
        ((inv (HomologicalComplex.homologyMap
          (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1)))
          ((inv (HomologicalComplex.homologyMap c (n - 1)))
            (HomologicalComplex.homologyMap e.hom (n - 1) y)))))
  rw [map_neg]
  have hly := ConcreteCategory.congr_hom hl
    ((inv (HomologicalComplex.homologyMap c (n - 1)))
      (HomologicalComplex.homologyMap e.hom (n - 1) y))
  change -(HomologicalComplex.homologyMap S.f n
      (((H.shiftIso 1 (n - 1) n (by omega)).hom.app S.X₁)
        ((inv (HomologicalComplex.homologyMap
          (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1)))
          ((inv (HomologicalComplex.homologyMap c (n - 1)))
            (HomologicalComplex.homologyMap e.hom (n - 1) y))))) = _ at hly
  rw [hly]
  exact (ConcreteCategory.congr_hom he y).symm.trans
    (ConcreteCategory.congr_hom hc' (HomologicalComplex.homologyMap e.hom (n - 1) y)).symm

end AlgebraicGeometry.ComplexPoint
