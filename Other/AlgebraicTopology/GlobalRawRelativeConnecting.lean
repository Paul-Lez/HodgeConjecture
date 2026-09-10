/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.BettiSupportSingularGlobalComparison
public import Other.AlgebraicTopology.RelativeCochainConeForgetComparison
public import Other.Algebra.Homology.MapHomologyShift
public import Other.Algebra.Homology.MapArrowConeConnecting

/-! # Exact connecting sign for the raw global relative cochain comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology.Singular

variable (R : Type) [Field R] (X : TopCat.{0}) (A : Set X)

/-- The actual global raw restriction-cone isomorphism preserves its negative
connecting map and its actual ambient cochain identification. -/
@[reassoc]
theorem globalRawSingularRestrictionConeIsoRelative_connecting :
    (globalRawSingularRestrictionConeIsoRelative R X A).hom ≫
      (CochainComplex.mappingCone.triangle
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
          (relativeCochainRestrictionInt R (TopPair.ofSubset A)))).mor₃ =
    (CochainComplex.mappingCone.triangle (globalRawSingularRestrictionInt R X A)).mor₃ ≫
      (globalRawSingularCochainComplexIntIsoRelative R X).hom⟦(1 : ℤ)⟧' :=
  CochainComplex.mappingCone.homotopyCofiber_mapArrowIso_connecting _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- After all literal global-cochain and coefficient-forgetting identifications,
the raw restriction-cone connecting map is the negative relative cochain inclusion.
No arbitrary comparison, purity, or one-dimensionality is used. -/
theorem globalRawSingularRestrictionCone_signed_inclusion (n : ℕ) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
        (CochainComplex.mappingCone.triangle (globalRawSingularRestrictionInt R X A)).mor₃
        ((n : ℤ) - 1) (n : ℤ) (by omega) ≫
      HomologicalComplex.homologyMap (globalRawSingularCochainComplexIntIsoRelative R X).hom
        (n : ℤ) ≫
      (((relativeDualCochainShortComplexInt R (TopPair.ofSubset A)).X₂.sc (n : ℤ)).mapHomologyIso
        (forget₂ (ModuleCat R) AddCommGrpCat)).hom =
    -(HomologicalComplex.homologyMap (globalRawSingularRestrictionConeIsoRelative R X A).hom
        ((n : ℤ) - 1) ≫
      HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.mapHomologicalComplexIso
          (relativeCochainRestrictionInt R (TopPair.ofSubset A))
          (forget₂ (ModuleCat R) AddCommGrpCat)).inv ((n : ℤ) - 1) ≫
      (((CochainComplex.mappingCone
        (relativeCochainRestrictionInt R (TopPair.ofSubset A))).sc ((n : ℤ) - 1)).mapHomologyIso
          (forget₂ (ModuleCat R) AddCommGrpCat)).hom ≫
      (forget₂ (ModuleCat R) AddCommGrpCat).map
        ((relativeCochainConeHomologyIsoDualRelativeInt R (TopPair.ofSubset A) n).hom ≫
          HomologicalComplex.homologyMap
            (relativeDualCochainShortComplexInt R (TopPair.ofSubset A)).f (n : ℤ))) := by
  let F := forget₂ (ModuleCat R) AddCommGrpCat
  let g := relativeCochainRestrictionInt R (TopPair.ofSubset A)
  let eF := CochainComplex.mappingCone.mapHomologicalComplexIso g F
  let HD := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0
  have he := congrArg
    (fun f => HD.shiftMap f ((n : ℤ) - 1) (n : ℤ) (show (1 : ℤ) + ((n : ℤ) - 1) = n by omega))
    (globalRawSingularRestrictionConeIsoRelative_connecting R X A)
  rw [Functor.shiftMap_comp', Functor.shiftMap_comp] at he
  have hF := CochainComplex.mappingCone.mapHomologicalComplexIso_homology_connecting
    g F ((n : ℤ) - 1) (n : ℤ) (by omega)
  have hF' := congrArg
    (fun f => HomologicalComplex.homologyMap eF.inv ((n : ℤ) - 1) ≫ f) hF
  simp only [eF, ← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    Iso.inv_hom_id, HomologicalComplex.homologyMap_id, Category.id_comp] at hF'
  have hs := CochainComplex.mapHomologyIso_shiftMap F 1 ((n : ℤ) - 1) n (by omega)
    (CochainComplex.mappingCone.triangle g).mor₃
  rw [← Category.assoc]
  erw [← he]
  simp only [Category.assoc]
  erw [hF']
  simp only [Category.assoc]
  erw [hs]
  erw [← relativeCochainConeHomologyIsoDualRelativeInt_inclusion]
  simp only [Functor.map_neg, Preadditive.comp_neg]
  rfl

/-- The positive ordinary raw cochain class induced by a relative cohomology
class: actual dual-relative inclusion, with only coefficient-forgetting and
the literal global raw ambient-cochain identification. -/
def globalRawRelativeCochainClass (n : ℕ)
    (a : RelativeCohomology R (TopPair.ofSubset A) n) :
    (globalRawSingularCochainComplexInt R X).homology (n : ℤ) :=
  (HomologicalComplex.homologyMapIso (globalRawSingularCochainComplexIntIsoRelative R X)
    (n : ℤ)).inv
    ((((relativeDualCochainShortComplexInt R (TopPair.ofSubset A)).X₂.sc (n : ℤ)).mapHomologyIso
      (forget₂ (ModuleCat R) AddCommGrpCat)).inv
      (HomologicalComplex.homologyMap
        (relativeDualCochainShortComplexInt R (TopPair.ofSubset A)).f (n : ℤ)
          ((relativeDualCochainCohomologyEquiv R (TopPair.ofSubset A) n).symm a)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- The original raw relative comparison followed by cone connecting is exactly
the negative of the positive ordinary cochain class. -/
theorem globalRawSingularRestrictionCone_connecting_of_relative (n : ℕ)
    (a : RelativeCohomology R (TopPair.ofSubset A) n) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
      (CochainComplex.mappingCone.triangle (globalRawSingularRestrictionInt R X A)).mor₃
      ((n : ℤ) - 1) (n : ℤ) (by omega)
      ((globalRawSingularRestrictionConeCohomologyEquivRelative R X A n).symm a) =
        -globalRawRelativeCochainClass R X A n a := by
  let F := forget₂ (ModuleCat R) AddCommGrpCat
  let S := relativeDualCochainShortComplexInt R (TopPair.ofSubset A)
  let g := relativeCochainRestrictionInt R (TopPair.ofSubset A)
  let eX := HomologicalComplex.homologyMapIso
    (globalRawSingularCochainComplexIntIsoRelative R X) (n : ℤ)
  let eA := (S.X₂.sc (n : ℤ)).mapHomologyIso F
  let w := (globalRawSingularRestrictionConeCohomologyEquivRelative R X A n).symm a
  let v := (((CochainComplex.mappingCone g).sc ((n : ℤ) - 1)).mapHomologyIso F).hom
    (HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.mapHomologicalComplexIso g F).inv ((n : ℤ) - 1)
      (HomologicalComplex.homologyMap (globalRawSingularRestrictionConeIsoRelative R X A).hom
        ((n : ℤ) - 1) w))
  have ha : (relativeCochainConeHomologyIsoDualRelativeInt R (TopPair.ofSubset A) n).hom v =
      (relativeDualCochainCohomologyEquiv R (TopPair.ofSubset A) n).symm a := by
    apply (relativeDualCochainCohomologyEquiv R (TopPair.ofSubset A) n).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (globalRawSingularRestrictionConeCohomologyEquivRelative R X A n).apply_symm_apply a
  apply eX.addCommGroupIsoToAddEquiv.injective
  apply eA.addCommGroupIsoToAddEquiv.injective
  have hh := ConcreteCategory.congr_hom
    (globalRawSingularRestrictionCone_signed_inclusion R X A n) w
  change eA.hom (eX.hom (_)) =
    -(HomologicalComplex.homologyMap S.f (n : ℤ)
      ((relativeCochainConeHomologyIsoDualRelativeInt R (TopPair.ofSubset A) n).hom v)) at hh
  rw [ha] at hh
  change eA.hom (eX.hom (_)) = eA.hom (eX.hom (-(eX.inv (eA.inv _))))
  simp only [map_neg, ← ConcreteCategory.comp_apply, Iso.inv_hom_id,
    ConcreteCategory.id_apply]
  exact hh

end AlgebraicTopology.Singular
