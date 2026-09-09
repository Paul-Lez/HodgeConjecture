/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularCochainOpenCone
public import Other.AlgebraicTopology.GlobalRawRelativeConnecting

/-! # Exact ordinary normalization of the canonical open relative comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicTopology.Singular

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (R : Type) [Field R] (X : TopCat.{0}) {V W : Opens X} (i : W ⟶ V)

/-- The local raw cone's actual comparison preserves the connecting projection. -/
@[reassoc]
theorem openRawSingularRestrictionConeIsoRelative_connecting :
    (openRawSingularRestrictionConeIsoRelative R X i).hom ≫
      (CochainComplex.mappingCone.triangle
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
          (relativeCochainRestrictionInt R (openInclusionPair X i)))).mor₃ =
    (CochainComplex.mappingCone.triangle
      (HomologicalComplex.extendMap (openRawSingularRestriction R X i)
        ComplexShape.embeddingUpNat)).mor₃ ≫
      (openRawSingularCochainComplexIntIsoDual R X V).hom⟦(1 : ℤ)⟧' :=
  CochainComplex.mappingCone.homotopyCofiber_mapArrowIso_connecting _ _ _

set_option maxHeartbeats 800000 in
/-- The canonical open raw cone comparison has the same negative connecting
sign as its actual positive dual-relative inclusion. -/
theorem openRawSingularRestrictionCone_signed_inclusion (n : ℕ) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
        (CochainComplex.mappingCone.triangle
          (HomologicalComplex.extendMap (openRawSingularRestriction R X i)
            ComplexShape.embeddingUpNat)).mor₃ ((n : ℤ) - 1) (n : ℤ) (by omega) ≫
      HomologicalComplex.homologyMap (openRawSingularCochainComplexIntIsoDual R X V).hom
        (n : ℤ) ≫
      (((relativeDualCochainShortComplexInt R (openInclusionPair X i)).X₂.sc (n : ℤ)).mapHomologyIso
        (forget₂ (ModuleCat R) AddCommGrpCat)).hom =
    -(HomologicalComplex.homologyMap (openRawSingularRestrictionConeIsoRelative R X i).hom
        ((n : ℤ) - 1) ≫
      HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.mapHomologicalComplexIso
          (relativeCochainRestrictionInt R (openInclusionPair X i))
          (forget₂ (ModuleCat R) AddCommGrpCat)).inv ((n : ℤ) - 1) ≫
      (((CochainComplex.mappingCone
        (relativeCochainRestrictionInt R (openInclusionPair X i))).sc ((n : ℤ) - 1)).mapHomologyIso
          (forget₂ (ModuleCat R) AddCommGrpCat)).hom ≫
      (forget₂ (ModuleCat R) AddCommGrpCat).map
        ((relativeDualCochainHomologyIsoCone R (openInclusionPair X i) n).inv ≫
          HomologicalComplex.homologyMap
            (relativeDualCochainShortComplexInt R (openInclusionPair X i)).f (n : ℤ))) := by
  let F := forget₂ (ModuleCat R) AddCommGrpCat
  let g := relativeCochainRestrictionInt R (openInclusionPair X i)
  let eF := CochainComplex.mappingCone.mapHomologicalComplexIso g F
  let HD := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0
  have he := congrArg
    (fun f => HD.shiftMap f ((n : ℤ) - 1) (n : ℤ) (show (1 : ℤ) + ((n : ℤ) - 1) = n by omega))
    (openRawSingularRestrictionConeIsoRelative_connecting R X i)
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
  erw [← relativeCochainConeHomologyIsoDualRelativeInt_inclusion,
    relativeCochainCone_legacy_canonical_inclusion]
  simp only [Functor.map_neg, Preadditive.comp_neg]
  rfl

/-- Actual positive inclusion of a local relative class into raw cochains on V. -/
def openRawRelativeCochainClass (n : ℕ)
    (a : RelativeCohomology R (openInclusionPair X i) n) :
    ((openRawSingularCochainComplex R X V).extend ComplexShape.embeddingUpNat).homology (n : ℤ) :=
  (HomologicalComplex.homologyMapIso (openRawSingularCochainComplexIntIsoDual R X V)
    (n : ℤ)).inv
    ((((relativeDualCochainShortComplexInt R (openInclusionPair X i)).X₂.sc (n : ℤ)).mapHomologyIso
      (forget₂ (ModuleCat R) AddCommGrpCat)).inv
      (HomologicalComplex.homologyMap
        (relativeDualCochainShortComplexInt R (openInclusionPair X i)).f (n : ℤ)
          ((relativeDualCochainCohomologyEquiv R (openInclusionPair X i) n).symm a)))

set_option maxHeartbeats 1000000 in
/-- On a prescribed relative class, the canonical local cone connecting map is
the negative of its actual positive ordinary cochain class. -/
theorem openRawSingularRestrictionCone_connecting_of_relative (n : ℕ)
    (a : RelativeCohomology R (openInclusionPair X i) n) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
      (CochainComplex.mappingCone.triangle
        (HomologicalComplex.extendMap (openRawSingularRestriction R X i)
          ComplexShape.embeddingUpNat)).mor₃ ((n : ℤ) - 1) (n : ℤ) (by omega)
      ((openRawSingularRestrictionConeCohomologyEquivRelative R X i n).symm a) =
        -openRawRelativeCochainClass R X i n a := by
  let F := forget₂ (ModuleCat R) AddCommGrpCat
  let S := relativeDualCochainShortComplexInt R (openInclusionPair X i)
  let g := relativeCochainRestrictionInt R (openInclusionPair X i)
  let eX := HomologicalComplex.homologyMapIso
    (openRawSingularCochainComplexIntIsoDual R X V) (n : ℤ)
  let eA := (S.X₂.sc (n : ℤ)).mapHomologyIso F
  let w := (openRawSingularRestrictionConeCohomologyEquivRelative R X i n).symm a
  let v := (((CochainComplex.mappingCone g).sc ((n : ℤ) - 1)).mapHomologyIso F).hom
    (HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.mapHomologicalComplexIso g F).inv ((n : ℤ) - 1)
      (HomologicalComplex.homologyMap (openRawSingularRestrictionConeIsoRelative R X i).hom
        ((n : ℤ) - 1) w))
  have ha : (relativeDualCochainHomologyIsoCone R (openInclusionPair X i) n).inv v =
      (relativeDualCochainCohomologyEquiv R (openInclusionPair X i) n).symm a := by
    apply (relativeDualCochainCohomologyEquiv R (openInclusionPair X i) n).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (openRawSingularRestrictionConeCohomologyEquivRelative R X i n).apply_symm_apply a
  apply eX.addCommGroupIsoToAddEquiv.injective
  apply eA.addCommGroupIsoToAddEquiv.injective
  have hh := ConcreteCategory.congr_hom
    (openRawSingularRestrictionCone_signed_inclusion R X i n) w
  change eA.hom (eX.hom (_)) =
    -(HomologicalComplex.homologyMap S.f (n : ℤ)
      ((relativeDualCochainHomologyIsoCone R (openInclusionPair X i) n).inv v)) at hh
  rw [ha] at hh
  change eA.hom (eX.hom (_)) = eA.hom (eX.hom (-(eX.inv (eA.inv _))))
  simp only [map_neg, ← ConcreteCategory.comp_apply, Iso.inv_hom_id,
    ConcreteCategory.id_apply]
  exact hh

end AlgebraicTopology.Singular
