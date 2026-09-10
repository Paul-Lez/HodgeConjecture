/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.OpenRawRelativeConnecting
public import Other.AlgebraicTopology.SupportedSectionConeConnecting
public import HodgeConjecture.Definitions.AlgebraicTopology.SupportedSingularSectionCohomology

/-! # Positive ordinary normalization of actual supported singular sections -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicTopology.Singular

variable (X : TopCat.{0})

/-- The actual sheafification cone comparison sends the canonical relative
representative to its corresponding sheaf-cone representative. -/
theorem openSingularSheafRestrictionConeCohomologyEquivRelative_symm
    {V W : Opens X} (i : W ⟶ V) [ParacompactSpace V] [T2Space V]
    [ParacompactSpace W] [T2Space W] (n : ℕ)
    (a : RelativeCohomology ℚ (openInclusionPair X i) n) :
    (openSingularSheafRestrictionConeCohomologyEquivRelative X i n).symm a =
      HomologicalComplex.homologyMap (openRawToSingularSheafRestrictionCone ℚ X i)
        ((n : ℤ) - 1)
        ((openRawSingularRestrictionConeCohomologyEquivRelative ℚ X i n).symm a) := by
  let := openRawToSingularSheafRestrictionCone_quasiIso X i
  apply (openSingularSheafRestrictionConeCohomologyEquivRelative X i n).injective
  rw [AddEquiv.apply_symm_apply]
  change a = (openRawSingularRestrictionConeCohomologyEquivRelative ℚ X i n)
    (inv (HomologicalComplex.homologyMap (openRawToSingularSheafRestrictionCone ℚ X i)
      ((n : ℤ) - 1))
      (HomologicalComplex.homologyMap (openRawToSingularSheafRestrictionCone ℚ X i)
        ((n : ℤ) - 1) _))
  rw [← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply,
    AddEquiv.apply_symm_apply]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The actual local sheaf-cone connecting map is minus the raw relative
cochain inclusion followed by the literal sheafification unit. -/
theorem openSingularSheafRestrictionCone_connecting_of_relative
    {V W : Opens X} (i : W ⟶ V) [ParacompactSpace V] [T2Space V]
    [ParacompactSpace W] [T2Space W] (n : ℕ)
    (a : RelativeCohomology ℚ (openInclusionPair X i) n) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
      (CochainComplex.mappingCone.triangle
        (HomologicalComplex.extendMap (openSingularSheafRestriction ℚ X i)
          ComplexShape.embeddingUpNat)).mor₃ ((n : ℤ) - 1) (n : ℤ) (by omega)
      ((openSingularSheafRestrictionConeCohomologyEquivRelative X i n).symm a) =
    -(HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex ℚ X V)
        ComplexShape.embeddingUpNat) (n : ℤ)
      (openRawRelativeCochainClass ℚ X i n a)) := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0
  have hc := congrArg
    (fun f => H.shiftMap f ((n : ℤ) - 1) n (show (1 : ℤ) + ((n : ℤ) - 1) = n by omega))
    (openRawToSingularSheafRestrictionCone_connecting ℚ X i)
  rw [Functor.shiftMap_comp', Functor.shiftMap_comp] at hc
  rw [openSingularSheafRestrictionConeCohomologyEquivRelative_symm]
  have hh := ConcreteCategory.congr_hom hc
    ((openRawSingularRestrictionConeCohomologyEquivRelative ℚ X i n).symm a)
  exact hh.trans ((congrArg
    (HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex ℚ X V)
        ComplexShape.embeddingUpNat) (n : ℤ))
    (openRawSingularRestrictionCone_connecting_of_relative ℚ X i n a)).trans
      (map_neg _ _))

end AlgebraicTopology.Singular

namespace TopCat.Sheaf

/-- The literal grading comparison of open restriction cones preserves the
connecting map with its actual ambient-section grading isomorphism. -/
@[reassoc]
theorem sectionComplexRestrictionExtendConeIso_connecting (X : TopCat.{0})
    (K : CochainComplex (Sheaf AddCommGrpCat X) ℕ)
    {V W : Opens X} (i : W ⟶ V) :
    (sectionComplexRestrictionExtendConeIso X K i).hom ≫
      (CochainComplex.mappingCone.triangle
        (HomologicalComplex.extendMap (sectionComplexRestriction X (.up ℕ) K i)
          ComplexShape.embeddingUpNat)).mor₃ =
    (CochainComplex.mappingCone.triangle
      (sectionComplexRestriction X (.up ℤ) (K.extend ComplexShape.embeddingUpNat) i)).mor₃ ≫
      (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X V) K
        ComplexShape.embeddingUpNat).hom⟦(1 : ℤ)⟧' :=
  CochainComplex.mappingCone.homotopyCofiber_mapArrowIso_connecting _ _ _

end TopCat.Sheaf

namespace AlgebraicTopology.Singular

variable (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
  (U V : Opens X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- The actual supported singular section comparison has POSITIVE ordinary
normalization: its inverse followed by kernel inclusion is the actual positive
relative cochain inclusion followed by sheafification. -/
theorem supportedRationalSingularSectionCohomologyEquivRelative_inclusion (n : ℕ)
    (a : RelativeCohomology ℚ (openInclusionPair X (Opens.infLELeft V U)) n) :
    HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V
        (rationalSingularCochainComplex X)).f (n : ℤ)
      ((supportedRationalSingularSectionCohomologyEquivRelative X U V n).symm a) =
    HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex ℚ X V)
        ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.mapExtendCanonicalIso (TopCat.Sheaf.supportEvaluation X V)
          (singularCochainSheafComplex ℚ X) ComplexShape.embeddingUpNat).inv) (n : ℤ)
      (openRawRelativeCochainClass ℚ X (Opens.infLELeft V U) n a) := by
  let K := rationalSingularCochainComplex X
  let K₀ := singularCochainSheafComplex ℚ X
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V K
  let i := Opens.infLELeft V U
  let eK := TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone X U V K
    (fun _ => inferInstance) (n : ℤ)
  let eg := TopCat.Sheaf.sectionComplexRestrictionExtendConeIso X K₀ i
  let eV := HomologicalComplex.mapExtendCanonicalIso (TopCat.Sheaf.supportEvaluation X V)
    K₀ ComplexShape.embeddingUpNat
  let ev := HomologicalComplex.homologyMapIso eV (n : ℤ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0
  let x := (supportedRationalSingularSectionCohomologyEquivRelative X U V n).symm a
  have hx : HomologicalComplex.homologyMap eg.hom ((n : ℤ) - 1) (eK.hom x) =
      (openSingularSheafRestrictionConeCohomologyEquivRelative X i n).symm a := by
    apply (openSingularSheafRestrictionConeCohomologyEquivRelative X i n).injective
    rw [AddEquiv.apply_symm_apply]
    exact (supportedRationalSingularSectionCohomologyEquivRelative X U V n).apply_symm_apply a
  have hk := ConcreteCategory.congr_hom
    (TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone_connecting X U V K
      (fun _ => inferInstance) (n : ℤ)) x
  have hg := congrArg
    (fun f => H.shiftMap f ((n : ℤ) - 1) n (show (1 : ℤ) + ((n : ℤ) - 1) = n by omega))
    (TopCat.Sheaf.sectionComplexRestrictionExtendConeIso_connecting X K₀ i)
  rw [Functor.shiftMap_comp', Functor.shiftMap_comp] at hg
  have hge := ConcreteCategory.congr_hom hg (eK.hom x)
  change H.shiftMap _ ((n : ℤ) - 1) n (by omega)
      (HomologicalComplex.homologyMap eg.hom ((n : ℤ) - 1) (eK.hom x)) =
    ev.hom (H.shiftMap _ ((n : ℤ) - 1) n (by omega) (eK.hom x)) at hge
  rw [hx] at hge
  have hge' := (openSingularSheafRestrictionCone_connecting_of_relative X i n a).symm.trans hge
  change H.shiftMap _ ((n : ℤ) - 1) n (by omega) (eK.hom x) =
    -(HomologicalComplex.homologyMap S.f (n : ℤ) x) at hk
  have hge'' := hge'.trans (congrArg ev.hom hk)
  rw [map_neg] at hge''
  have he := neg_injective hge''
  apply ev.addCommGroupIsoToAddEquiv.injective
  change ev.hom (HomologicalComplex.homologyMap S.f (n : ℤ) x) = _
  rw [← he, HomologicalComplex.homologyMap_comp]
  change _ = ev.hom (ev.inv _)
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  rfl

end AlgebraicTopology.Singular
