/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularCochainOpenCone
public import Other.AlgebraicTopology.RelativeCochainConeBoundaryComparison
public import Other.Algebra.Homology.DerivedCategory.MappingConeMapNaturality

/-!
# Positive boundary normalization of raw open relative cohomology

The raw open relative-cone comparison preserves the positive dual-cochain
boundary through the literal cochain and coefficient-forgetting identifications.
The legacy comparison gives the same value on boundary classes.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace AlgebraicTopology.Singular
variable (R : Type) [Field R] (X : TopCat.{0}) {V W : Opens X} (i : W ⟶ V)

/-- On the complement, the actual raw cochains have the standard dual-cochain
cohomology, through the prescribed grading and coefficient-forgetting maps. -/
def openRawCochainHomologyEquivDual (V : Opens X) (n : ℤ) :
    ((openRawSingularCochainComplex R X V).extend ComplexShape.embeddingUpNat).homology n ≃+
    ((SingularChainComplex R (TopCat.of V)).linearDualCochainComplex.extend
      ComplexShape.embeddingUpNat).homology n :=
  (HomologicalComplex.homologyMapIso
    (openRawSingularCochainComplexIntIsoDual R X V) n).addCommGroupIsoToAddEquiv |>.trans
    (((((SingularChainComplex R (TopCat.of V)).linearDualCochainComplex.extend
      ComplexShape.embeddingUpNat).sc n).mapHomologyIso
      (forget₂ (ModuleCat R) AddCommGrpCat)).addCommGroupIsoToAddEquiv)

lemma openRawSingularRestrictionConeIsoRelative_inr :
    CochainComplex.mappingCone.inr
      (HomologicalComplex.extendMap (openRawSingularRestriction R X i)
        ComplexShape.embeddingUpNat) ≫
      (openRawSingularRestrictionConeIsoRelative R X i).hom =
    (openRawSingularCochainComplexIntIsoDual R X W).hom ≫
      CochainComplex.mappingCone.inr
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
          (relativeCochainRestrictionInt R (openInclusionPair X i))) := by
  simp [openRawSingularRestrictionConeIsoRelative,
    HomologicalComplex.homotopyCofiber.mapArrowIso,
    HomologicalComplex.homotopyCofiber.mapArrowHom, CochainComplex.mappingCone.inr]

/-- The canonical raw relative comparison preserves the positive dual-cochain boundary. -/
lemma openRawSingularRestrictionConeCohomologyEquivRelative_boundary (n : ℕ)
    (z : ((openRawSingularCochainComplex R X W).extend
      ComplexShape.embeddingUpNat).homology ((n : ℤ) - 1)) :
    openRawSingularRestrictionConeCohomologyEquivRelative R X i n
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr
          (HomologicalComplex.extendMap (openRawSingularRestriction R X i)
            ComplexShape.embeddingUpNat)) ((n : ℤ) - 1) z) =
    relativeCochainConeCohomologyEquivCanonical R (openInclusionPair X i) n
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr
          (relativeCochainRestrictionInt R (openInclusionPair X i))) ((n : ℤ) - 1)
        (openRawCochainHomologyEquivDual R X W ((n : ℤ) - 1) z)) := by
  let F := forget₂ (ModuleCat R) AddCommGrpCat
  let g := relativeCochainRestrictionInt R (openInclusionPair X i)
  let m := (n : ℤ) - 1
  let eR := openRawSingularRestrictionConeIsoRelative R X i
  let eF := CochainComplex.mappingCone.mapHomologicalComplexIso g F
  let eW := openRawSingularCochainComplexIntIsoDual R X W
  let eH := ((CochainComplex.mappingCone g).sc m).mapHomologyIso F
  let eWH := (((relativeDualCochainShortComplexInt R (openInclusionPair X i)).X₃).sc m).mapHomologyIso F
  let k := CochainComplex.mappingCone.inr
    (HomologicalComplex.extendMap (openRawSingularRestriction R X i) ComplexShape.embeddingUpNat)
  have hc : (k ≫ eR.hom) ≫ eF.inv =
      eW.hom ≫ (F.mapHomologicalComplex (.up ℤ)).map (CochainComplex.mappingCone.inr g) := by
    apply (cancel_mono eF.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [CochainComplex.mappingCone.map_inr]
    exact openRawSingularRestrictionConeIsoRelative_inr R X i
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (.up ℤ) m).map
      (CochainComplex.mappingCone.inr g)) F
  change HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map (CochainComplex.mappingCone.inr g)) m ≫ eH.hom =
    eWH.hom ≫ F.map (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr g) m) at hn
  have hh : HomologicalComplex.homologyMap k m ≫
      HomologicalComplex.homologyMap eR.hom m ≫
      HomologicalComplex.homologyMap eF.inv m ≫ eH.hom =
    HomologicalComplex.homologyMap eW.hom m ≫ eWH.hom ≫
      F.map (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr g) m) := by
    rw [← Category.assoc, ← Category.assoc, ← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp, hc,
      HomologicalComplex.homologyMap_comp, Category.assoc, hn]
  exact congrArg (relativeCochainConeCohomologyEquivCanonical R (openInclusionPair X i) n)
    (ConcreteCategory.congr_hom hh z)

/-- The same boundary calculation uses the legacy relative comparison as well,
because the two prescribed relative comparisons agree on boundary classes. -/
lemma openRawSingularRestrictionConeCohomologyEquivRelative_boundary_legacy (n : ℕ)
    (z : ((openRawSingularCochainComplex R X W).extend
      ComplexShape.embeddingUpNat).homology ((n : ℤ) - 1)) :
    openRawSingularRestrictionConeCohomologyEquivRelative R X i n
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr
          (HomologicalComplex.extendMap (openRawSingularRestriction R X i)
            ComplexShape.embeddingUpNat)) ((n : ℤ) - 1) z) =
    relativeCochainConeCohomologyEquiv R (openInclusionPair X i) n
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr
          (relativeCochainRestrictionInt R (openInclusionPair X i))) ((n : ℤ) - 1)
        (openRawCochainHomologyEquivDual R X W ((n : ℤ) - 1) z)) := by
  rw [openRawSingularRestrictionConeCohomologyEquivRelative_boundary,
    relativeCochainConeCohomologyEquiv_eq_canonical_of_boundary]

/-- Restricting literal raw cochains corresponds to the actual dual of inclusion,
under the prescribed open cochain and coefficient-forgetting comparisons. -/
lemma openRawCochainHomologyEquivDual_restriction (n : ℤ)
    (z : ((openRawSingularCochainComplex R X V).extend
      ComplexShape.embeddingUpNat).homology n) :
    openRawCochainHomologyEquivDual R X W n
      (HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap (openRawSingularRestriction R X i)
          ComplexShape.embeddingUpNat) n z) =
    HomologicalComplex.homologyMap (relativeCochainRestrictionInt R (openInclusionPair X i)) n
      (openRawCochainHomologyEquivDual R X V n z) := by
  let F := forget₂ (ModuleCat R) AddCommGrpCat
  let g := relativeCochainRestrictionInt R (openInclusionPair X i)
  let eV := openRawSingularCochainComplexIntIsoDual R X V
  let eW := openRawSingularCochainComplexIntIsoDual R X W
  let eVH := (((SingularChainComplex R (TopCat.of V)).linearDualCochainComplex.extend
    ComplexShape.embeddingUpNat).sc n).mapHomologyIso F
  let eWH := (((SingularChainComplex R (TopCat.of W)).linearDualCochainComplex.extend
    ComplexShape.embeddingUpNat).sc n).mapHomologyIso F
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (.up ℤ) n).map g) F
  change HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map g) n ≫ eWH.hom =
    eVH.hom ≫ F.map (HomologicalComplex.homologyMap g n) at hn
  have hc := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (openRawSingularRestrictionInt_transport R X i)
  simp only [HomologicalComplex.homologyMap_comp] at hc
  have h : (HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap (openRawSingularRestriction R X i)
        ComplexShape.embeddingUpNat) n ≫ HomologicalComplex.homologyMap eW.hom n) ≫ eWH.hom =
    HomologicalComplex.homologyMap eV.hom n ≫ eVH.hom ≫
      F.map (HomologicalComplex.homologyMap g n) := by
    rw [hc, Category.assoc, hn]
  exact ConcreteCategory.congr_hom h z

end AlgebraicTopology.Singular
