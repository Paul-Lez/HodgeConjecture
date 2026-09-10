/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.BettiScalarComparison
public import Other.AlgebraicGeometry.HypercohomologyFlasqueMapNaturality
public import Other.AlgebraicTopology.SingularCochainCoefficientChange
public import Other.Algebra.Homology.MapExtendNaturality

/-!
# Naturality of the scalar Betti comparison in the coefficient ring

The identification of constant-sheaf cohomology with coefficients in `R` with ordinary singular
cohomology with coefficients in `R` is natural in `R`: a ring homomorphism `f : R →+* S` acts
on the sheaf-theoretic side through the constant sheaf morphism `constantCoefficientSheafMap`,
and on the singular side through postcomposition with `f` on cochains. This file proves that
the comparison equivalences intertwine these two actions, one naturality square per factor of
the comparison.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicTopology.Singular.HereditarilyParacompact

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
  (Y : TopCat.{0}) [ParacompactSpace Y] [T2Space Y] (n : ℕ)

/-- The identification of ordinary singular cohomology with the cohomology of global sections
of the singular-cochain sheaf complex is compatible with change of coefficients. -/
lemma ordinaryScalarSingularCohomologyEquivGlobalSections_coefficientChange
    (a : OrdinarySingularCohomology R Y n) :
    ordinaryScalarSingularCohomologyEquivGlobalSections S Y n
        (ordinarySingularCohomologyCoefficientChange f Y n a) =
      HomologicalComplex.homologyMap (globalSingularCochainSheafComplexMap f Y) n
        (ordinaryScalarSingularCohomologyEquivGlobalSections R Y n a) := by
  simp only [ordinaryScalarSingularCohomologyEquivGlobalSections, AddEquiv.trans_apply,
    Iso.addCommGroupIsoToAddEquiv_apply, asIso_hom]
  rw [ordinarySingularCohomologyEquivGlobalRaw_coefficientChange,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    topOpenToGlobalSingularCochainSheafComplex_comp_map]

/-- The inverse form of `ordinaryScalarSingularCohomologyEquivGlobalSections_coefficientChange`. -/
lemma ordinaryScalarSingularCohomologyEquivGlobalSections_symm_coefficientChange
    (b : (globalSingularCochainSheafComplex R Y).homology n) :
    (ordinaryScalarSingularCohomologyEquivGlobalSections S Y n).symm
        (HomologicalComplex.homologyMap (globalSingularCochainSheafComplexMap f Y) n b) =
      ordinarySingularCohomologyCoefficientChange f Y n
        ((ordinaryScalarSingularCohomologyEquivGlobalSections R Y n).symm b) := by
  rw [AddEquiv.symm_apply_eq,
    ordinaryScalarSingularCohomologyEquivGlobalSections_coefficientChange,
    AddEquiv.apply_symm_apply]

end AlgebraicTopology.Singular.HereditarilyParacompact

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)

/-- Step 1: the postcomposition equivalence along the constant-to-singular resolution is
natural in the coefficient ring. -/
lemma scalarCohomologySingularCochainEquiv_coefficientChange
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) (α : ScalarCohomology X R n) :
    scalarCohomologySingularCochainEquiv X S n
        (hypercohomologyMap X (constantCoefficientSheafComplexIntMap X f) n α) =
      hypercohomologyMap X (singularCochainSheafComplexIntMap X f) n
        (scalarCohomologySingularCochainEquiv X R n α) := by
  rw [scalarCohomologySingularCochainEquiv_apply, scalarCohomologySingularCochainEquiv_apply,
    ← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply,
    constantsToSingularCochainComplexInt_comp_map]

/-- Step 2: the flasque global-sections comparison is natural in the coefficient ring. -/
lemma scalarSingularCochainHypercohomologyAddEquivGlobalSections_coefficientChange
    [T2Space (ComplexPoint X)] [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) (a : ScalarSingularCochainHypercohomology X R n) :
    scalarSingularCochainHypercohomologyAddEquivGlobalSections X S n
        (hypercohomologyMap X (singularCochainSheafComplexIntMap X f) n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (singularCochainSheafComplexIntMap X f)) n
        (scalarSingularCochainHypercohomologyAddEquivGlobalSections X R n a) := by
  let : (singularCochainSheafComplexInt X R).IsStrictlyGE 0 := by
    dsimp [singularCochainSheafComplexInt]
    infer_instance
  let : (singularCochainSheafComplexInt X S).IsStrictlyGE 0 := by
    dsimp [singularCochainSheafComplexInt]
    infer_instance
  exact hypercohomologyAddEquivGlobalSections_naturality X
    (singularCochainSheafComplexInt X R) (singularCochainSheafComplexInt X S) 0
    (singularCochainSheafComplexInt_isFlasque_scalar X R)
    (singularCochainSheafComplexInt_isFlasque_scalar X S)
    (singularCochainSheafComplexIntMap X f) n a

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Step 3, at the level of complexes: the identification of global sections of the extended
singular-cochain sheaf complex with the extension of the global-section complex is natural in
the coefficient ring. -/
lemma globalSectionsSingularCochainComplexIntIsoExtend_scalar_naturality :
    ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
          (singularCochainSheafComplexIntMap X f) ≫
        (globalSectionsSingularCochainComplexIntIsoExtend_scalar X S).hom =
      (globalSectionsSingularCochainComplexIntIsoExtend_scalar X R).hom ≫
        HomologicalComplex.extendMap
          (AlgebraicTopology.Singular.globalSingularCochainSheafComplexMap f
            (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat := by
  let Y := TopCat.of (ComplexPoint X)
  let F := TopCat.Sheaf.forget AddCommGrpCat Y
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)
  let G := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let g := AlgebraicTopology.Singular.singularCochainSheafComplexMap f Y
  let e := ComplexShape.embeddingUpNat
  let : F.Additive := by dsimp [F]; infer_instance
  let : E.Additive := by dsimp [E]; infer_instance
  let eComp : F ⋙ E ≅ G := Iso.refl _
  let ι := (Functor.mapHomologicalComplexCompIso eComp (ComplexShape.up ℕ)).inv
  change (G.mapHomologicalComplex (.up ℤ)).map (HomologicalComplex.extendMap g e) ≫
      (HomologicalComplex.mapExtendIso G
        (AlgebraicTopology.Singular.singularCochainSheafComplex S Y) e).hom ≫
        HomologicalComplex.extendMap
          (ι.app (AlgebraicTopology.Singular.singularCochainSheafComplex S Y)) e =
    ((HomologicalComplex.mapExtendIso G
        (AlgebraicTopology.Singular.singularCochainSheafComplex R Y) e).hom ≫
        HomologicalComplex.extendMap
          (ι.app (AlgebraicTopology.Singular.singularCochainSheafComplex R Y)) e) ≫
      HomologicalComplex.extendMap
        ((F.mapHomologicalComplex (.up ℕ) ⋙ E.mapHomologicalComplex (.up ℕ)).map g) e
  have h1 := HomologicalComplex.mapExtendIso_inv_naturality G g e
  rw [Iso.comp_inv_eq] at h1
  have h2 := ι.naturality g
  simp only [Category.assoc]
  rw [← HomologicalComplex.extendMap_comp, ← h2, HomologicalComplex.extendMap_comp, h1]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Step 3, on homology. -/
lemma homologyMapIso_globalSectionsSingularCochainComplexIntIsoExtend_scalar_coefficientChange
    (n : ℤ)
    (a : (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
      (singularCochainSheafComplexInt X R)).homology n) :
    (HomologicalComplex.homologyMapIso
        (globalSectionsSingularCochainComplexIntIsoExtend_scalar X S) n).hom
      (HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (singularCochainSheafComplexIntMap X f)) n a) =
      HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap
          (AlgebraicTopology.Singular.globalSingularCochainSheafComplexMap f
            (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat) n
        ((HomologicalComplex.homologyMapIso
          (globalSectionsSingularCochainComplexIntIsoExtend_scalar X R) n).hom a) := by
  have h : HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (singularCochainSheafComplexIntMap X f)) n ≫
        HomologicalComplex.homologyMap
          (globalSectionsSingularCochainComplexIntIsoExtend_scalar X S).hom n =
      HomologicalComplex.homologyMap
          (globalSectionsSingularCochainComplexIntIsoExtend_scalar X R).hom n ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap
            (AlgebraicTopology.Singular.globalSingularCochainSheafComplexMap f
              (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      globalSectionsSingularCochainComplexIntIsoExtend_scalar_naturality]
  exact ConcreteCategory.congr_hom h a

/-- Step 4: the extension-by-zero homology isomorphism is natural in the coefficient ring. -/
lemma extendHomologyIso_globalSingularCochainSheafComplex_coefficientChange (n : ℕ)
    (a : ((AlgebraicTopology.Singular.globalSingularCochainSheafComplex R
      (TopCat.of (ComplexPoint X))).extend ComplexShape.embeddingUpNat).homology (n : ℤ)) :
    ((AlgebraicTopology.Singular.globalSingularCochainSheafComplex S
        (TopCat.of (ComplexPoint X))).extendHomologyIso ComplexShape.embeddingUpNat
          (j := n) (j' := (n : ℤ)) rfl).hom
      (HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap
          (AlgebraicTopology.Singular.globalSingularCochainSheafComplexMap f
            (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat) (n : ℤ) a) =
      HomologicalComplex.homologyMap
        (AlgebraicTopology.Singular.globalSingularCochainSheafComplexMap f
          (TopCat.of (ComplexPoint X))) n
        (((AlgebraicTopology.Singular.globalSingularCochainSheafComplex R
          (TopCat.of (ComplexPoint X))).extendHomologyIso
            ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).hom a) := by
  have h := HomologicalComplex.extendHomologyIso_hom_naturality
    (AlgebraicTopology.Singular.globalSingularCochainSheafComplexMap f
      (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, h]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Steps 2 to 5 assembled: the identification of singular-cochain hypercohomology with
ordinary singular cohomology is natural in the coefficient ring. -/
lemma scalarSingularCochainHypercohomologyEquivOrdinaryCohomology_coefficientChange
    [T2Space (ComplexPoint X)] [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) (a : ScalarSingularCochainHypercohomology X R (n : ℤ)) :
    scalarSingularCochainHypercohomologyEquivOrdinaryCohomology X S n
        (hypercohomologyMap X (singularCochainSheafComplexIntMap X f) (n : ℤ) a) =
      AlgebraicTopology.Singular.ordinarySingularCohomologyCoefficientChange f
        (TopCat.of (ComplexPoint X)) n
        (scalarSingularCochainHypercohomologyEquivOrdinaryCohomology X R n a) := by
  let : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  change (AlgebraicTopology.Singular.HereditarilyParacompact.ordinaryScalarSingularCohomologyEquivGlobalSections
        S (TopCat.of (ComplexPoint X)) n).symm
      (((AlgebraicTopology.Singular.globalSingularCochainSheafComplex S
        (TopCat.of (ComplexPoint X))).extendHomologyIso ComplexShape.embeddingUpNat
          (j := n) (j' := (n : ℤ)) rfl).hom
        ((HomologicalComplex.homologyMapIso
          (globalSectionsSingularCochainComplexIntIsoExtend_scalar X S) (n : ℤ)).hom
          (scalarSingularCochainHypercohomologyAddEquivGlobalSections X S (n : ℤ)
            (hypercohomologyMap X (singularCochainSheafComplexIntMap X f) (n : ℤ) a)))) =
    AlgebraicTopology.Singular.ordinarySingularCohomologyCoefficientChange f
      (TopCat.of (ComplexPoint X)) n
      ((AlgebraicTopology.Singular.HereditarilyParacompact.ordinaryScalarSingularCohomologyEquivGlobalSections
        R (TopCat.of (ComplexPoint X)) n).symm
        (((AlgebraicTopology.Singular.globalSingularCochainSheafComplex R
          (TopCat.of (ComplexPoint X))).extendHomologyIso ComplexShape.embeddingUpNat
            (j := n) (j' := (n : ℤ)) rfl).hom
          ((HomologicalComplex.homologyMapIso
            (globalSectionsSingularCochainComplexIntIsoExtend_scalar X R) (n : ℤ)).hom
            (scalarSingularCochainHypercohomologyAddEquivGlobalSections X R (n : ℤ) a))))
  rw [scalarSingularCochainHypercohomologyAddEquivGlobalSections_coefficientChange,
    homologyMapIso_globalSectionsSingularCochainComplexIntIsoExtend_scalar_coefficientChange,
    extendHomologyIso_globalSingularCochainSheafComplex_coefficientChange,
    AlgebraicTopology.Singular.HereditarilyParacompact.ordinaryScalarSingularCohomologyEquivGlobalSections_symm_coefficientChange]

/-- The comparison between constant-sheaf cohomology and ordinary singular cohomology is
natural in the coefficient ring. -/
theorem scalarCohomologyEquivOrdinarySingularCohomology_coefficientChange
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)] [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) (α : ScalarCohomology X R n) :
    scalarCohomologyEquivOrdinarySingularCohomology X S n
        (hypercohomologyMap X (constantCoefficientSheafComplexIntMap X f) n α) =
      AlgebraicTopology.Singular.ordinarySingularCohomologyCoefficientChange f
        (TopCat.of (ComplexPoint X)) n
        (scalarCohomologyEquivOrdinarySingularCohomology X R n α) := by
  simp only [scalarCohomologyEquivOrdinarySingularCohomology, Equiv.trans_apply]
  rw [scalarCohomologySingularCochainEquiv_coefficientChange,
    scalarSingularCochainHypercohomologyEquivOrdinaryCohomology_coefficientChange]

end AlgebraicGeometry.ComplexPoint
