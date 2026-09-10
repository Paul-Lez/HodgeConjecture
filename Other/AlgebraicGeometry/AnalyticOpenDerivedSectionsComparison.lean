/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticTransitionCoboundary
public import Other.AlgebraicGeometry.HypercohomologyGlobalSectionsNaturality
public import Other.AlgebraicTopology.DerivedSheafSupportLocalization

/-!
# Derived morphisms from a free analytic open and cohomology on that open

The free abelian sheaf represented by an analytic open `U` represents sections
on `U`.  Degreewise, this identifies the Hom complex out of that sheaf with the
actual complex of sections on `U`.  For a K-injective target this gives the
derived comparison needed to turn relative Cech/Yoneda classes into open-set
cohomology classes before applying a localization boundary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec (.of ℂ)))

local instance analyticOpenDerivedSectionsSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

/-- The free sheaf on `U`, placed in cohomological degree zero. -/
def analyticOpenFreeSingleComplex
    (U : Opens (TopCat.of (ComplexPoint X))) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
    (analyticOpenFreeAbelianSheaf X U)

/-- The additive represented-section equivalence, natural in the target sheaf. -/
def analyticOpenFreeHomIsoSectionsFunctor
    (U : Opens (TopCat.of (ComplexPoint X))) :
    preadditiveCoyoneda.obj (.op (analyticOpenFreeAbelianSheaf X U)) ≅
      TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) U :=
  NatIso.ofComponents
    (fun F ↦ (analyticSectionSheafHomEquiv X F U).symm.toAddCommGrpIso)
    (fun {F G} f ↦ by
      apply AddCommGrpCat.hom_ext
      ext g
      simp only [AddCommGrpCat.comp_apply]
      let g' : analyticOpenFreeAbelianSheaf X U ⟶ F := g
      change (analyticSectionSheafHomEquiv X G U).symm (g' ≫ f) =
        f.hom.app (.op U) ((analyticSectionSheafHomEquiv X F U).symm g')
      apply (analyticSectionSheafHomEquiv X G U).injective
      rw [AddEquiv.apply_symm_apply]
      exact (congrArg (fun h : analyticOpenFreeAbelianSheaf X U ⟶ F ↦ h ≫ f)
        ((analyticSectionSheafHomEquiv X F U).apply_symm_apply g')).symm.trans
          (analyticSectionSheafHom_postcomp X F G f U _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The Hom complex out of the degree-zero free-open sheaf is canonically the
actual section complex on that open. -/
def homComplexSingleOpenFreeIsoSections
    (U : Opens (TopCat.of (ComplexPoint X)))
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) :
    CochainComplex.HomComplex (analyticOpenFreeSingleComplex X U) K ≅
      ((TopCat.Sheaf.supportEvaluation
        (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).obj K := by
  let pre := (inferInstance : Preadditive (AnalyticAdditiveSheaf X))
  letI : Preadditive (AnalyticAdditiveSheaf X) := pre
  let : (TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) U).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  exact CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda
      (analyticOpenFreeAbelianSheaf X U) K ≪≫
    (NatIso.mapHomologicalComplex (analyticOpenFreeHomIsoSectionsFunctor X U)
      (.up ℤ)).app K

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The Hom-complex/open-sections identification commutes with a map of
coefficient complexes. -/
@[reassoc]
lemma homComplexSingleOpenFreeIsoSections_naturality
    (U : Opens (TopCat.of (ComplexPoint X)))
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) :
    CochainComplex.HomComplex.postcompMap
        (analyticOpenFreeSingleComplex X U) f ≫
      (homComplexSingleOpenFreeIsoSections X U L).hom =
    (homComplexSingleOpenFreeIsoSections X U K).hom ≫
      ((TopCat.Sheaf.supportEvaluation
        (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).map f := by
  let e := NatIso.mapHomologicalComplex
    (analyticOpenFreeHomIsoSectionsFunctor X U) (.up ℤ)
  have h := CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda_naturality_assoc
    (analyticOpenFreeAbelianSheaf X U) f (e.hom.app L)
  have h' := congrArg (fun g =>
    (CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda
      (analyticOpenFreeAbelianSheaf X U) K).hom ≫ g)
      (e.hom.naturality f)
  exact h.trans (h'.trans (Category.assoc _ _ _).symm)

/-- A closed map out of the free sheaf on `U`, interpreted directly as an
actual class in the section complex.  Unlike the derived presentation below,
this construction does not require the target complex to be K-injective. -/
def openSectionCohomologyClassOfClosedMap
    (U : Opens (TopCat.of (ComplexPoint X)))
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    (q : ℤ) (f : analyticOpenFreeAbelianSheaf X U ⟶ K.X q)
    (hf : f ≫ K.d q (q + 1) = 0) :
    (((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).obj K).homology q :=
  (HomologicalComplex.homologyMapIso
      (homComplexSingleOpenFreeIsoSections X U K) q).hom
    ((CochainComplex.HomComplex.homologyAddEquiv
      (analyticOpenFreeSingleComplex X U) K q).symm
      (CochainComplex.HomComplex.CohomologyClass.mk
        (CochainComplex.HomComplex.Cocycle.fromSingleMk f
          (show 0 + q = q by omega) (q + 1) rfl hf)))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The direct open-section class commutes with a map of coefficient
complexes. -/
theorem openSectionCohomologyClassOfClosedMap_postcomp
    (U : Opens (TopCat.of (ComplexPoint X)))
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (g : K ⟶ L)
    (q : ℤ) (f : analyticOpenFreeAbelianSheaf X U ⟶ K.X q)
    (hf : f ≫ K.d q (q + 1) = 0) :
    openSectionCohomologyClassOfClosedMap X U L q (f ≫ g.f q) (by
        calc
          (f ≫ g.f q) ≫ L.d q (q + 1) =
              f ≫ (g.f q ≫ L.d q (q + 1)) := Category.assoc _ _ _
          _ = f ≫ (K.d q (q + 1) ≫ g.f (q + 1)) :=
            congrArg (fun t : K.X q ⟶ L.X (q + 1) => f ≫ t)
              (g.comm q (q + 1))
          _ = (f ≫ K.d q (q + 1)) ≫ g.f (q + 1) :=
            (Category.assoc _ _ _).symm
          _ = 0 := by rw [hf, zero_comp]) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.supportEvaluation
          (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).map g) q
        (openSectionCohomologyClassOfClosedMap X U K q f hf) := by
  let z : CochainComplex.HomComplex.Cocycle
      (analyticOpenFreeSingleComplex X U) K q :=
    CochainComplex.HomComplex.Cocycle.fromSingleMk f
      (show 0 + q = q by omega) (q + 1) rfl hf
  let x := (CochainComplex.HomComplex.homologyAddEquiv
    (analyticOpenFreeSingleComplex X U) K q).symm
      (CochainComplex.HomComplex.CohomologyClass.mk z)
  have hx :
      (CochainComplex.HomComplex.homologyAddEquiv
        (analyticOpenFreeSingleComplex X U) L q).symm
          (CochainComplex.HomComplex.CohomologyClass.mk (z.postcomp g)) =
        HomologicalComplex.homologyMap
          (CochainComplex.HomComplex.postcompMap
            (analyticOpenFreeSingleComplex X U) g) q x := by
    apply (CochainComplex.HomComplex.homologyAddEquiv
      (analyticOpenFreeSingleComplex X U) L q).injective
    rw [AddEquiv.apply_symm_apply,
      CochainComplex.HomComplex.homologyAddEquiv_postcompMap]
    simp only [x, AddEquiv.apply_symm_apply,
      CochainComplex.HomComplex.postcompClass_mk]
  have he := congrArg (fun h => HomologicalComplex.homologyMap h q)
    (homComplexSingleOpenFreeIsoSections_naturality X U g)
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp] at he
  have hex := ConcreteCategory.congr_hom he x
  unfold openSectionCohomologyClassOfClosedMap
  change (HomologicalComplex.homologyMap
      (homComplexSingleOpenFreeIsoSections X U L).hom q)
      ((CochainComplex.HomComplex.homologyAddEquiv
        (analyticOpenFreeSingleComplex X U) L q).symm
        (CochainComplex.HomComplex.CohomologyClass.mk _)) = _
  rw [show CochainComplex.HomComplex.Cocycle.fromSingleMk (f ≫ g.f q)
      (show 0 + q = q by omega) (q + 1) rfl _ = z.postcomp g by
    exact CochainComplex.HomComplex.Cocycle.fromSingleMk_postcomp
      f (show 0 + q = q by omega) (q + 1) rfl hf g]
  rw [hx]
  exact hex

/-- Derived morphisms from the free-open sheaf into a K-injective complex are
computed by actual cohomology of sections on that open. -/
def derivedHomAddEquivOpenSectionsKInjective
    (U : Opens (TopCat.of (ComplexPoint X)))
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsKInjective]
    (n : ℤ) :
    ShiftedHom
      (DerivedCategory.Q.obj (analyticOpenFreeSingleComplex X U))
      (DerivedCategory.Q.obj K) n ≃+
      (((TopCat.Sheaf.supportEvaluation
        (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).obj K).homology n :=
  (kInjectiveDerivedHomAddEquivCohomologyClass
      (analyticOpenFreeSingleComplex X U) K n).trans
    ((CochainComplex.HomComplex.homologyAddEquiv
      (analyticOpenFreeSingleComplex X U) K n).symm.trans
      (HomologicalComplex.homologyMapIso
        (homComplexSingleOpenFreeIsoSections X U K) n).addCommGroupIsoToAddEquiv)

/-- A closed degree-`q` morphism from the free sheaf on `U` determines an
actual class in degree `q` cohomology of the section complex on `U`. -/
def openCohomologyClassOfClosedMap
    (U : Opens (TopCat.of (ComplexPoint X)))
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsKInjective]
    (q : ℤ) (f : analyticOpenFreeAbelianSheaf X U ⟶ K.X q)
    (hf : f ≫ K.d q (q + 1) = 0) :
    (((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).obj K).homology q :=
  derivedHomAddEquivOpenSectionsKInjective X U K q
    ((kInjectiveDerivedHomAddEquivCohomologyClass
      (analyticOpenFreeSingleComplex X U) K q).symm
      (CochainComplex.HomComplex.CohomologyClass.mk
        (CochainComplex.HomComplex.Cocycle.fromSingleMk f
          (show 0 + q = q by omega) (q + 1) rfl hf)))

end AlgebraicGeometry.ComplexPoint
