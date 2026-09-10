/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticIteratedTransitionClass
public import Other.AlgebraicGeometry.AnalyticOpenDerivedSectionsComparison
public import Other.AlgebraicGeometry.DerivedGlobalHypercohomologyComparison

/-!
# Closed holomorphic forms on an analytic open

A closed holomorphic `p`-form on an arbitrary analytic open gives a cochain
map from the free sheaf on that open, placed in degree `p`, to both the full
and `p`-filtered de Rham complexes.  Composing with the fixed injective
augmentation gives the closed degree-`p` morphism used by relative Cech
localization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local instance analyticClosedOpenSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

/-- A closed `p`-form on `U` as a map to the full integer-indexed de Rham
complex. -/
def analyticClosedOpenSectionToDeRhamComplexInt
    (U : Opens (TopCat.of (ComplexPoint X))) {p : ℕ}
    (c : (holomorphicDeRhamSheaf X (dim X.left) p).obj.obj (.op U))
    (hc : (holomorphicDeRhamSheafDifferential X (dim X.left) p).hom.app
      (.op U) c = 0) :
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) (p : ℤ)).obj
        (analyticOpenFreeAbelianSheaf X U) ⟶
      holomorphicDeRhamComplexInt X :=
  HomologicalComplex.mkHomFromSingle
    (analyticSectionSheafHom X
        (holomorphicDeRhamSheaf X (dim X.left) p) U c ≫
      ((holomorphicDeRhamComplex X (dim X.left)).extendXIso
        ComplexShape.embeddingUpNat (i := p) rfl).inv) (by
      have hclosed :
          analyticSectionSheafHom X
              (holomorphicDeRhamSheaf X (dim X.left) p) U c ≫
            holomorphicDeRhamSheafDifferential X (dim X.left) p = 0 := by
        rw [analyticSectionSheafHom_postcomp, hc,
          analyticSectionSheafHom_zero]
      intro k hk
      have hk' : k = (p : ℤ) + 1 := by
        simpa [ComplexShape.up_Rel] using hk.symm
      subst k
      unfold holomorphicDeRhamComplexInt
      rw [HomologicalComplex.extend_d_eq
        (holomorphicDeRhamComplex X (dim X.left))
        ComplexShape.embeddingUpNat
        (i' := (p : ℤ)) (j' := (p : ℤ) + 1)
        (i := p) (j := p + 1) rfl (by simp)]
      simp only [Category.assoc]
      erw [Iso.inv_hom_id_assoc]
      rw [holomorphicDeRhamComplex_d]
      rw [← Category.assoc, hclosed, zero_comp])

/-- The closed open-section map factored through the `p`-th Hodge filtration. -/
def analyticClosedOpenSectionToFilteredDeRhamComplexInt
    (U : Opens (TopCat.of (ComplexPoint X))) {p : ℕ}
    (c : (holomorphicDeRhamSheaf X (dim X.left) p).obj.obj (.op U))
    (hc : (holomorphicDeRhamSheafDifferential X (dim X.left) p).hom.app
      (.op U) c = 0) :
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) (p : ℤ)).obj
        (analyticOpenFreeAbelianSheaf X U) ⟶
      hodgeFilteredDeRhamComplex X (p : ℤ) :=
  HomologicalComplex.liftStupidTrunc
    (ComplexShape.embeddingUpIntGE (p : ℤ))
    (analyticClosedOpenSectionToDeRhamComplexInt X U c hc)

/-- Forgetting the filtration recovers the original open-section map. -/
@[reassoc (attr := simp)]
theorem analyticClosedOpenSectionToFilteredDeRhamComplexInt_comp_inclusion
    (U : Opens (TopCat.of (ComplexPoint X))) {p : ℕ}
    (c : (holomorphicDeRhamSheaf X (dim X.left) p).obj.obj (.op U))
    (hc : (holomorphicDeRhamSheafDifferential X (dim X.left) p).hom.app
      (.op U) c = 0) :
    analyticClosedOpenSectionToFilteredDeRhamComplexInt X U c hc ≫
        hodgeFilteredDeRhamInclusion X (p : ℤ) =
      analyticClosedOpenSectionToDeRhamComplexInt X U c hc :=
  HomologicalComplex.liftStupidTrunc_inclusion _ _

local instance hodgeFilteredDeRhamComplex_isStrictlyGE_zero_open (p : ℕ) :
    (hodgeFilteredDeRhamComplex X (p : ℤ)).IsStrictlyGE 0 := by
  letI : (hodgeFilteredDeRhamComplex X (p : ℤ)).IsStrictlyGE (p : ℤ) := by
    unfold hodgeFilteredDeRhamComplex
    infer_instance
  exact (hodgeFilteredDeRhamComplex X (p : ℤ)).isStrictlyGE_of_ge
    0 (p : ℤ) (by omega)

/-- A closed `p`-form on `U`, represented directly in degree `p` of the fixed
injective model for `F^p Ω^*`. -/
def analyticClosedOpenSectionToFilteredInjectiveDegree
    (U : Opens (TopCat.of (ComplexPoint X))) {p : ℕ}
    (c : (holomorphicDeRhamSheaf X (dim X.left) p).obj.obj (.op U))
    (hc : (holomorphicDeRhamSheafDifferential X (dim X.left) p).hom.app
      (.op U) c = 0) :
    analyticOpenFreeAbelianSheaf X U ⟶
      (globalHypercohomologyInjectiveComplex X
        (hodgeFilteredDeRhamComplex X (p : ℤ))).X (p : ℤ) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) (p : ℤ)
      (analyticOpenFreeAbelianSheaf X U)).inv ≫
    (analyticClosedOpenSectionToFilteredDeRhamComplexInt X U c hc ≫
      globalHypercohomologyInjectiveMap X
        (hodgeFilteredDeRhamComplex X (p : ℤ))).f (p : ℤ)

/-- The fixed-injective representative of a closed open form is closed. -/
theorem analyticClosedOpenSectionToFilteredInjectiveDegree_closed
    (U : Opens (TopCat.of (ComplexPoint X))) {p : ℕ}
    (c : (holomorphicDeRhamSheaf X (dim X.left) p).obj.obj (.op U))
    (hc : (holomorphicDeRhamSheafDifferential X (dim X.left) p).hom.app
      (.op U) c = 0) :
    analyticClosedOpenSectionToFilteredInjectiveDegree X U c hc ≫
        (globalHypercohomologyInjectiveComplex X
          (hodgeFilteredDeRhamComplex X (p : ℤ))).d (p : ℤ) ((p : ℤ) + 1) = 0 := by
  rw [analyticClosedOpenSectionToFilteredInjectiveDegree]
  have hcomm := (analyticClosedOpenSectionToFilteredDeRhamComplexInt X U c hc ≫
    globalHypercohomologyInjectiveMap X
      (hodgeFilteredDeRhamComplex X (p : ℤ))).comm (p : ℤ) ((p : ℤ) + 1)
  simp only [Category.assoc]
  rw [hcomm]
  simp

end AlgebraicGeometry.ComplexPoint
