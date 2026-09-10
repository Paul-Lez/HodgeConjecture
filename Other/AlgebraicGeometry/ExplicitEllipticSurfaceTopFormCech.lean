/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicDeRhamModuleSheaf
public import Other.AlgebraicGeometry.ExplicitEllipticCurveCechRepresentative

/-!
# Multiplying the elliptic-surface Cech class by its global top form

This file constructs the honest sheaf morphism from holomorphic functions to
holomorphic two-forms given by multiplication with the explicit global form.
It also records functoriality of relative and nested Mayer--Vietoris classes
under every morphism of their coefficient sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))

local instance topFormCechSheafAbelian : Abelian (AnalyticAdditiveSheaf X) :=
  CategoryTheory.sheafIsAbelian

local instance topFormCechHasExt : HasExt.{1} (AnalyticAdditiveSheaf X) :=
  analyticHasExt X

/-- Relative two-open transition classes commute with postcomposition on the
coefficient sheaf. -/
theorem analyticRelativeTransitionExtClass_postcomp
    (F G : AnalyticAdditiveSheaf X) (f : F ⟶ G)
    (A B W : Opens (TopCat.of (ComplexPoint X)))
    (hA : A ≤ W) (hB : B ≤ W) (hcover : A ⊔ B = W)
    (c : F.obj.obj (.op (A ⊓ B))) :
    (analyticRelativeTransitionExtClass X F A B W hA hB hcover c).comp
        (Abelian.Ext.mk₀ f) (show 1 + 0 = 1 from rfl) =
      analyticRelativeTransitionExtClass X G A B W hA hB hcover
        (f.hom.app (.op (A ⊓ B)) c) := by
  let δ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X W)
      (analyticOpenFreeAbelianSheaf X (A ⊓ B)) 1 :=
    ((analyticRelativeCoverMayerVietorisSquare X A B W hA hB
      hcover).shortComplex_shortExact).extClass
        (C := AnalyticAdditiveSheaf X)
  let s : Abelian.Ext.{1}
      (analyticOpenFreeAbelianSheaf X (A ⊓ B)) F 0 :=
    Abelian.Ext.mk₀ (analyticSectionSheafHom X F (A ⊓ B) c)
  let t : Abelian.Ext.{1} F G 0 := Abelian.Ext.mk₀ f
  change (δ.comp s rfl).comp t rfl =
    δ.comp (Abelian.Ext.mk₀ (analyticSectionSheafHom X G (A ⊓ B)
      (f.hom.app (.op (A ⊓ B)) c))) rfl
  rw [Abelian.Ext.comp_assoc δ s t rfl rfl rfl]
  rw [Abelian.Ext.mk₀_comp_mk₀]
  rw [analyticSectionSheafHom_postcomp]

/-- Nested four-open transition classes commute with postcomposition on the
coefficient sheaf. -/
theorem analyticNestedTransitionExtClass_postcomp
    (F G : AnalyticAdditiveSheaf X) (f : F ⟶ G)
    (U V A B : Opens (TopCat.of (ComplexPoint X)))
    (hcover : U ⊔ V = ⊤)
    (hA : A ≤ U ⊓ V) (hB : B ≤ U ⊓ V)
    (hoverlap : A ⊔ B = U ⊓ V)
    (c : F.obj.obj (.op (A ⊓ B))) :
    (analyticNestedTransitionExtClass X F U V A B hcover hA hB hoverlap c).comp
        (Abelian.Ext.mk₀ f) (show 2 + 0 = 2 from rfl) =
      analyticNestedTransitionExtClass X G U V A B hcover hA hB hoverlap
        (f.hom.app (.op (A ⊓ B)) c) := by
  let a₀ : Abelian.Ext.{1} (constantIntegerSheaf X)
      (analyticOpenFreeAbelianSheaf X ⊤) 0 :=
    Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso X).inv
  let δ₀ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X ⊤)
      (analyticOpenFreeAbelianSheaf X (U ⊓ V)) 1 :=
    (analyticCoverMayerVietorisSquare X U V
      hcover).shortComplex_shortExact.extClass
        (C := AnalyticAdditiveSheaf X)
  let βF := analyticRelativeTransitionExtClass X F A B (U ⊓ V)
    hA hB hoverlap c
  let βG := analyticRelativeTransitionExtClass X G A B (U ⊓ V)
    hA hB hoverlap (f.hom.app (.op (A ⊓ B)) c)
  let t : Abelian.Ext.{1} F G 0 := Abelian.Ext.mk₀ f
  change (a₀.comp (δ₀.comp βF rfl) rfl).comp t rfl =
    a₀.comp (δ₀.comp βG rfl) rfl
  rw [Abelian.Ext.comp_assoc a₀ (δ₀.comp βF rfl) t rfl rfl rfl]
  rw [Abelian.Ext.comp_assoc δ₀ βF t rfl rfl rfl]
  rw [analyticRelativeTransitionExtClass_postcomp]

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

local instance surfaceTopFormCechSheafAbelian :
    Abelian (AnalyticAdditiveSheaf surfaceVariety) :=
  CategoryTheory.sheafIsAbelian

local instance surfaceTopFormCechHasExt :
    HasExt.{1} (AnalyticAdditiveSheaf surfaceVariety) :=
  analyticHasExt surfaceVariety

/-- The honest morphism `𝒪_S ⟶ Ω²_S` given by multiplication with the
explicit global invariant two-form. -/
def surfaceHolomorphicTopFormMultiplication :
    surfaceCechHolomorphicFunctionSheaf ⟶ surfaceHolomorphicTwoFormSheaf :=
  holomorphicTopFormMultiplicationSheaf surfaceVariety 2 2
    surfaceGlobalHolomorphicTwoForm

/-- The image of an explicit holomorphic Cech external product under
multiplication by the global top form is the nested transition class of the
pointwise multiplied deepest-overlap section. -/
theorem surfaceHolomorphicCechExternalProductClass_comp_topForm
    (a b : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    (surfaceHolomorphicCechExternalProductClass a b).comp
        (Abelian.Ext.mk₀ surfaceHolomorphicTopFormMultiplication)
        (show 2 + 0 = 2 from rfl) =
      analyticNestedTransitionExtClass surfaceVariety
        surfaceHolomorphicTwoFormSheaf
        (surfaceFstCechOpen 0) (surfaceFstCechOpen 1)
        (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
        surfaceFstCechOpen_cover inf_le_left inf_le_left
        surfaceCechInnerOpen_cover
        (surfaceHolomorphicTopFormMultiplication.hom.app
          (.op surfaceCechDeepestOpen) (surfaceCechProductSection a b)) := by
  exact analyticNestedTransitionExtClass_postcomp surfaceVariety
    surfaceCechHolomorphicFunctionSheaf surfaceHolomorphicTwoFormSheaf
    surfaceHolomorphicTopFormMultiplication
    (surfaceFstCechOpen 0) (surfaceFstCechOpen 1)
    (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
    surfaceFstCechOpen_cover inf_le_left inf_le_left
    surfaceCechInnerOpen_cover (surfaceCechProductSection a b)

end AlgebraicGeometry.ExplicitEllipticCandidate
