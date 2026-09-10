import Other.AlgebraicGeometry.ExplicitEllipticCurveCechRepresentative
import Other.AlgebraicGeometry.HolomorphicDeRhamModuleSheaf
open CategoryTheory CategoryTheory.Limits TopologicalSpace
#check Abelian.Ext.comp_assoc
#check Abelian.Ext.mk₀_comp_mk₀
#check AlgebraicGeometry.ComplexPoint.analyticSectionSheafHom_postcomp
#check AlgebraicGeometry.ComplexPoint.holomorphicTopFormMultiplicationSheaf

namespace AlgebraicGeometry.ComplexPoint
noncomputable section
variable (X : Over (AlgebraicGeometry.Spec (.of ℂ)))
local instance : Abelian (AnalyticAdditiveSheaf X) := CategoryTheory.sheafIsAbelian
local instance : HasExt.{1} (AnalyticAdditiveSheaf X) := analyticHasExt X

theorem test_nested_postcomp
    (F G : AnalyticAdditiveSheaf X) (f : F ⟶ G)
    (U V A B : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (hA : A ≤ U ⊓ V) (hB : B ≤ U ⊓ V) (hoverlap : A ⊔ B = U ⊓ V)
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
    (analyticCoverMayerVietorisSquare X U V hcover).shortComplex_shortExact.extClass
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
  rw [test_relative_postcomp]

theorem test_relative_postcomp
    (F G : AnalyticAdditiveSheaf X) (f : F ⟶ G)
    (A B W : Opens (TopCat.of (ComplexPoint X))) (hA : A ≤ W) (hB : B ≤ W)
    (hcover : A ⊔ B = W) (c : F.obj.obj (.op (A ⊓ B))) :
    (analyticRelativeTransitionExtClass X F A B W hA hB hcover c).comp
        (Abelian.Ext.mk₀ f) (show 1 + 0 = 1 from rfl) =
      analyticRelativeTransitionExtClass X G A B W hA hB hcover
        (f.hom.app (.op (A ⊓ B)) c) := by
  let δ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X W)
      (analyticOpenFreeAbelianSheaf X (A ⊓ B)) 1 :=
    ((analyticRelativeCoverMayerVietorisSquare X A B W hA hB hcover).shortComplex_shortExact).extClass
      (C := AnalyticAdditiveSheaf X)
  let s : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X (A ⊓ B)) F 0 :=
    Abelian.Ext.mk₀ (analyticSectionSheafHom X F (A ⊓ B) c)
  let t : Abelian.Ext.{1} F G 0 := Abelian.Ext.mk₀ f
  change (δ.comp s rfl).comp t rfl =
    δ.comp (Abelian.Ext.mk₀ (analyticSectionSheafHom X G (A ⊓ B)
      (f.hom.app (.op (A ⊓ B)) c))) rfl
  rw [Abelian.Ext.comp_assoc δ s t rfl rfl rfl]
  rw [Abelian.Ext.mk₀_comp_mk₀]
  rw [analyticSectionSheafHom_postcomp]

variable (d : ℕ) [SmoothOfRelativeDimension d X.hom]

theorem test_top_app (p : ℕ)
    (s : (holomorphicDeRhamSheaf X d p).obj.obj (.op ⊤))
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (a : OpenHolomorphicFunctions X d U) :
    (holomorphicTopFormMultiplicationSheaf X d p s).hom.app U a =
      (holomorphicDeRhamOSheafToAdditiveIso X d p).hom.hom.app U
        ((a : (holomorphicRingSheaf X d).obj.obj U) •
          ((moduleSectionsOfTop X d
            ((holomorphicDeRhamOSheafToAdditiveIso X d p).inv.hom.app (.op ⊤) s)).val U :
              (holomorphicDeRhamOSheaf X d p).val.obj U)) := by
  rfl

end
end AlgebraicGeometry.ComplexPoint
