/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicGeometry.RelativeChernOriginalSupportSection
public import Other.AlgebraicGeometry.ChernRelativeClassGeneric
public import Other.AlgebraicGeometry.ChernComponentSectionExtraction

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open CategoryTheory.Localization

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace AlgebraicGeometry.ComplexPoint

local instance closedSupportSectionTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local instance closedSupportSectionDerivedCategory (Y : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat Y) := HasDerivedCategory.standard _

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [SmoothOfRelativeDimension (dim X.left) X.hom]

variable {X}

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [SmoothOfRelativeDimension (dim X.left) X.hom] in
/-- Transporting the cone class along equal supports agrees with support enlargement. -/
lemma enlargeSupportedInjectiveHomology_coneSupport_of_eq {S₀ T : Closeds (ComplexPoint X)} {n : ℤ}
    (h : S₀ = T) (β : RationalCohomologyWithSupport X (S₀ : Set (ComplexPoint X)) n) :
    enlargeSupportedInjectiveHomology X h.le n
        (coneSupportAddEquivSupportedInjectiveHomology X
          (S₀ : Set (ComplexPoint X)) S₀.isClosed n β) =
      coneSupportAddEquivSupportedInjectiveHomology X
        (T : Set (ComplexPoint X)) T.isClosed n
        (supportedClassTransport X
          (congrArg (fun R : Closeds (ComplexPoint X) => (R : Set (ComplexPoint X))) h)
          n β) := by
  cases h
  rw [enlargeSupportedInjectiveHomology_refl]
  rfl

variable (S : Closeds (ComplexPoint X))
  (E : HolomorphicUnitExtension X (dim X.left))
  (ℓ : E.middle.obj.obj (op S.compl))
  (hℓ : E.projection.hom.app (op S.compl) ℓ =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : S.compl ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)
  (cmp : RelativeChernComparison X (dim X.left) S.compl)
  (U : Opens (TopCat.of (ComplexPoint X)))
  (ℓU : E.middle.obj.obj (op U))
  (hℓU : E.projection.hom.app (op U) ℓU =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : U ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)
  (w : (holomorphicUnitSheaf X (dim X.left)).obj.obj (op (U ⊓ S.compl)))
  (hw : E.inclusion.hom.app (op (U ⊓ S.compl)) w =
      E.middle.obj.map (homOfLE (inf_le_right : U ⊓ S.compl ≤ S.compl)).op ℓ -
      E.middle.obj.map (homOfLE (inf_le_left : U ⊓ S.compl ≤ U)).op ℓU)

include ℓU hℓU hw in
omit [IsProjective X.hom] in
set_option maxHeartbeats 2000000 in
/-- The original supported section transports to the prescribed closed support. -/
theorem restrict_original_relativeChernClass_closed_support_section :
    let Z : Set (ComplexPoint X) := (S.compl : Set (ComplexPoint X))ᶜ
    let S₀ : Closeds (ComplexPoint X) := ⟨Z, S.compl.isOpen.isClosed_compl⟩
    let hS : S₀ = S := by
      apply Closeds.ext
      change ((S.compl : Set (ComplexPoint X))ᶜ) = (S : Set (ComplexPoint X))
      exact compl_compl _
    let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z
      S.compl.isOpen.isClosed_compl)
    let K := (TopCat.Sheaf.supportRestrictionComplexShortComplex
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, S.compl.isOpen.isClosed_compl.isOpen_compl⟩
      (ambientRationalInjectiveComplex X)).X₁
    let m := supportSheafToAmbientInjectiveCone X Z S.compl.isOpen.isClosed_compl
    let : IsIso ((HomologicalComplex.homologyMap m 1).hom.app
        (op (U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U))))) := by
      have : IsIso (HomologicalComplex.homologyMap m 1) :=
        (quasiIsoAt_iff_isIso_homologyMap m 1).mp inferInstance
      infer_instance
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let gU := originalLocalBoundaryMap X (dim X.left) S.compl U w
    let a₀ := (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
        (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X)))).homologyπ 0
      (TopCat.Sheaf.integerCocycleGlobalSection (TopCat.of (ComplexPoint X))
        (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) 0
        (CochainComplex.HomComplex.Cocycle.ofHom
          (𝟙 (TopCat.Sheaf.integerConstantSingleComplex
            (TopCat.of (ComplexPoint X))))))
    let b :=
      ((((TopCat.Sheaf.integerConstantSingleComplex
          (TopCat.of (ComplexPoint X))).sc 0).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap gU 0 ≫
          (((C⟦(1 : ℤ)⟧).sc 0).mapHomologyIso F).hom).hom.app
        (op (⊤ : Opens (TopCat.of U)))
        (((TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))).homology 0).obj.map
          (homOfLE (le_top : U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)) ≤ ⊤)).op
          (TopCat.Sheaf.sectionCohomologyToSheafSection
            (TopCat.of (ComplexPoint X))
            (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) 0 ⊤ a₀))
    let t :=
      (TopCat.Sheaf.sectionCohomologySheafShiftMap (TopCat.of (ComplexPoint X)) C
        1 0 1 (by omega)).hom.app
        (op (U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)))) b
    supportedInjectiveLocalSection (U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)))
        (2 : ℤ) (relativeChernSupportedClassOnClosed S E ℓ hℓ cmp) =
      (HomologicalComplex.homologyMap
        (supportedInjectiveComplexMap X hS.le) 2).hom.app
        (op (U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U))))
        (-(TopCat.Sheaf.sectionCohomologySheafShiftMap (TopCat.of (ComplexPoint X)) K
          1 1 2 (by omega)).hom.app
          (op (U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U))))
          (inv ((HomologicalComplex.homologyMap m 1).hom.app
            (op (U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U))))) t)) := by
  dsimp only
  let S₀ : Closeds (ComplexPoint X) :=
    ⟨((S.compl : Set (ComplexPoint X))ᶜ), S.compl.isOpen.isClosed_compl⟩
  let hS : S₀ = S := by
    apply Closeds.ext
    change ((S.compl : Set (ComplexPoint X))ᶜ) = (S : Set (ComplexPoint X))
    exact compl_compl _
  let a₀ := coneSupportAddEquivSupportedInjectiveHomology X
    (S₀ : Set (ComplexPoint X)) S₀.isClosed 2
    (E.relativeChernClass S.compl ℓ hℓ cmp)
  have hclass : enlargeSupportedInjectiveHomology X hS.le 2 a₀ =
      relativeChernSupportedClassOnClosed S E ℓ hℓ cmp := by
    exact enlargeSupportedInjectiveHomology_coneSupport_of_eq hS (E.relativeChernClass S.compl ℓ hℓ cmp)
  have hlocal := supportedInjectiveLocalSection_enlarge (X := X) hS.le
    (U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U))) 2 a₀
  rw [← hclass, hlocal]
  have horig := restrict_original_relativeChernClass_support_section
    (X := X) (d := dim X.left) E S.compl U ℓU ℓ hℓ hℓU cmp w hw ⊤
  dsimp only at horig
  have hsec := ConcreteCategory.congr_hom
    (TopCat.Sheaf.sectionCohomologyToSheafSection_restriction
      (TopCat.of (ComplexPoint X)) (complexSupportInjectiveComplex X S₀) 2
      (homOfLE (le_top : U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)) ≤ ⊤))) a₀
  simp only [ConcreteCategory.comp_apply] at hsec
  exact congrArg
    ((HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hS.le) 2).hom.app
      (op (U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)))))
    (hsec.trans horig)

end AlgebraicGeometry.ComplexPoint
