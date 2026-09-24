/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CartierWindingChartVanishing
public import Other.AlgebraicGeometry.CartierChernLocalWinding
public import Other.AlgebraicGeometry.Cohomology.SupportSheafConeLocalVanishing

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open AlgebraicTopology.Singular

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace AlgebraicGeometry.ComplexPoint

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
local instance cartierNormalizedVanishingTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local instance cartierNormalizedVanishingAmbientDerived :
    HasDerivedCategory (AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _
local instance cartierNormalizedVanishingOpenDerived
    (V : Opens (TopCat.of (ComplexPoint X))) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of V)) := HasDerivedCategory.standard _
attribute [local instance] isNoetherian_of_isProjective

variable {L : X.left.Modules} {c : Scheme.CartierData X.left}
  (g : ∀ i : c.ι, Γ(L, c.opens i))
  (E : HolomorphicUnitExtension X (dim X.left))
  (e : (moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules)
  (hg : ∀ i, Scheme.Modules.Generates (g i))
  {x : X.left} {q : ComplexPoint X}
  (ch : ChernWindingChart X c x (dim X.left) 1 q)

lemma ChernWindingChart.regularFrame_relativeSection_restrict_eq_zero
    (z : ComplexPoint X) (hcz : ch.carrier ≤ E.localLifts.opens z)
    (cmp : RelativeChernComparison X (dim X.left) ch.punctured) :
    let Y := TopCat.of (ComplexPoint X)
    let S : Closeds Y := ⟨(ch.punctured : Set Y)ᶜ, ch.punctured.isOpen.isClosed_compl⟩
    let K := complexSupportInjectiveComplex X S
    let α := E.relativeChernClass ch.punctured
      (E.middle.obj.map (homOfLE ch.punctured_le).op
        (E.frameLift z ch.carrier hcz (ch.regularFrame g E e)
          (ch.holomorphicGenerates_regularFrame g E e hg)))
      (E.projection_restrict_lift X ch.punctured_le
        (E.frameLift z ch.carrier hcz (ch.regularFrame g E e)
          (ch.holomorphicGenerates_regularFrame g E e hg))
        (E.projection_frameLift z ch.carrier hcz (ch.regularFrame g E e)
          (ch.holomorphicGenerates_regularFrame g E e hg))) cmp
    (supportRelativeCohomologySheaf Y S 2).obj.map
        (homOfLE (show ch.carrier ≤ (⊤ : Opens Y) from le_top)).op
      ((complexSupportInjectiveCohomologySheafIsoRelative X S 2).hom.hom.app (op ⊤)
        (TopCat.Sheaf.sectionCohomologyToSheafSection Y K 2 ⊤
          (coneSupportAddEquivSupportedInjectiveHomology X S S.isClosed 2 α))) = 0 := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let S : Closeds Y := ⟨(ch.punctured : Set Y)ᶜ, ch.punctured.isOpen.isClosed_compl⟩
  let K := complexSupportInjectiveComplex X S
  let ℓ := E.frameLift z ch.carrier hcz (ch.regularFrame g E e)
    (ch.holomorphicGenerates_regularFrame g E e hg)
  let hℓ := E.projection_frameLift z ch.carrier hcz (ch.regularFrame g E e)
    (ch.holomorphicGenerates_regularFrame g E e hg)
  let α := E.relativeChernClass ch.punctured
    (E.middle.obj.map (homOfLE ch.punctured_le).op ℓ)
    (E.projection_restrict_lift X ch.punctured_le ℓ hℓ) cmp
  have hreg := ChernWindingChart.regularFrame_relativeChernClass_restrict_eq_zero
    g E e hg ch z hcz cmp
  dsimp [ℓ, hℓ, α] at hreg ⊢
  have hloc := coneSupportSection_restrict_eq_zero X
    (S : Set Y) S.isClosed 2 α ch.carrier hreg ⊤
  dsimp only at hloc
  rw [Opens.isOpenEmbedding_obj_top] at hloc
  have hloc' :
      (K.homology (2 : ℤ)).obj.map
        (homOfLE (show ch.carrier ≤ (⊤ : Opens Y) from le_top)).op
        (TopCat.Sheaf.sectionCohomologyToSheafSection Y K (2 : ℤ) ⊤
          (coneSupportAddEquivSupportedInjectiveHomology X (S : Set Y) S.isClosed 2 α)) = 0 := by
    convert hloc using 1 <;>
      simp only [K, Y, complexSupportInjectiveComplex,
        TopCat.Sheaf.supportRestrictionComplexShortComplex, TopologicalSpace.Closeds.compl]
  let N := complexSupportInjectiveCohomologySheafIsoRelative X S 2
  have hN := congrArg
    (fun y : ((complexSupportInjectiveComplex X S).homology (2 : ℤ)).obj.obj
        (op ch.carrier) =>
      (complexSupportInjectiveCohomologySheafIsoRelative X S 2).hom.hom.app
        (op ch.carrier) y) hloc'
  have hn := N.hom.hom.naturality
    (homOfLE (show ch.carrier ≤ (⊤ : Opens Y) from le_top)).op
  simp only at hN hn
  have hp := ConcreteCategory.congr_hom hn
    (TopCat.Sheaf.sectionCohomologyToSheafSection Y
      (complexSupportInjectiveComplex X S) 2 ⊤
      (coneSupportAddEquivSupportedInjectiveHomology X (S : Set Y) S.isClosed 2 α))
  simp only [ConcreteCategory.comp_apply] at hp
  calc
    _ = (ConcreteCategory.hom (N.hom.hom.app (op ch.carrier)))
        ((ConcreteCategory.hom
          ((HomologicalComplex.homology (complexSupportInjectiveComplex X S) (2 : ℤ)).obj.map
            (homOfLE (show ch.carrier ≤ (⊤ : Opens Y) from le_top)).op))
          ((ConcreteCategory.hom
            (TopCat.Sheaf.sectionCohomologyToSheafSection Y
              (complexSupportInjectiveComplex X S) (2 : ℤ) ⊤)
            (coneSupportAddEquivSupportedInjectiveHomology X (S : Set Y) S.isClosed 2 α)))) :=
      hp.symm
    _ = 0 := by
      convert (by simpa only [N, K, Y, map_zero] using hN) using 1

lemma ChernWindingChart.cartier_relativeSection_restrict_eq_windingSheaf
    {Ω : Opens (TopCat.of (ComplexPoint X))} {ℓ : E.middle.obj.obj (op Ω)}
    (hℓ : IsCartierComplementLift g E e hg Ω ℓ)
    (hℓ₀ : E.projection.hom.app (op Ω) ℓ =
      (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection)
    (hΩc : Ω ≤ divisorComplementOpen c) (hchΩ : ch.punctured ≤ Ω)
    (z : ComplexPoint X) (hcz : ch.carrier ≤ E.localLifts.opens z)
    (cmp : RelativeChernComparison X (dim X.left) ch.punctured) :
    let Y := TopCat.of (ComplexPoint X)
    let S : Closeds Y := ⟨(ch.punctured : Set Y)ᶜ, ch.punctured.isOpen.isClosed_compl⟩
    let ℓ₂ := E.middle.obj.map (homOfLE hchΩ).op ℓ
    let hℓ₂ := E.projection_restrict_lift X hchΩ ℓ hℓ₀
    let α₂ := E.relativeChernClass ch.punctured
      ℓ₂ hℓ₂ cmp
    let N := complexSupportInjectiveCohomologySheafIsoRelative X S 2
    let sec := TopCat.Sheaf.sectionCohomologyToSheafSection Y
      (complexSupportInjectiveComplex X S) 2 ⊤
    (supportRelativeCohomologySheaf Y S 2).obj.map
      (homOfLE (show ch.carrier ≤ (⊤ : Opens Y) from le_top)).op
      (N.hom.hom.app (op ⊤) (sec (coneSupportAddEquivSupportedInjectiveHomology X S
        S.isClosed 2 α₂))) =
      (supportRelativeCohomologySheaf Y S 2).obj.map
        (homOfLE (show ch.carrier ≤ (⊤ : Opens Y) from le_top)).op
        (windingSheafHom (hasWindingPeriods X (dim X.left) ⊤ S)
          ((holomorphicUnitSheaf X (dim X.left)).obj.map
            (homOfLE (show ⊤ ⊓ S.compl ≤ ch.punctured from
              fun _y hy => not_not.mp hy.2)).op ch.cartierUnit)) := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let S : Closeds Y := ⟨(ch.punctured : Set Y)ᶜ, ch.punctured.isOpen.isClosed_compl⟩
  let ℓ₁ := E.frameLift z ch.carrier hcz (ch.regularFrame g E e)
    (ch.holomorphicGenerates_regularFrame g E e hg)
  let hℓ₁ := E.projection_frameLift z ch.carrier hcz (ch.regularFrame g E e)
    (ch.holomorphicGenerates_regularFrame g E e hg)
  let ℓ₂ := E.middle.obj.map (homOfLE hchΩ).op ℓ
  let hℓ₂ := E.projection_restrict_lift X hchΩ ℓ hℓ₀
  let α₁ := E.relativeChernClass ch.punctured
    (E.middle.obj.map (homOfLE ch.punctured_le).op ℓ₁)
    (E.projection_restrict_lift X ch.punctured_le ℓ₁ hℓ₁) cmp
  let α₂ := E.relativeChernClass ch.punctured
    (E.middle.obj.map (homOfLE hchΩ).op ℓ)
    hℓ₂ cmp
  let F := coneSupportAddEquivSupportedInjectiveHomology X S S.isClosed 2
  let N := complexSupportInjectiveCohomologySheafIsoRelative X S 2
  let sec := TopCat.Sheaf.sectionCohomologyToSheafSection Y
    (complexSupportInjectiveComplex X S) 2 ⊤
  let R := (supportRelativeCohomologySheaf Y S 2).obj.map
    (homOfLE (show ch.carrier ≤ (⊤ : Opens Y) from le_top)).op
  have hzero := ChernWindingChart.regularFrame_relativeSection_restrict_eq_zero
    g E e hg ch z hcz cmp
  dsimp [ℓ₁, hℓ₁, ℓ₂, hℓ₂, α₁, α₂] at hzero ⊢
  have hdiff := IsCartierComplementLift.relativeChernClass_sub_eq_windingSheaf_cartier
    X g E e hg ch hℓ hℓ₀ hΩc hchΩ z hcz cmp
  dsimp only at hdiff
  have hdiffR := congrArg (fun v => R v) hdiff
  have hsub :
      N.hom.hom.app (op ⊤) (sec (F (α₂ - α₁))) =
        N.hom.hom.app (op ⊤) (sec (F α₂)) -
          N.hom.hom.app (op ⊤) (sec (F α₁)) := by
    rw [← map_sub]
    congr 1
    rw [F.map_sub]
    rw [map_sub]
  have hzero' : R (N.hom.hom.app (op ⊤) (sec (F α₁))) = 0 := by
    exact hzero
  calc
    R (N.hom.hom.app (op ⊤) (sec (F α₂))) =
        R (N.hom.hom.app (op ⊤) (sec (F α₂))) -
          R (N.hom.hom.app (op ⊤) (sec (F α₁))) := by rw [hzero', sub_zero]
    _ = R (N.hom.hom.app (op ⊤) (sec (F α₂)) -
        N.hom.hom.app (op ⊤) (sec (F α₁))) := by rw [map_sub]
    _ = R (N.hom.hom.app (op ⊤) (sec (F (α₂ - α₁)))) := by rw [hsub]
    _ = _ := hdiffR

end AlgebraicGeometry.ComplexPoint
