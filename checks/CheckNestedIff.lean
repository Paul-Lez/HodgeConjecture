import Other.AlgebraicGeometry.AnalyticNestedTransitionClass

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

noncomputable section

variable (X : Over (Spec (CommRingCat.of ℂ)))

local instance : Abelian (AnalyticAdditiveSheaf X) :=
  CategoryTheory.sheafIsAbelian

local instance : HasExt.{1} (AnalyticAdditiveSheaf X) := analyticHasExt X

example (F : AnalyticAdditiveSheaf X)
    (U V A B : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (hA : A ≤ U ⊓ V) (hB : B ≤ U ⊓ V) (hoverlap : A ⊔ B = U ⊓ V)
    (c : F.obj.obj (.op (A ⊓ B))) :
    analyticNestedTransitionExtClass X F U V A B hcover hA hB hoverlap c = 0 ↔
      ∃ γ : Abelian.Ext.{1}
          (analyticOpenFreeAbelianSheaf X U ⊞ analyticOpenFreeAbelianSheaf X V) F 1,
        analyticOuterExtRestriction X F U V hcover γ =
          analyticRelativeTransitionExtClass X F A B (U ⊓ V)
            hA hB hoverlap c := by
  let T : ShortComplex (AnalyticAdditiveSheaf X) :=
    (analyticCoverMayerVietorisSquare X U V hcover).shortComplex
  have hT : T.ShortExact :=
    (analyticCoverMayerVietorisSquare X U V hcover).shortComplex_shortExact
  let δ : Abelian.Ext.{1} T.X₃ T.X₁ 1 := hT.extClass
  let β : Abelian.Ext.{1} T.X₁ F 1 :=
    analyticRelativeTransitionExtClass X F A B (U ⊓ V) hA hB hoverlap c
  let a₀ : Abelian.Ext.{1} (constantIntegerSheaf X) T.X₃ 0 :=
    Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso X).inv
  constructor
  · intro hnested
    have hδβ : δ.comp β (show 1 + 1 = 2 from rfl) = 0 := by
      let z : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X ⊤) F 2 :=
        δ.comp β (show 1 + 1 = 2 from rfl)
      have hz : (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X)
          (analyticTopFreeAbelianSheafIso X).inv).comp z
          (show 0 + 2 = 2 from rfl) = 0 := hnested
      have h := congrArg
        (fun z : Abelian.Ext.{1} (constantIntegerSheaf X) F 2 ↦
          (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X)
            (analyticTopFreeAbelianSheafIso X).hom).comp z
            (show 0 + 2 = 2 from rfl)) hz
      have hz' : z = 0 := by
        simpa only [Abelian.Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id,
          Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_zero] using h
      change z = 0
      exact hz'
    obtain ⟨γ, hγ⟩ := Abelian.Ext.contravariant_sequence_exact₁ hT F β
      (show 1 + 1 = 2 from rfl) hδβ
    exact ⟨γ, hγ⟩
  · rintro ⟨γ, hγ⟩
    let γ' : Abelian.Ext.{1} T.X₂ F 1 := γ
    have hγ' : (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X) T.f).comp γ'
        (show 0 + 1 = 1 from rfl) = β := by
      exact hγ
    unfold analyticNestedTransitionExtClass
    dsimp only
    change a₀.comp (δ.comp β (show 1 + 1 = 2 from rfl))
      (show 0 + 2 = 2 from rfl) = 0
    rw [← hγ']
    rw [hT.extClass_comp_assoc, Abelian.Ext.comp_zero]

end
end AlgebraicGeometry.ComplexPoint
