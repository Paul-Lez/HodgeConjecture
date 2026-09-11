/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.SupportedSectionRestrictionCone
public import Other.Algebra.Homology.MapArrowConeConnecting

/-! # The exact sign of the actual supported-section kernel comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U V : Opens X)
  (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Replacing the pushed-forward restriction target by the literal intersection
does not change the actual cone connecting morphism. -/
@[reassoc]
theorem supportRestrictionSectionsConeIso_connecting :
    (supportRestrictionSectionsConeIso X U V K).hom ≫
      (CochainComplex.mappingCone.triangle
        (sectionComplexRestriction X (.up ℤ) K (Opens.infLELeft V U))).mor₃ =
    (CochainComplex.mappingCone.triangle
      (supportRestrictionSectionsComplexShortComplex X U V K).g).mor₃ := by
  have h := CochainComplex.mappingCone.homotopyCofiber_mapArrowIso_connecting
    (supportRestrictionSectionsComplexShortComplex X U V K).g
    (sectionComplexRestriction X (.up ℤ) K (Opens.infLELeft V U))
    (Arrow.isoMk (Iso.refl _) (supportRestrictionSectionsIntersectionIso X U V K)
      (by simpa using (supportRestrictionSectionsIntersectionIso_restriction X U V K).symm))
  change (supportRestrictionSectionsConeIso X U V K).hom ≫ _ =
    (CochainComplex.mappingCone.triangle
      (supportRestrictionSectionsComplexShortComplex X U V K).g).mor₃ ≫
        (𝟙 _)⟦(1 : ℤ)⟧' at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The positive kernel-to-cone comparison followed by the standard connecting
map is the negative actual inclusion of supported sections. -/
theorem supportedSectionHomologyIsoRestrictionCone_connecting
    (hK : ∀ n, (K.X n).IsFlasque) (n : ℤ) :
    (supportedSectionHomologyIsoRestrictionCone X U V K hK n).hom ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
        (CochainComplex.mappingCone.triangle
          (sectionComplexRestriction X (.up ℤ) K (Opens.infLELeft V U))).mor₃
        (n - 1) n (by omega) =
      -HomologicalComplex.homologyMap
        (supportRestrictionSectionsComplexShortComplex X U V K).f n := by
  let S := supportRestrictionSectionsComplexShortComplex X U V K
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0
  have he := congrArg (fun f => H.shiftMap f (n - 1) n (show (1 : ℤ) + (n - 1) = n by omega))
    (supportRestrictionSectionsConeIso_connecting X U V K)
  rw [Functor.shiftMap_comp'] at he
  have hl := CochainComplex.mappingCocone.homologyMap_shiftedLiftShortComplex_connecting
    S (n - 1) n (by omega)
  change ((H.shiftIso 1 (n - 1) n (by omega)).inv.app S.X₁ ≫
    HomologicalComplex.homologyMap (CochainComplex.mappingCocone.shiftedLiftShortComplex S)
      (n - 1) ≫
    HomologicalComplex.homologyMap (supportRestrictionSectionsConeIso X U V K).hom (n - 1)) ≫ _ = _
  simp only [Category.assoc]
  erw [he, hl]
  simp only [H, Preadditive.comp_neg, Iso.inv_hom_id_app_assoc]
  rfl

end TopCat.Sheaf
