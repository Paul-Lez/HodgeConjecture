/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ActualSingularSupportBoundary
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SectionRestrictionConeNaturality

/-! # Local naturality of supported singular boundaries -/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open AlgebraicTopology.Singular
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace AlgebraicGeometry.ComplexPoint

local instance localSingularSupportTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local instance localSingularSupportParacompact (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (Z : Set (ComplexPoint X)) (hZ : IsClosed Z)

/-- The actual singular-to-injective kernel boundary comparison is natural on every open. -/
lemma actualSingularSupportBoundary_comp_injective_on_open
    (V : Opens (TopCat.of (ComplexPoint X))) (n : ℤ)
    (z : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ V
      (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).X₃.homology (n - 1)) :
    let Y := TopCat.of (ComplexPoint X)
    let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
    let SS := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
      (rationalSingularCochainComplex Y)
    let SI := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
      (ambientRationalInjectiveComplex X)
    let eS := CochainComplex.mappingCocone.shortExactHomologyIsoCone SS
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque
        Y U V _ (fun _ => inferInstance)) (n - 1) n (by omega)
    let eI := CochainComplex.mappingCocone.shortExactHomologyIsoCone SI
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact
        Y U V _) (n - 1) n (by omega)
    let Γ := (TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)
    let f : SS ⟶ SI := by
      change (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
        (rationalSingularCochainComplex Y)).map Γ ⟶
        (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
          (ambientRationalInjectiveComplex X)).map Γ
      exact Γ.mapShortComplex.map
        (TopCat.Sheaf.supportRestrictionComplexShortComplexMap Y U
          (complexSingularToAmbientInjective X))
    (eI.inv (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr SI.g) (n - 1)
      (HomologicalComplex.homologyMap f.τ₃ (n - 1) z))) =
      (complexSupportedSingularInjectiveHomologyIso X U V n).hom
        (eS.inv (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr SS.g) (n - 1) z)) := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let SS := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
      (rationalSingularCochainComplex Y)
  let SI := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
      (ambientRationalInjectiveComplex X)
  let eS := CochainComplex.mappingCocone.shortExactHomologyIsoCone SS
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque
        Y U V _ (fun _ => inferInstance)) (n - 1) n (by omega)
  let eI := CochainComplex.mappingCocone.shortExactHomologyIsoCone SI
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact
        Y U V _) (n - 1) n (by omega)
  let Γ := (TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)
  let f : SS ⟶ SI := by
    change (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
      (rationalSingularCochainComplex Y)).map Γ ⟶
      (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
        (ambientRationalInjectiveComplex X)).map Γ
    exact Γ.mapShortComplex.map
      (TopCat.Sheaf.supportRestrictionComplexShortComplexMap Y U
        (complexSingularToAmbientInjective X))
  have hf := CochainComplex.mappingCocone.shortExactHomologyIsoCone_inv_inr_naturality f
    (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque
      Y U V _ (fun _ => inferInstance))
    (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y U V _)
    (n - 1) n (by omega)
  have hz := ConcreteCategory.congr_hom hf z
  change _ = _ at hz
  have heq : (complexSupportedSingularInjectiveHomologyIso X U V n).hom =
      HomologicalComplex.homologyMap f.τ₁ n := by
    rfl
  rw [heq]
  exact hz.symm

end AlgebraicGeometry.ComplexPoint
