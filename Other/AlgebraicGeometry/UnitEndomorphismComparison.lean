/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveHolomorphicFunctions
public import Other.AlgebraicGeometry.AnalytificationModules

/-!
# Degree-zero comparison for morphisms of module sheaves

On a preconnected projective analytification, maximum modulus makes every holomorphic global
function algebraic.  This file upgrades that statement from functions to the categorical form
needed in a twist presentation: every endomorphism of the holomorphic tensor unit is the
analytification of an endomorphism of the algebraic tensor unit.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace SheafOfModules

universe u

variable {T : Type u} [TopologicalSpace T]
  (R : Sheaf (Opens.grothendieckTopology T) RingCat.{u})

/-- A section of a module presheaf on an opens site is determined by its value on the top open. -/
lemma sections_ext_top {M : SheafOfModules.{u} R} (s t : M.sections)
    (h : s.val (.op ⊤) = t.val (.op ⊤)) : s = t := by
  apply PresheafOfModules.sections_ext
  intro U
  let i : Opposite.op (⊤ : Opens T) ⟶ U := (homOfLE le_top).op
  rw [← s.property i, ← t.property i, h]

/-- Extend an element over the top open to its compatible family of restrictions. -/
def unitSectionsOfTop (a : R.obj.obj (.op ⊤)) : (unit R).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ R.obj.map (homOfLE (show U.unop ≤ (⊤ : Opens T) from le_top)).op a)
    (fun {U V} f ↦ by
      let iU : Opposite.op (⊤ : Opens T) ⟶ U :=
        (homOfLE (show U.unop ≤ (⊤ : Opens T) from le_top)).op
      let iV : Opposite.op (⊤ : Opens T) ⟶ V :=
        (homOfLE (show V.unop ≤ (⊤ : Opens T) from le_top)).op
      change R.obj.map f (R.obj.map iU a) = R.obj.map iV a
      rw [← ConcreteCategory.comp_apply, ← R.obj.map_comp]
      rw [show iU ≫ f = iV from Subsingleton.elim _ _])

@[simp]
lemma unitSectionsOfTop_top (a : R.obj.obj (.op ⊤)) :
    (unitSectionsOfTop R a).val (.op ⊤) = a := by
  change R.obj.map (𝟙 _) a = a
  simp

end SheafOfModules

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  [IsProjective X.hom]

local instance unitComparison_siteContinuous :
    (Opens.map (underlyingContinuousMap X)).IsContinuous
      (Opens.grothendieckTopology X.left) (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreserving_opens_map (underlyingContinuousMap X))
    (coverPreserving_opens_map (underlyingContinuousMap X))

local instance unitComparison_pushforward_isRightAdjoint :
    (holomorphicModulePushforward X d).IsRightAdjoint :=
  (moduleAnalytificationAdjunction X d).isRightAdjoint

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Under the unit isomorphisms, analytification is surjective on endomorphisms of the tensor
unit. This is the categorical degree-zero `H⁰` comparison. -/
theorem unitEndomorphism_analytification_surjective
    [PreconnectedSpace (ComplexPoint X)] :
    Function.Surjective
      (fun f : SheafOfModules.unit X.left.ringCatSheaf ⟶
          SheafOfModules.unit X.left.ringCatSheaf ↦
        (moduleAnalytificationUnitIso X d).inv ≫
          (moduleAnalytification X d).map f ≫
            (moduleAnalytificationUnitIso X d).hom) := by
  intro h
  let φ := regularToHolomorphicRingSheaf X d
  letI : (SheafOfModules.pushforward φ).IsRightAdjoint := by
    change (holomorphicModulePushforward X d).IsRightAdjoint
    infer_instance
  let u : SheafOfModules.unit X.left.ringCatSheaf ⟶
      (holomorphicModulePushforward X d).obj
        (SheafOfModules.unit (holomorphicRingSheaf X d)) :=
    SheafOfModules.unitToPushforwardObjUnit φ
  let sR : (SheafOfModules.unit (holomorphicRingSheaf X d)).sections :=
    (SheafOfModules.unit (holomorphicRingSheaf X d)).unitHomEquiv h
  obtain ⟨a, ha⟩ := regularFunctionsToHolomorphic_top_surjective X d
    (sR.val (.op (analyticOpen X (⊤ : X.left.Opens))))
  let sS : (SheafOfModules.unit X.left.ringCatSheaf).sections :=
    SheafOfModules.unitSectionsOfTop X.left.ringCatSheaf a
  let f : SheafOfModules.unit X.left.ringCatSheaf ⟶
      SheafOfModules.unit X.left.ringCatSheaf :=
    (SheafOfModules.unit X.left.ringCatSheaf).unitHomEquiv.symm sS
  have hsections : SheafOfModules.sectionsMap u sS =
      SheafOfModules.pushforwardSections φ sR := by
    apply SheafOfModules.sections_ext_top
    change u.val.app (.op ⊤) (sS.val (.op ⊤)) =
      sR.val (.op (analyticOpen X (⊤ : X.left.Opens)))
    rw [show sS.val (.op ⊤) = a by
      simpa [sS] using SheafOfModules.unitSectionsOfTop_top X.left.ringCatSheaf a]
    rw [show u.val.app (.op ⊤) a = φ.hom.app (.op ⊤) a by
      exact SheafOfModules.unitToPushforwardObjUnit_val_app_apply φ a]
    change (regularFunctionsToHolomorphic X d (⊤ : X.left.Opens)) a = _
    exact ha
  have hu : f ≫ u = u ≫ (holomorphicModulePushforward X d).map h := by
    apply ((holomorphicModulePushforward X d).obj
      (SheafOfModules.unit (holomorphicRingSheaf X d))).unitHomEquiv.injective
    have hf : (SheafOfModules.unit X.left.ringCatSheaf).unitHomEquiv f = sS := by
      exact Equiv.apply_symm_apply _ _
    have hfu : ((holomorphicModulePushforward X d).obj
        (SheafOfModules.unit (holomorphicRingSheaf X d))).unitHomEquiv (f ≫ u) =
        SheafOfModules.sectionsMap u sS :=
      (SheafOfModules.unitHomEquiv_comp_apply f u).trans
        (congrArg (SheafOfModules.sectionsMap u) hf)
    have hpush := SheafOfModules.pushforwardSections_unitHomEquiv φ h
    exact hfu.trans (hsections.trans (by
      simpa only [u, φ, sR, holomorphicModulePushforward] using hpush))
  refine ⟨f, ?_⟩
  rw [← cancel_epi (moduleAnalytificationUnitIso X d).hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  apply ((moduleAnalytificationAdjunction X d).homEquiv _ _).injective
  have he : (moduleAnalytificationAdjunction X d).homEquiv _ _
      (moduleAnalytificationUnitIso X d).hom = u := by
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ
  calc
    ((moduleAnalytificationAdjunction X d).homEquiv _ _)
        ((moduleAnalytification X d).map f ≫ (moduleAnalytificationUnitIso X d).hom) =
      f ≫ ((moduleAnalytificationAdjunction X d).homEquiv _ _)
        (moduleAnalytificationUnitIso X d).hom :=
          (moduleAnalytificationAdjunction X d).homEquiv_naturality_left _ _
    _ = f ≫ u := by rw [he]
    _ = u ≫ (holomorphicModulePushforward X d).map h := hu
    _ = ((moduleAnalytificationAdjunction X d).homEquiv _ _)
        (moduleAnalytificationUnitIso X d).hom ≫
          (holomorphicModulePushforward X d).map h := by rw [he]
    _ = ((moduleAnalytificationAdjunction X d).homEquiv _ _)
        ((moduleAnalytificationUnitIso X d).hom ≫ h) :=
          ((moduleAnalytificationAdjunction X d).homEquiv_naturality_right _ _).symm

end AlgebraicGeometry.ComplexPoint
