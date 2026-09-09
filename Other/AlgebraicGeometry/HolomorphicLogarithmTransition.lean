/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicUnitObstruction

/-!
# Computing the exponential obstruction from actual local logarithms

If two holomorphic logarithms of a global unit differ by an actual integral-period
section on the overlap, the Mayer–Vietoris class of that integer section is precisely
the exponential obstruction. The comparison is proved by a morphism between the actual
short exact sequences, so its normalization retains the displayed `2πi` period map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 5000

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

local instance logarithmTransitionSheafAbelian : Abelian (AnalyticAdditiveSheaf X) :=
  CategoryTheory.sheafIsAbelian

local instance logarithmTransitionHasExt : HasExt.{1} (AnalyticAdditiveSheaf X) := analyticHasExt X

/-- The right Mayer–Vietoris map represents the restrictions of a global section. -/
theorem analyticMayerVietoris_sum (F : AnalyticAdditiveSheaf X)
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (a : F.obj.obj (.op ⊤)) :
    (analyticCoverMayerVietorisSquare X U V hcover).shortComplex.g ≫
      analyticSectionSheafHom X F ⊤ a =
    biprod.desc
      (analyticSectionSheafHom X F U (F.obj.map (homOfLE le_top).op a))
      (analyticSectionSheafHom X F V (F.obj.map (homOfLE le_top).op a)) := by
  change biprod.desc (analyticOpenFreeAbelianMap X (homOfLE le_top))
    (analyticOpenFreeAbelianMap X (homOfLE le_top)) ≫ analyticSectionSheafHom X F ⊤ a = _
  apply biprod.hom_ext'
  · simp only [← Category.assoc, biprod.inl_desc]
    exact analyticOpenFreeAbelianMap_comp_section X F (homOfLE le_top) a
  · simp only [← Category.assoc, biprod.inr_desc]
    exact analyticOpenFreeAbelianMap_comp_section X F (homOfLE le_top) a

variable (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- Actual local logarithms define a morphism from the Mayer–Vietoris resolution to the
exponential sequence, with the overlap integer section as the left component. -/
def holomorphicLogarithmCoverMorphism
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (u : (OpenHolomorphicFunctions X d (.op ⊤))ˣ)
    (fU : OpenHolomorphicFunctions X d (.op U)) (fV : OpenHolomorphicFunctions X d (.op V))
    (n : (constantIntegerSheaf X).obj.obj (.op (U ⊓ V)))
    (hU : holomorphicExpUnit X d (.op U) fU =
      Units.map (holomorphicRestrictionAlgHom X d (homOfLE le_top).op).toMonoidHom u)
    (hV : holomorphicExpUnit X d (.op V) fV =
      Units.map (holomorphicRestrictionAlgHom X d (homOfLE le_top).op).toMonoidHom u)
    (hn : holomorphicRestrictionAlgHom X d (homOfLE inf_le_left).op fU -
        holomorphicRestrictionAlgHom X d (homOfLE inf_le_right).op fV =
      (holomorphicIntegerPeriodSheaf X d).hom.app (.op (U ⊓ V)) n) :
    (analyticCoverMayerVietorisSquare X U V hcover).shortComplex ⟶
      holomorphicExponentialSequence X d where
  τ₁ := analyticSectionSheafHom X (constantIntegerSheaf X) (U ⊓ V) n
  τ₂ := biprod.desc (analyticSectionSheafHom X (holomorphicAdditiveFunctionSheaf X d) U fU)
    (analyticSectionSheafHom X (holomorphicAdditiveFunctionSheaf X d) V fV)
  τ₃ := analyticSectionSheafHom X (holomorphicUnitsSheaf X d) ⊤ (Additive.ofMul u)
  comm₁₂ := by
    symm
    exact (analyticMayerVietoris_difference X (holomorphicAdditiveFunctionSheaf X d)
      U V hcover fU fV).trans
      ((congrArg (analyticSectionSheafHom X (holomorphicAdditiveFunctionSheaf X d) (U ⊓ V)) hn).trans
        (analyticSectionSheafHom_postcomp X (constantIntegerSheaf X)
          (holomorphicAdditiveFunctionSheaf X d) (holomorphicIntegerPeriodSheaf X d) (U ⊓ V) n).symm)
  comm₂₃ := by
    symm
    change (analyticCoverMayerVietorisSquare X U V hcover).shortComplex.g ≫
      analyticSectionSheafHom X (holomorphicUnitsSheaf X d) ⊤ (Additive.ofMul u) =
      biprod.desc (analyticSectionSheafHom X (holomorphicAdditiveFunctionSheaf X d) U fU)
        (analyticSectionSheafHom X (holomorphicAdditiveFunctionSheaf X d) V fV) ≫
          holomorphicExpSheaf X d
    rw [analyticMayerVietoris_sum]
    apply biprod.hom_ext'
    · simp only [← Category.assoc, biprod.inl_desc]
      exact (congrArg (fun v => analyticSectionSheafHom X (holomorphicUnitsSheaf X d) U
        (Additive.ofMul v)) hU).symm.trans
          (analyticSectionSheafHom_postcomp X (holomorphicAdditiveFunctionSheaf X d)
            (holomorphicUnitsSheaf X d) (holomorphicExpSheaf X d) U fU).symm
    · simp only [← Category.assoc, biprod.inr_desc]
      exact (congrArg (fun v => analyticSectionSheafHom X (holomorphicUnitsSheaf X d) V
        (Additive.ofMul v)) hV).symm.trans
          (analyticSectionSheafHom_postcomp X (holomorphicAdditiveFunctionSheaf X d)
            (holomorphicUnitsSheaf X d) (holomorphicExpSheaf X d) V fV).symm

/-- The integer-period transition class computes the actual exponential obstruction, with
the canonical constant-integer source identification. -/
theorem holomorphicLogarithmTransition_class
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (u : (OpenHolomorphicFunctions X d (.op ⊤))ˣ)
    (fU : OpenHolomorphicFunctions X d (.op U)) (fV : OpenHolomorphicFunctions X d (.op V))
    (n : (constantIntegerSheaf X).obj.obj (.op (U ⊓ V)))
    (hU : holomorphicExpUnit X d (.op U) fU =
      Units.map (holomorphicRestrictionAlgHom X d (homOfLE le_top).op).toMonoidHom u)
    (hV : holomorphicExpUnit X d (.op V) fV =
      Units.map (holomorphicRestrictionAlgHom X d (homOfLE le_top).op).toMonoidHom u)
    (hn : holomorphicRestrictionAlgHom X d (homOfLE inf_le_left).op fU -
        holomorphicRestrictionAlgHom X d (homOfLE inf_le_right).op fV =
      (holomorphicIntegerPeriodSheaf X d).hom.app (.op (U ⊓ V)) n) :
    analyticTransitionExtClass X (constantIntegerSheaf X) U V hcover n =
      (Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso X).inv).comp
        (holomorphicUnitLogarithmObstruction X d ⊤ u) (show 0 + 1 = 1 from rfl) := by
  let φ := holomorphicLogarithmCoverMorphism X d U V hcover u fU fV n hU hV hn
  have h := ShortComplex.ShortExact.extClass_naturality (C := AnalyticAdditiveSheaf X)
    (analyticCoverMayerVietorisSquare X U V hcover).shortComplex_shortExact
      (holomorphicExponentialSequence_shortExact X d) φ
  exact congrArg (fun z : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X ⊤)
      (constantIntegerSheaf X) 1 =>
        (Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso X).inv).comp z
          (show 0 + 1 = 1 from rfl)) h

end AlgebraicGeometry.ComplexPoint
