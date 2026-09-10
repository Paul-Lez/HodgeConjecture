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

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ)

local instance logarithmTransitionSheafAbelian : Abelian (AnalyticAdditiveSheaf s) :=
  CategoryTheory.sheafIsAbelian

local instance logarithmTransitionHasExt : HasExt.{1} (AnalyticAdditiveSheaf s) := analyticHasExt s

/-- The right Mayer–Vietoris map represents the restrictions of a global section. -/
theorem analyticMayerVietoris_sum (F : AnalyticAdditiveSheaf s)
    (U V : Opens (TopCat.of (ComplexPoint X s))) (hcover : U ⊔ V = ⊤)
    (a : F.obj.obj (.op ⊤)) :
    (analyticCoverMayerVietorisSquare s U V hcover).shortComplex.g ≫
      analyticSectionSheafHom s F ⊤ a =
    biprod.desc
      (analyticSectionSheafHom s F U (F.obj.map (homOfLE le_top).op a))
      (analyticSectionSheafHom s F V (F.obj.map (homOfLE le_top).op a)) := by
  change biprod.desc (analyticOpenFreeAbelianMap s (homOfLE le_top))
    (analyticOpenFreeAbelianMap s (homOfLE le_top)) ≫ analyticSectionSheafHom s F ⊤ a = _
  apply biprod.hom_ext'
  · simp only [← Category.assoc, biprod.inl_desc]
    exact analyticOpenFreeAbelianMap_comp_section s F (homOfLE le_top) a
  · simp only [← Category.assoc, biprod.inr_desc]
    exact analyticOpenFreeAbelianMap_comp_section s F (homOfLE le_top) a

variable (d : ℕ) [SmoothOfRelativeDimension d s]

/-- Actual local logarithms define a morphism from the Mayer–Vietoris resolution to the
exponential sequence, with the overlap integer section as the left component. -/
def holomorphicLogarithmCoverMorphism
    (U V : Opens (TopCat.of (ComplexPoint X s))) (hcover : U ⊔ V = ⊤)
    (u : (OpenHolomorphicFunctions s d (.op ⊤))ˣ)
    (fU : OpenHolomorphicFunctions s d (.op U)) (fV : OpenHolomorphicFunctions s d (.op V))
    (n : (constantIntegerSheaf s).obj.obj (.op (U ⊓ V)))
    (hU : holomorphicExpUnit s d (.op U) fU =
      Units.map (holomorphicRestrictionAlgHom s d (homOfLE le_top).op).toMonoidHom u)
    (hV : holomorphicExpUnit s d (.op V) fV =
      Units.map (holomorphicRestrictionAlgHom s d (homOfLE le_top).op).toMonoidHom u)
    (hn : holomorphicRestrictionAlgHom s d (homOfLE inf_le_left).op fU -
        holomorphicRestrictionAlgHom s d (homOfLE inf_le_right).op fV =
      (holomorphicIntegerPeriodSheaf s d).hom.app (.op (U ⊓ V)) n) :
    (analyticCoverMayerVietorisSquare s U V hcover).shortComplex ⟶
      holomorphicExponentialSequence s d where
  τ₁ := analyticSectionSheafHom s (constantIntegerSheaf s) (U ⊓ V) n
  τ₂ := biprod.desc (analyticSectionSheafHom s (holomorphicAdditiveFunctionSheaf s d) U fU)
    (analyticSectionSheafHom s (holomorphicAdditiveFunctionSheaf s d) V fV)
  τ₃ := analyticSectionSheafHom s (holomorphicUnitsSheaf s d) ⊤ (Additive.ofMul u)
  comm₁₂ := by
    symm
    exact (analyticMayerVietoris_difference s (holomorphicAdditiveFunctionSheaf s d)
      U V hcover fU fV).trans
      ((congrArg (analyticSectionSheafHom s (holomorphicAdditiveFunctionSheaf s d) (U ⊓ V)) hn).trans
        (analyticSectionSheafHom_postcomp s (constantIntegerSheaf s)
          (holomorphicAdditiveFunctionSheaf s d) (holomorphicIntegerPeriodSheaf s d) (U ⊓ V) n).symm)
  comm₂₃ := by
    symm
    change (analyticCoverMayerVietorisSquare s U V hcover).shortComplex.g ≫
      analyticSectionSheafHom s (holomorphicUnitsSheaf s d) ⊤ (Additive.ofMul u) =
      biprod.desc (analyticSectionSheafHom s (holomorphicAdditiveFunctionSheaf s d) U fU)
        (analyticSectionSheafHom s (holomorphicAdditiveFunctionSheaf s d) V fV) ≫
          holomorphicExpSheaf s d
    rw [analyticMayerVietoris_sum]
    apply biprod.hom_ext'
    · simp only [← Category.assoc, biprod.inl_desc]
      exact (congrArg (fun v => analyticSectionSheafHom s (holomorphicUnitsSheaf s d) U
        (Additive.ofMul v)) hU).symm.trans
          (analyticSectionSheafHom_postcomp s (holomorphicAdditiveFunctionSheaf s d)
            (holomorphicUnitsSheaf s d) (holomorphicExpSheaf s d) U fU).symm
    · simp only [← Category.assoc, biprod.inr_desc]
      exact (congrArg (fun v => analyticSectionSheafHom s (holomorphicUnitsSheaf s d) V
        (Additive.ofMul v)) hV).symm.trans
          (analyticSectionSheafHom_postcomp s (holomorphicAdditiveFunctionSheaf s d)
            (holomorphicUnitsSheaf s d) (holomorphicExpSheaf s d) V fV).symm

/-- The integer-period transition class computes the actual exponential obstruction, with
the canonical constant-integer source identification. -/
theorem holomorphicLogarithmTransition_class
    (U V : Opens (TopCat.of (ComplexPoint X s))) (hcover : U ⊔ V = ⊤)
    (u : (OpenHolomorphicFunctions s d (.op ⊤))ˣ)
    (fU : OpenHolomorphicFunctions s d (.op U)) (fV : OpenHolomorphicFunctions s d (.op V))
    (n : (constantIntegerSheaf s).obj.obj (.op (U ⊓ V)))
    (hU : holomorphicExpUnit s d (.op U) fU =
      Units.map (holomorphicRestrictionAlgHom s d (homOfLE le_top).op).toMonoidHom u)
    (hV : holomorphicExpUnit s d (.op V) fV =
      Units.map (holomorphicRestrictionAlgHom s d (homOfLE le_top).op).toMonoidHom u)
    (hn : holomorphicRestrictionAlgHom s d (homOfLE inf_le_left).op fU -
        holomorphicRestrictionAlgHom s d (homOfLE inf_le_right).op fV =
      (holomorphicIntegerPeriodSheaf s d).hom.app (.op (U ⊓ V)) n) :
    analyticTransitionExtClass s (constantIntegerSheaf s) U V hcover n =
      (Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso s).inv).comp
        (holomorphicUnitLogarithmObstruction s d ⊤ u) (show 0 + 1 = 1 from rfl) := by
  let φ := holomorphicLogarithmCoverMorphism s d U V hcover u fU fV n hU hV hn
  have h := ShortComplex.ShortExact.extClass_naturality (C := AnalyticAdditiveSheaf s)
    (analyticCoverMayerVietorisSquare s U V hcover).shortComplex_shortExact
      (holomorphicExponentialSequence_shortExact s d) φ
  exact congrArg (fun z : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf s ⊤)
      (constantIntegerSheaf s) 1 =>
        (Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso s).inv).comp z
          (show 0 + 1 = 1 from rfl)) h

end AlgebraicGeometry.ComplexPoint
