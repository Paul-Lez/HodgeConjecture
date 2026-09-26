/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalytificationStalk
public import Other.AlgebraicGeometry.ComplexPointClosedPointEquiv
public import Other.AlgebraicGeometry.InvertibleSheafStalk
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.FiniteStalk
public import Other.RingTheory.FaithfullyFlatRankOne

/-!
# Rank-one descent along the analytification stalk map

An algebraic module stalk is free of rank one when its analytification stalk is free of rank one
and the comparison of local rings is faithfully flat.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

/-- Rank one descends from an analytified stalk along a faithfully flat comparison map. -/
theorem exists_algebraicStalkLinearEquiv_of_analytification
    (F : X.left.Modules) (z : ComplexPoint X)
    [Module.Finite (X.left.presheaf.stalk z.underlying)
      ((SheafOfModules.stalkFunctor
        (R := X.left.presheaf) (hR := X.left.ringCatSheaf.property) z.underlying).obj F)]
    (hff : ((analytificationToPresheafedSpace X d).stalkMap z).hom.FaithfullyFlat)
    (e : ((SheafOfModules.stalkFunctor
          (R := (holomorphicFunctionSheaf X d).presheaf)
          (hR := (holomorphicRingSheaf X d).property) z).obj
        ((moduleAnalytification X d).obj F)) ≃ₗ[
          (holomorphicFunctionSheaf X d).presheaf.stalk z]
        (holomorphicFunctionSheaf X d).presheaf.stalk z) :
    Nonempty (((SheafOfModules.stalkFunctor
      (R := X.left.presheaf) (hR := X.left.ringCatSheaf.property) z.underlying).obj F) ≃ₗ[
      X.left.presheaf.stalk z.underlying] X.left.presheaf.stalk z.underlying) := by
  exact Module.exists_linearEquiv_self_of_faithfullyFlat_extendScalars
    (X.left.presheaf.stalk z.underlying)
    ((holomorphicFunctionSheaf X d).presheaf.stalk z)
    ((analytificationToPresheafedSpace X d).stalkMap z).hom
    ((SheafOfModules.stalkFunctor
      (R := X.left.presheaf) (hR := X.left.ringCatSheaf.property) z.underlying).obj F)
    hff
    (((moduleAnalytificationStalkIso X d z).app F).symm.toLinearEquiv.trans e)

/-- Rank one descends from an analytic model isomorphic to an analytified module. -/
theorem exists_algebraicStalkLinearEquiv_of_analytificationIso
    (F : X.left.Modules) (M : SheafOfModules.{0} (holomorphicRingSheaf X d))
    (z : ComplexPoint X)
    [Module.Finite (X.left.presheaf.stalk z.underlying)
      ((SheafOfModules.stalkFunctor
        (R := X.left.presheaf) (hR := X.left.ringCatSheaf.property) z.underlying).obj F)]
    (hff : ((analytificationToPresheafedSpace X d).stalkMap z).hom.FaithfullyFlat)
    (eFM : (moduleAnalytification X d).obj F ≅ M)
    (eM : ((SheafOfModules.stalkFunctor
          (R := (holomorphicFunctionSheaf X d).presheaf)
          (hR := (holomorphicRingSheaf X d).property) z).obj M) ≃ₗ[
            (holomorphicFunctionSheaf X d).presheaf.stalk z]
          (holomorphicFunctionSheaf X d).presheaf.stalk z) :
    Nonempty (((SheafOfModules.stalkFunctor
      (R := X.left.presheaf) (hR := X.left.ringCatSheaf.property) z.underlying).obj F) ≃ₗ[
        X.left.presheaf.stalk z.underlying] X.left.presheaf.stalk z.underlying) :=
  exists_algebraicStalkLinearEquiv_of_analytification X d F z hff
    (((SheafOfModules.stalkFunctor
      (R := (holomorphicFunctionSheaf X d).presheaf)
      (hR := (holomorphicRingSheaf X d).property) z).mapIso eFM).toLinearEquiv.trans eM)

/-- The algebraic stalk of a coherent model of an analytic line bundle is free of rank one when
the analytification stalk map is faithfully flat. -/
theorem exists_algebraicStalkLinearEquiv_of_isInvertible
    (F : X.left.Modules) (M : SheafOfModules.{0} (holomorphicRingSheaf X d))
    (z : ComplexPoint X)
    [Module.Finite (X.left.presheaf.stalk z.underlying)
      ((SheafOfModules.stalkFunctor
        (R := X.left.presheaf) (hR := X.left.ringCatSheaf.property) z.underlying).obj F)]
    (hff : ((analytificationToPresheafedSpace X d).stalkMap z).hom.FaithfullyFlat)
    (eFM : (moduleAnalytification X d).obj F ≅ M)
    (hM : TauCeti.SheafOfModules.IsInvertible M) :
    Nonempty (((SheafOfModules.stalkFunctor
      (R := X.left.presheaf) (hR := X.left.ringCatSheaf.property) z.underlying).obj F) ≃ₗ[
        X.left.presheaf.stalk z.underlying] X.left.presheaf.stalk z.underlying) := by
  let Y := holomorphicLocallyRingedSpace X d
  have hMY : TauCeti.SheafOfModules.IsInvertible
      (show SheafOfModules.{0} Y.ringSheaf from M) := hM
  exact exists_algebraicStalkLinearEquiv_of_analytificationIso X d F M z hff eFM
    (@AlgebraicGeometry.LocallyRingedSpace.nonempty_stalkLinearEquiv_of_isInvertible
      Y (show SheafOfModules.{0} Y.ringSheaf from M) hMY z).some

/-- The stalk of an algebraic model of an analytic line bundle is free of rank one at every
closed point. -/
theorem exists_algebraicStalkLinearEquiv_of_isInvertible_closedPoint
    [LocallyOfFiniteType X.hom]
    (F : X.left.Modules) (M : SheafOfModules.{0} (holomorphicRingSheaf X d))
    [F.IsFiniteType] (x : closedPoints X.left)
    (hff : ∀ z : ComplexPoint X,
      ((analytificationToPresheafedSpace X d).stalkMap z).hom.FaithfullyFlat)
    (eFM : (moduleAnalytification X d).obj F ≅ M)
    (hM : TauCeti.SheafOfModules.IsInvertible M) :
    Nonempty (((SheafOfModules.stalkFunctor
      (R := X.left.presheaf) (hR := X.left.ringCatSheaf.property) x.1).obj F) ≃ₗ[
        X.left.presheaf.stalk x.1] X.left.presheaf.stalk x.1) := by
  have hF : F.IsFiniteType := inferInstance
  let Y := X.left.toLocallyRingedSpace
  have hFY : (show SheafOfModules.{0} Y.ringSheaf from F).IsFiniteType := hF
  let : Module.Finite (X.left.presheaf.stalk x.1)
      ((SheafOfModules.stalkFunctor
        (R := X.left.presheaf) (hR := X.left.ringCatSheaf.property) x.1).obj F) :=
    @AlgebraicGeometry.LocallyRingedSpace.finite_stalk_of_isFiniteType Y
      (show SheafOfModules.{0} Y.ringSheaf from F) hFY x.1
  let z := (complexPointEquivClosedPoint X).symm x
  have hz : z.underlying = x.1 := congrArg Subtype.val
    ((complexPointEquivClosedPoint X).apply_symm_apply x)
  let : Module.Finite (X.left.presheaf.stalk z.underlying)
      ((SheafOfModules.stalkFunctor
        (R := X.left.presheaf) (hR := X.left.ringCatSheaf.property) z.underlying).obj F) := by
    rw [hz]
    infer_instance
  rw [← hz]
  exact exists_algebraicStalkLinearEquiv_of_isInvertible X d F M z (hff z) eFM hM

end AlgebraicGeometry.ComplexPoint
