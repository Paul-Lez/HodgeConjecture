/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Algebra.DeRham.Logarithmic
public import HodgeConjecture.Definitions.AlgebraicGeometry.HolomorphicDeRham
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.MonCat.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Holomorphic logarithmic forms

The logarithmic forms of holomorphic units are actual elements of the repository's analytic
de Rham complex. They are closed, and restriction commutes with their construction. In degree
one, `dlog` gives a morphism from the sheaf of holomorphic units to closed holomorphic one-forms.
This is the local de Rham construction used in the filtered divisor-class map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ) (d : ℕ) [SmoothOfRelativeDimension d s]

/-- The logarithmic form of a tuple of nowhere-vanishing holomorphic functions. -/
def holomorphicLogarithmicForm
    (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ) (p : ℕ)
    (u : Fin p → (OpenHolomorphicFunctions s d U)ˣ) : HolomorphicForm s d U p :=
  algebraicFormToHolomorphicForm s d U p
    (Algebra.DeRham.logarithmicForm ℂ (OpenHolomorphicFunctions s d U) p u)

/-- Logarithmic forms are closed under the actual analytic exterior derivative. -/
@[simp]
theorem holomorphicFormDifferential_logarithmicForm
    (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ) (p : ℕ)
    (u : Fin p → (OpenHolomorphicFunctions s d U)ˣ) :
    holomorphicFormDifferential s d U p (holomorphicLogarithmicForm s d U p u) = 0 := by
  rw [holomorphicLogarithmicForm, holomorphicFormDifferential_algebraicFormToHolomorphicForm,
    Algebra.DeRham.differential_logarithmicForm, map_zero]

/-- Restriction of logarithmic forms is the logarithmic form of the restricted units. -/
@[simp]
theorem holomorphicFormRestriction_logarithmicForm
    {U V : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (u : Fin p → (OpenHolomorphicFunctions s d U)ˣ) :
    holomorphicFormRestriction s d i p (holomorphicLogarithmicForm s d U p u) =
      holomorphicLogarithmicForm s d V p
        (fun j => Units.map (holomorphicRestrictionAlgHom s d i).toMonoidHom (u j)) := by
  rw [holomorphicLogarithmicForm, holomorphicFormRestriction_algebraicFormToHolomorphicForm,
    Algebra.DeRham.map_logarithmicForm]
  rfl

/-- Units regarded additively, as needed for their sheaf cohomology. -/
def holomorphicUnitsPresheaf : TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X s)) :=
  holomorphicFunctionPresheaf s d ⋙ forget₂ CommRingCat CommMonCat ⋙
    CommMonCat.units ⋙ CommGrpCat.toAddCommGrp

/-- The actual sheaf of holomorphic units, with its multiplicative group written additively. -/
def holomorphicUnitsSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X s)) :=
  letI : CreatesLimitsOfSize.{0, 0} (forget CommMonCat) :=
    { CreatesLimitsOfShape := fun {_ _} => { CreatesLimit := fun {_} => inferInstance } }
  letI : PreservesLimitsOfSize.{0, 0} (forget₂ CommRingCat CommMonCat) :=
    preservesLimits_of_reflects_of_preserves _ (forget CommMonCat)
  letI : CommGrpCat.toAddCommGrp.IsEquivalence :=
    inferInstanceAs commGroupAddCommGroupEquivalence.functor.IsEquivalence
  (sheafCompose (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s)))
    (forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙ CommGrpCat.toAddCommGrp)).obj
      (holomorphicFunctionSheaf s d)

/-- The logarithmic differential as a morphism of presheaves of abelian groups. -/
def holomorphicDlogPresheaf : holomorphicUnitsPresheaf s d ⟶
    holomorphicDeRhamPresheaf s d 1 where
  app U := AddCommGrpCat.ofHom {
    toFun u := holomorphicLogarithmicForm s d U 1 (fun _ => u.toMul)
    map_zero' := by
      change algebraicFormToHolomorphicForm s d U 1
        (Algebra.DeRham.dlog ℂ (OpenHolomorphicFunctions s d U) 1) = 0
      rw [Algebra.DeRham.dlog_one, map_zero]
    map_add' u v := by
      change algebraicFormToHolomorphicForm s d U 1
        (Algebra.DeRham.dlog ℂ (OpenHolomorphicFunctions s d U) (u.toMul * v.toMul)) = _
      rw [Algebra.DeRham.dlog_mul ℂ (OpenHolomorphicFunctions s d U), map_add]
      rfl }
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro u
    exact (holomorphicFormRestriction_logarithmicForm s d i 1 (fun _ => u.toMul)).symm

/-- The logarithmic differential lands in closed one-forms. -/
theorem holomorphicDlogPresheaf_comp_differential :
    holomorphicDlogPresheaf s d ≫ holomorphicDeRhamDifferential s d 1 = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro u
  exact holomorphicFormDifferential_logarithmicForm s d U 1 (fun _ => u.toMul)

/-- The actual logarithmic derivative from holomorphic units to holomorphic one-forms. -/
def holomorphicDlogSheaf : holomorphicUnitsSheaf s d ⟶ holomorphicDeRhamSheaf s d 1 :=
  ⟨holomorphicDlogPresheaf s d ≫
    toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s)))
      (holomorphicDeRhamPresheaf s d 1)⟩

/-- Sheafification preserves the proved closedness of logarithmic derivatives. -/
theorem holomorphicDlogSheaf_comp_differential :
    holomorphicDlogSheaf s d ≫ holomorphicDeRhamSheafDifferential s d 1 = 0 := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  change holomorphicDlogPresheaf s d ≫
      toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s))) _ ≫
        sheafifyMap _ (holomorphicDeRhamDifferential s d 1) = 0
  rw [← toSheafify_naturality, ← Category.assoc,
    holomorphicDlogPresheaf_comp_differential, zero_comp]

/-- The logarithmic derivative, as a cochain map from units placed in degree one. -/
def holomorphicDlogComplex :
    (HomologicalComplex.single _ (ComplexShape.up ℕ) 1).obj (holomorphicUnitsSheaf s d) ⟶
      holomorphicDeRhamComplex s d :=
  HomologicalComplex.mkHomFromSingle (holomorphicDlogSheaf s d) (by
    intro k hk
    have hk' : k = 2 := by simpa using hk.symm
    subst k
    exact holomorphicDlogSheaf_comp_differential s d)

end AlgebraicGeometry.ComplexPoint
