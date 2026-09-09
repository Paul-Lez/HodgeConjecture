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

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- The logarithmic form of a tuple of nowhere-vanishing holomorphic functions. -/
def holomorphicLogarithmicForm
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (u : Fin p → (OpenHolomorphicFunctions X d U)ˣ) : HolomorphicForm X d U p :=
  algebraicFormToHolomorphicForm X d U p
    (Algebra.DeRham.logarithmicForm ℂ (OpenHolomorphicFunctions X d U) p u)

/-- Logarithmic forms are closed under the actual analytic exterior derivative. -/
@[simp]
theorem holomorphicFormDifferential_logarithmicForm
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (u : Fin p → (OpenHolomorphicFunctions X d U)ˣ) :
    holomorphicFormDifferential X d U p (holomorphicLogarithmicForm X d U p u) = 0 := by
  rw [holomorphicLogarithmicForm, holomorphicFormDifferential_algebraicFormToHolomorphicForm,
    Algebra.DeRham.differential_logarithmicForm, map_zero]

/-- Restriction of logarithmic forms is the logarithmic form of the restricted units. -/
@[simp]
theorem holomorphicFormRestriction_logarithmicForm
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (u : Fin p → (OpenHolomorphicFunctions X d U)ˣ) :
    holomorphicFormRestriction X d i p (holomorphicLogarithmicForm X d U p u) =
      holomorphicLogarithmicForm X d V p
        (fun j => Units.map (holomorphicRestrictionAlgHom X d i).toMonoidHom (u j)) := by
  rw [holomorphicLogarithmicForm, holomorphicFormRestriction_algebraicFormToHolomorphicForm,
    Algebra.DeRham.map_logarithmicForm]
  rfl

/-- Units regarded additively, as needed for their sheaf cohomology. -/
def holomorphicUnitsPresheaf : TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
  holomorphicFunctionPresheaf X d ⋙ forget₂ CommRingCat CommMonCat ⋙
    CommMonCat.units ⋙ CommGrpCat.toAddCommGrp

/-- The actual sheaf of holomorphic units, with its multiplicative group written additively. -/
def holomorphicUnitsSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
  letI : CreatesLimitsOfSize.{0, 0} (forget CommMonCat) :=
    { CreatesLimitsOfShape := fun {_ _} => { CreatesLimit := fun {_} => inferInstance } }
  letI : PreservesLimitsOfSize.{0, 0} (forget₂ CommRingCat CommMonCat) :=
    preservesLimits_of_reflects_of_preserves _ (forget CommMonCat)
  letI : CommGrpCat.toAddCommGrp.IsEquivalence :=
    inferInstanceAs commGroupAddCommGroupEquivalence.functor.IsEquivalence
  (sheafCompose (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙ CommGrpCat.toAddCommGrp)).obj
      (holomorphicFunctionSheaf X d)

/-- The logarithmic differential as a morphism of presheaves of abelian groups. -/
def holomorphicDlogPresheaf : holomorphicUnitsPresheaf X d ⟶
    holomorphicDeRhamPresheaf X d 1 where
  app U := AddCommGrpCat.ofHom {
    toFun u := holomorphicLogarithmicForm X d U 1 (fun _ => u.toMul)
    map_zero' := by
      change algebraicFormToHolomorphicForm X d U 1
        (Algebra.DeRham.dlog ℂ (OpenHolomorphicFunctions X d U) 1) = 0
      rw [Algebra.DeRham.dlog_one, map_zero]
    map_add' u v := by
      change algebraicFormToHolomorphicForm X d U 1
        (Algebra.DeRham.dlog ℂ (OpenHolomorphicFunctions X d U) (u.toMul * v.toMul)) = _
      rw [Algebra.DeRham.dlog_mul ℂ (OpenHolomorphicFunctions X d U), map_add]
      rfl }
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro u
    exact (holomorphicFormRestriction_logarithmicForm X d i 1 (fun _ => u.toMul)).symm

/-- The logarithmic differential lands in closed one-forms. -/
theorem holomorphicDlogPresheaf_comp_differential :
    holomorphicDlogPresheaf X d ≫ holomorphicDeRhamDifferential X d 1 = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro u
  exact holomorphicFormDifferential_logarithmicForm X d U 1 (fun _ => u.toMul)

/-- The actual logarithmic derivative from holomorphic units to holomorphic one-forms. -/
def holomorphicDlogSheaf : holomorphicUnitsSheaf X d ⟶ holomorphicDeRhamSheaf X d 1 :=
  ⟨holomorphicDlogPresheaf X d ≫
    toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d 1)⟩

/-- Sheafification preserves the proved closedness of logarithmic derivatives. -/
theorem holomorphicDlogSheaf_comp_differential :
    holomorphicDlogSheaf X d ≫ holomorphicDeRhamSheafDifferential X d 1 = 0 := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  change holomorphicDlogPresheaf X d ≫
      toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) _ ≫
        sheafifyMap _ (holomorphicDeRhamDifferential X d 1) = 0
  rw [← toSheafify_naturality, ← Category.assoc,
    holomorphicDlogPresheaf_comp_differential, zero_comp]

/-- The logarithmic derivative, as a cochain map from units placed in degree one. -/
def holomorphicDlogComplex :
    (HomologicalComplex.single _ (ComplexShape.up ℕ) 1).obj (holomorphicUnitsSheaf X d) ⟶
      holomorphicDeRhamComplex X d :=
  HomologicalComplex.mkHomFromSingle (holomorphicDlogSheaf X d) (by
    intro k hk
    have hk' : k = 2 := by simpa using hk.symm
    subst k
    exact holomorphicDlogSheaf_comp_differential X d)

end AlgebraicGeometry.ComplexPoint
