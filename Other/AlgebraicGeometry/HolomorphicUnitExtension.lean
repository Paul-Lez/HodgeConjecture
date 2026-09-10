/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicIntegralHodgeClass
public import Other.AlgebraicTopology.SheafExtensionLocalLifts
public import Other.CategoryTheory.Abelian.ExtOneRepresentative
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Sheaf extensions representing holomorphic Chern-class lifts

We realize classes in `H¹(𝒪ˣ)` by extensions `0 → 𝒪ˣ → E → ℤ → 0`.
Local lifts of the integer section `1` produce the transition functions for the
associated holomorphic line bundle.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance holomorphicUnitExtensionTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

/-- An extension of the constant integer sheaf by the additive form of holomorphic units. -/
structure HolomorphicUnitExtension where
  /-- The middle sheaf of the extension. -/
  middle : AnalyticAdditiveSheaf X
  /-- Inclusion of the holomorphic units. -/
  inclusion : holomorphicUnitSheaf X d ⟶ middle
  /-- Projection to the constant integer sheaf. -/
  projection : middle ⟶ constantIntegerSheaf X
  /-- Consecutive arrows have zero composite. -/
  zero : inclusion ≫ projection = 0
  /-- The extension is short exact. -/
  shortExact : (ShortComplex.mk inclusion projection zero).ShortExact

namespace HolomorphicUnitExtension

variable {X d}

/-- The short complex underlying an extension. -/
abbrev shortComplex (E : HolomorphicUnitExtension X d) :=
  ShortComplex.mk E.inclusion E.projection E.zero

/-- The degree-one sheaf cohomology class of an extension. -/
def cohomologyClass (E : HolomorphicUnitExtension X d) :
    Abelian.Ext.{1} (constantIntegerSheaf X) (holomorphicUnitSheaf X d) 1 :=
  E.shortExact.extClass

/-- The integral first Chern class of an extension, in the project's cohomology presentation. -/
def firstChernClass (E : HolomorphicUnitExtension X d) : IntegralCohomology X 2 :=
  (analyticSheafCohomologyEquivExt X (constantIntegerSheaf X) 2).symm
    (holomorphicFirstChernClass X d E.cohomologyClass)

variable (X d)

/-- Every degree-one class of the holomorphic-unit sheaf is represented by an extension. -/
theorem exists_cohomologyClass
    (β : Abelian.Ext.{1} (constantIntegerSheaf X) (holomorphicUnitSheaf X d) 1) :
    ∃ E : HolomorphicUnitExtension X d, E.cohomologyClass = β := by
  obtain ⟨M, i, p, w, h, hβ⟩ := Abelian.Ext.exists_shortExact β
  exact ⟨⟨M, i, p, w, h⟩, hβ⟩

variable {X d}

/-- The constant integer section `1` on the whole analytic space. -/
def integerOneSection : (constantIntegerSheaf X).obj.obj
    (op (⊤ : Opens (TopCat.of (ComplexPoint X)))) :=
  (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    ((Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).obj (AddCommGrpCat.of ℤ))).app
      (op ⊤) (1 : ℤ)

/-- Chosen local lifts of the integer section `1` through the extension. -/
def localLifts (E : HolomorphicUnitExtension X d) :
    TopCat.Sheaf.ExtensionLocalLifts E.shortComplex integerOneSection :=
  TopCat.Sheaf.ExtensionLocalLifts.choose E.shortComplex E.shortExact integerOneSection

end HolomorphicUnitExtension

/-- Integral Hodge classes are first Chern classes of extensions by holomorphic units. -/
theorem exists_holomorphicUnitExtension_of_integral_hodgeClass [IsIntegral X.left] [Smooth X.hom]
    (α : IntegralCohomology X 2)
    (hα : integralToRationalCohomology X 2 α ∈ hodgeClasses ℚ X 1) :
    ∃ E : HolomorphicUnitExtension X (dim X.left), E.firstChernClass = α := by
  obtain ⟨β, hβ⟩ := exists_holomorphicFirstChernClass_of_integral_hodgeClass X α hα
  obtain ⟨E, hE⟩ := HolomorphicUnitExtension.exists_cohomologyClass X (dim X.left) β
  refine ⟨E, ?_⟩
  apply (analyticSheafCohomologyEquivExt X (constantIntegerSheaf X) 2).injective
  rw [HolomorphicUnitExtension.firstChernClass, Equiv.apply_symm_apply, hE, hβ]

end AlgebraicGeometry.ComplexPoint
