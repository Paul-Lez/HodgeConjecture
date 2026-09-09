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

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ) (d : ℕ) [SmoothOfRelativeDimension d s]

local instance holomorphicUnitExtensionTopology : TopologicalSpace (ComplexPoint X s) :=
  Point.analyticTopology

/-- An extension of the constant integer sheaf by the additive form of holomorphic units. -/
structure HolomorphicUnitExtension where
  /-- The middle sheaf of the extension. -/
  middle : AnalyticAdditiveSheaf s
  /-- Inclusion of the holomorphic units. -/
  inclusion : holomorphicUnitSheaf s d ⟶ middle
  /-- Projection to the constant integer sheaf. -/
  projection : middle ⟶ constantIntegerSheaf s
  /-- Consecutive arrows have zero composite. -/
  zero : inclusion ≫ projection = 0
  /-- The extension is short exact. -/
  shortExact : (ShortComplex.mk inclusion projection zero).ShortExact

namespace HolomorphicUnitExtension

variable {s d}

/-- The short complex underlying an extension. -/
abbrev shortComplex (E : HolomorphicUnitExtension s d) :=
  ShortComplex.mk E.inclusion E.projection E.zero

/-- The degree-one sheaf cohomology class of an extension. -/
def cohomologyClass (E : HolomorphicUnitExtension s d) :
    Abelian.Ext.{1} (constantIntegerSheaf s) (holomorphicUnitSheaf s d) 1 :=
  E.shortExact.extClass

/-- The integral first Chern class of an extension, in the project's cohomology presentation. -/
def firstChernClass (E : HolomorphicUnitExtension s d) : IntegralCohomology s 2 :=
  (analyticSheafCohomologyEquivExt s (constantIntegerSheaf s) 2).symm
    (holomorphicFirstChernClass s d E.cohomologyClass)

variable (s d)

/-- Every degree-one class of the holomorphic-unit sheaf is represented by an extension. -/
theorem exists_cohomologyClass
    (β : Abelian.Ext.{1} (constantIntegerSheaf s) (holomorphicUnitSheaf s d) 1) :
    ∃ E : HolomorphicUnitExtension s d, E.cohomologyClass = β := by
  obtain ⟨M, i, p, w, h, hβ⟩ := Abelian.Ext.exists_shortExact β
  exact ⟨⟨M, i, p, w, h⟩, hβ⟩

variable {s d}

/-- The constant integer section `1` on the whole analytic space. -/
def integerOneSection : (constantIntegerSheaf s).obj.obj
    (op (⊤ : Opens (TopCat.of (ComplexPoint X s)))) :=
  (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s)))
    ((Functor.const (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ).obj (AddCommGrpCat.of ℤ))).app
      (op ⊤) (1 : ℤ)

/-- Chosen local lifts of the integer section `1` through the extension. -/
def localLifts (E : HolomorphicUnitExtension s d) :
    TopCat.Sheaf.ExtensionLocalLifts E.shortComplex integerOneSection :=
  TopCat.Sheaf.ExtensionLocalLifts.choose E.shortComplex E.shortExact integerOneSection

end HolomorphicUnitExtension

/-- Integral Hodge classes are first Chern classes of extensions by holomorphic units. -/
theorem exists_holomorphicUnitExtension_of_integral_hodgeClass [IsIntegral X] [Smooth s]
    (α : IntegralCohomology s 2)
    (hα : integralToRationalCohomology s 2 α ∈ hodgeClasses ℚ s 1) :
    ∃ E : HolomorphicUnitExtension s (dim X), E.firstChernClass = α := by
  obtain ⟨β, hβ⟩ := exists_holomorphicFirstChernClass_of_integral_hodgeClass s α hα
  obtain ⟨E, hE⟩ := HolomorphicUnitExtension.exists_cohomologyClass s (dim X) β
  refine ⟨E, ?_⟩
  apply (analyticSheafCohomologyEquivExt s (constantIntegerSheaf s) 2).injective
  rw [HolomorphicUnitExtension.firstChernClass, Equiv.apply_symm_apply, hE, hβ]

end AlgebraicGeometry.ComplexPoint
