/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.IntegralCohomology
public import Other.AlgebraicGeometry.HolomorphicFirstChernClass
public import Other.AlgebraicTopology.SheafExtensionLocalLifts
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

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

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
  projection : middle ⟶ 𝓒(↧(ComplexPoint X); ℤ)
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
    Abelian.Ext.{0} (𝓒(↧(ComplexPoint X); ℤ)) (holomorphicUnitSheaf X d) 1 :=
  E.shortExact.extClass

/-- The integral first Chern class of an extension. -/
def firstChernClass (E : HolomorphicUnitExtension X d) : H^2(X; ℤ) :=
  holomorphicFirstChernClass X d
    ((sheafCohomologyEquivExt X (holomorphicUnitSheaf X d) 1).symm E.cohomologyClass)

/-- The constant integer section `1` on the whole analytic space. -/
def integerOneSection : (𝓒(↧(ComplexPoint X); ℤ)).obj.obj
    (op (⊤ : Opens (TopCat.of (ComplexPoint X)))) :=
  (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    ((Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).obj (AddCommGrpCat.of ℤ))).app
      (op ⊤) (1 : ℤ)

/-- Chosen local lifts of the integer section `1` through the extension. -/
def localLifts (E : HolomorphicUnitExtension X d) :
    TopCat.Sheaf.ExtensionLocalLifts E.shortComplex integerOneSection :=
  TopCat.Sheaf.ExtensionLocalLifts.choose E.shortComplex E.shortExact integerOneSection

end HolomorphicUnitExtension


end AlgebraicGeometry.ComplexPoint
