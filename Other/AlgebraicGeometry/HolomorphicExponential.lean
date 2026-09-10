/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexAnalyticSheaf
public import Other.Geometry.Manifold.HolomorphicLogarithm
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.MonCat.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.Abelian

/-!
# The holomorphic exponential morphism

We construct the sheaf of invertible holomorphic functions, written additively, and the
normalized exponential morphism `f ↦ exp(2πif)`. These are the actual function sheaves on the
analytic complex-point space, for use in the exponential-sequence proof of Lefschetz `(1, 1)`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

local instance holomorphicExponentialTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

/-- The additive sheaf underlying the holomorphic-function sheaf. -/
def holomorphicAdditiveSheaf :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
  (sheafCompose (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj
      (holomorphicFunctionSheaf X d)

/-- The unit group of a commutative ring, written as an additive group. -/
def holomorphicUnitsFunctor : CommRingCat ⥤ AddCommGrpCat :=
  forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
    commGroupAddCommGroupEquivalence.functor

instance : PreservesLimits holomorphicUnitsFunctor := by
  have : ReflectsLimits (forget CommMonCat) :=
    ⟨fun {_ _} ↦ ⟨fun {_} ↦ inferInstance⟩⟩
  have : PreservesLimits ((forget₂ CommRingCat CommMonCat) ⋙ forget CommMonCat) :=
    inferInstanceAs (PreservesLimits (forget CommRingCat))
  have : PreservesLimits (forget₂ CommRingCat CommMonCat) :=
    preservesLimits_of_reflects_of_preserves _ (forget CommMonCat)
  unfold holomorphicUnitsFunctor
  infer_instance

/-- The sheaf of invertible holomorphic functions, with its group law written additively. -/
def holomorphicUnitSheaf :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
  (sheafCompose (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    holomorphicUnitsFunctor).obj (holomorphicFunctionSheaf X d)

/-- The normalized exponential morphism of sheaves, sending `f` to `exp(2πif)`. -/
def holomorphicExponential : holomorphicAdditiveSheaf X d ⟶ holomorphicUnitSheaf X d :=
  ⟨{ app U := AddCommGrpCat.ofHom ContMDiffMap.holomorphicExponential
     naturality {U V} i := by
       apply AddCommGrpCat.hom_ext
       apply AddMonoidHom.ext
       intro f
       apply Units.ext
       apply ContMDiffMap.ext
       intro x
       rfl }⟩

/-- Every invertible holomorphic section locally lifts through the normalized exponential. -/
theorem holomorphicExponential_isLocallySurjective :
    TopCat.Presheaf.IsLocallySurjective (holomorphicExponential X d).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  change Additive (C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯)ˣ at t
  have ht : (t.toMul : C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯) ⟨x, hx⟩ ≠ 0 :=
    (t.toMul.isUnit.map (ContMDiffMap.evalRingHom (I := 𝓘(ℂ, Fin d → ℂ))
      (n := ω) (⟨x, hx⟩ : U))).ne_zero
  obtain ⟨V, hVU, hxV, g, hg⟩ :=
    (t.toMul : C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯).exists_local_holomorphicExponential
      ⟨x, hx⟩ ht
  refine ⟨V, hVU, ⟨g, ?_⟩, hxV⟩
  apply Units.ext
  apply ContMDiffMap.ext
  exact hg

/-- The holomorphic exponential is an epimorphism of sheaves of additive groups. -/
instance holomorphicExponential_epi : Epi (holomorphicExponential X d) :=
  (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp (holomorphicExponential_isLocallySurjective X d)

end AlgebraicGeometry.ComplexPoint
