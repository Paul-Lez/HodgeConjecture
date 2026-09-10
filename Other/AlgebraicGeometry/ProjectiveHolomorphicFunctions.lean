/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveAnalytificationConnected
public import Other.AlgebraicGeometry.ProjectiveAnalytification
public import Other.AlgebraicGeometry.HolomorphicLineBundleModule
public import Other.AlgebraicGeometry.RegularFunctionsHolomorphic
public import Mathlib.Geometry.Manifold.Complex

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Holomorphic functions on projective complex points

The maximum-modulus theorem for compact complex manifolds shows that every global holomorphic
function on a projective complex scheme is locally constant.  In particular its range is finite.
Once analytic connectedness of an integral projective variety is available, this specializes to
the degree-zero `H⁰` comparison: every global holomorphic function is constant.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  [IsProjective X.hom]

/-- The global regular section supplied by a scalar from the base field. -/
def constantRegularSection (c : ℂ) : Γ(X.left, ⊤) :=
  X.hom.appTop ((Scheme.ΓSpecIso ↧ℂ).inv c)

/-- A scalar from the base field evaluates to the corresponding constant function. -/
lemma evaluate_constantRegularSection (c : ℂ) (z : ComplexPoint X) :
    Point.evaluate ⊤ (constantRegularSection X c) z = c := by
  rw [evaluate_top_eq_appTop]
  change (Scheme.ΓSpecIso ↧ℂ).hom
    (z.left.appTop (X.hom.appTop ((Scheme.ΓSpecIso ↧ℂ).inv c))) = c
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop_assoc]
  rw [z.w]
  simp

/-- A global holomorphic function on projective complex points is locally constant. -/
theorem globalHolomorphic_isLocallyConstant
    (f : C^ω⟮𝓘(ℂ, Fin d → ℂ), ComplexPoint X; ℂ⟯) : IsLocallyConstant f :=
  (f.contMDiff.mdifferentiable (by simp)).isLocallyConstant

/-- A global holomorphic function on projective complex points takes only finitely many values. -/
theorem globalHolomorphic_range_finite
    (f : C^ω⟮𝓘(ℂ, Fin d → ℂ), ComplexPoint X; ℂ⟯) :
    (Set.range f).Finite :=
  (globalHolomorphic_isLocallyConstant X d f).range_finite

/-- On a preconnected projective analytification, every global holomorphic function is constant. -/
theorem globalHolomorphic_eq_const [PreconnectedSpace (ComplexPoint X)]
    (f : C^ω⟮𝓘(ℂ, Fin d → ℂ), ComplexPoint X; ℂ⟯) :
    ∃ c : ℂ, (f : ComplexPoint X → ℂ) = Function.const _ c :=
  (f.contMDiff.mdifferentiable (by simp)).exists_eq_const_of_compactSpace

/-- On a preconnected projective analytification, evaluation of algebraic global functions is
surjective onto analytic global functions. This is the degree-zero surjectivity half of `H⁰`
comparison; no algebraic injectivity assertion is needed to algebraize a degree-zero matrix. -/
theorem regularFunctionsToHolomorphic_top_surjective [PreconnectedSpace (ComplexPoint X)] :
    Function.Surjective (regularFunctionsToHolomorphic X d (⊤ : X.left.Opens)) := by
  intro f
  have htop : analyticOpen X (⊤ : X.left.Opens) = ⊤ := by
    exact TopologicalSpace.Opens.map_top (underlyingContinuousMap X)
  have hcompact : IsCompact (analyticOpen X (⊤ : X.left.Opens) : Set (ComplexPoint X)) := by
    rw [htop]
    exact isCompact_univ
  letI : CompactSpace (analyticOpen X (⊤ : X.left.Opens)) :=
    isCompact_iff_compactSpace.mp hcompact
  have hpreconnected :
      IsPreconnected (analyticOpen X (⊤ : X.left.Opens) : Set (ComplexPoint X)) := by
    rw [htop]
    exact isPreconnected_univ
  letI : PreconnectedSpace (analyticOpen X (⊤ : X.left.Opens)) :=
    Subtype.preconnectedSpace hpreconnected
  obtain ⟨c, hc⟩ :=
    (f.contMDiff.mdifferentiable (by simp)).exists_eq_const_of_compactSpace
  refine ⟨constantRegularSection X c, ?_⟩
  apply ContMDiffMap.ext
  intro z
  change Point.evaluate ⊤ (constantRegularSection X c) z.1 = f z
  rw [evaluate_constantRegularSection X c z.1]
  exact congrFun hc z |>.symm

end AlgebraicGeometry.ComplexPoint
