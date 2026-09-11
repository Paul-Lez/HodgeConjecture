/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingStandardTriangle
public import Other.AlgebraicTopology.ComplexOrientation
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Naturality of the connecting map of a pair, and the boundary of the complex local class

The repository has the connecting map `AlgebraicTopology.Singular.relativeSingularBoundary` of a
topological pair and the computation
`relativeSingularBoundary_standardLocalClass : ∂ (standardLocalClass (n+1)) =
standardPuncturedBoundaryClass n`, but no naturality statement.  This file supplies it, from
Mathlib's `HomologicalComplex.HomologySequence.δ_naturality`, and uses it to transport the
computation to the *complex* local class `standardComplexLocalClass 1`.

The two results are

* `AlgebraicTopology.Singular.relativeSingularBoundary_naturality`, and
* `AlgebraicTopology.Singular.relativeSingularBoundary_standardComplexLocalClass`, which says
  that `∂ (standardComplexLocalClass 1)` is the image of the explicit oriented boundary
  `standardPuncturedBoundaryClass 1` of the standard affine `2`-simplex under the real-to-complex
  coordinate homeomorphism.

Together with `ChernWinding.windingPeriod_standardPuncturedBoundaryClass` (the sign `+1`) and
`ChernWinding.windingPeriod_map` (naturality of the winding period) this computes the winding
number of any nowhere vanishing function along the boundary of the complex local class: see
`Other/AlgebraicGeometry/ChernWindingNormalChart.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Simplicial

namespace AlgebraicTopology.Singular

/-! ### Naturality of the connecting map -/

/-- A map of topological pairs induces a morphism of the short exact sequences of chains. -/
def relativeSingularChainShortComplexMap {P Q : TopPair} (f : P ⟶ Q) :
    relativeSingularChainShortComplex P ⟶ relativeSingularChainShortComplex Q where
  τ₁ := ((chainPairFunctor ℚ).map f).left
  τ₂ := ((chainPairFunctor ℚ).map f).right
  τ₃ := (relativeChainFunctor ℚ).map f
  comm₁₂ := ((chainPairFunctor ℚ).map f).w
  comm₂₃ := (Limits.coker.π (ChainCategory ℚ)).naturality ((chainPairFunctor ℚ).map f)

@[simp] theorem relativeSingularChainShortComplexMap_τ₁ {P Q : TopPair} (f : P ⟶ Q) :
    (relativeSingularChainShortComplexMap f).τ₁ = ((chainPairFunctor ℚ).map f).left := rfl

@[simp] theorem relativeSingularChainShortComplexMap_τ₃ {P Q : TopPair} (f : P ⟶ Q) :
    (relativeSingularChainShortComplexMap f).τ₃ = (relativeChainFunctor ℚ).map f := rfl

/-- **Naturality of the connecting map of a pair.** -/
theorem relativeSingularBoundary_naturality {P Q : TopPair} (f : P ⟶ Q) (n : ℕ) :
    relativeSingularBoundary P n ≫
        HomologicalComplex.homologyMap ((chainPairFunctor ℚ).map f).left n =
      HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map f) (n + 1) ≫
        relativeSingularBoundary Q n :=
  HomologicalComplex.HomologySequence.δ_naturality
    (relativeSingularChainShortComplexMap f)
    (relativeSingularChainShortComplex_shortExact P)
    (relativeSingularChainShortComplex_shortExact Q) (n + 1) n
    (ComplexShape.down_mk (n + 1) n (by lia))

/-- The elementwise form of naturality. -/
theorem relativeSingularBoundary_relativeHomologyMap {P Q : TopPair} (f : P ⟶ Q) (n : ℕ)
    (z : RelativeHomology ℚ P (n + 1)) :
    (relativeSingularBoundary Q n).hom (relativeHomologyMap ℚ (n + 1) f z) =
      (HomologicalComplex.homologyMap ((chainPairFunctor ℚ).map f).left n).hom
        ((relativeSingularBoundary P n).hom z) :=
  (ConcreteCategory.congr_hom (relativeSingularBoundary_naturality f n) z).symm

/-! ### The boundary of the standard complex local class -/

theorem standardComplexLocalClass_one :
    standardComplexLocalClass 1 =
      relativeHomologyMap ℚ 2 (standardRealToComplexPair 1) (standardLocalClass 2) := rfl

theorem homologyMap_eq_chainPairFunctor_left {P Q : TopPair} (f : P ⟶ Q) (n : ℕ)
    (z : Homology ℚ P.snd n) :
    homologyMap ℚ n f.left z =
      (HomologicalComplex.homologyMap ((chainPairFunctor ℚ).map f).left n).hom z := rfl

/-- **The boundary of the standard complex local class** is the image of the explicit oriented
boundary of the standard affine `2`-simplex under the real-to-complex coordinate map. -/
theorem relativeSingularBoundary_standardComplexLocalClass :
    (relativeSingularBoundary (standardComplexPuncturedPair 1) 1).hom
        (standardComplexLocalClass 1) =
      homologyMap ℚ 1 (standardRealToComplexPair 1).left
        (standardPuncturedBoundaryClass 1) := by
  rw [standardComplexLocalClass_one,
    relativeSingularBoundary_relativeHomologyMap (standardRealToComplexPair 1) 1
      (standardLocalClass 2),
    relativeSingularBoundary_standardLocalClass 1]
  rfl

end AlgebraicTopology.Singular

namespace ChernWinding

open AlgebraicTopology.Singular

theorem windingPeriod_congr {Y : TopCat.{0}} {g g' : C(Y, ℂ)} (hg : ∀ y, g y ≠ 0)
    (hg' : ∀ y, g' y ≠ 0) (h : g = g') (z : Homology ℚ Y 1) :
    windingPeriod g hg z = windingPeriod g' hg' z := by
  subst h; rfl

/-- **The winding number along the boundary of a transported complex local class.**

If `Ψ` maps the standard complex punctured pair into a pair `Q`, and the nowhere vanishing
function `g` on `Q`'s subspace pulls back along `Ψ` (read through the real coordinates) to the
complex coordinate, then the winding number of `g` along the boundary of the transported complex
local class is `1`.  This is the whole of the Lelong–Poincaré normalisation, with the sign. -/
theorem windingPeriod_relativeSingularBoundary_relativeHomologyMap
    {Q : TopPair} (Ψ : standardComplexPuncturedPair 1 ⟶ Q)
    (g : C(Q.snd, ℂ)) (hg : ∀ y, g y ≠ 0)
    (hcoord : ∀ v : (standardPuncturedPair 2).snd,
        g (Ψ.left ((standardRealToComplexPair 1).left v)) = complexCoordinate v) :
    windingPeriod g hg
        ((relativeSingularBoundary Q 1).hom
          (relativeHomologyMap ℚ 2 Ψ (standardComplexLocalClass 1))) = 1 := by
  rw [relativeSingularBoundary_relativeHomologyMap Ψ 1 (standardComplexLocalClass 1),
    ← homologyMap_eq_chainPairFunctor_left Ψ 1,
    relativeSingularBoundary_standardComplexLocalClass]
  have hcomp : homologyMap ℚ 1 Ψ.left
      (homologyMap ℚ 1 (standardRealToComplexPair 1).left (standardPuncturedBoundaryClass 1)) =
      homologyMap ℚ 1 ((standardRealToComplexPair 1).left ≫ Ψ.left)
        (standardPuncturedBoundaryClass 1) := by
    change ((homologyMap ℚ 1 Ψ.left).comp (homologyMap ℚ 1 (standardRealToComplexPair 1).left))
      (standardPuncturedBoundaryClass 1) = _
    rw [← homologyMap_comp]
  rw [hcomp, ← windingPeriod_map g ((standardRealToComplexPair 1).left ≫ Ψ.left) hg
    (fun v => by
      rw [show (g.comp (topMap ((standardRealToComplexPair 1).left ≫ Ψ.left))) v =
        g (Ψ.left ((standardRealToComplexPair 1).left v)) from rfl, hcoord v]
      exact complexCoordinate_ne_zero v)]
  refine (windingPeriod_congr _ complexCoordinate_ne_zero ?_ _).trans
    windingPeriod_standardPuncturedBoundaryClass
  exact ContinuousMap.ext hcoord

end ChernWinding
