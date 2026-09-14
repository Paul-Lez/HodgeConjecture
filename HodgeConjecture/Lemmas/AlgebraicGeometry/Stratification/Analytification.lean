/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Stratification.Analytification

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Complex points of the constructed smooth decomposition

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Stratification.Analytification`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) {Y : Over (Spec ↧ℂ)}

variable [LocallyOfFiniteType X.hom] [NoetherianSpace X.left]

/-- The inclusion of a reduced smooth stratum, bundled over the complex base. -/
def reducedClosedSmoothPieceMap (T : Closeds X.left) :
    Over.mk (reducedClosedSmoothPieceι X.hom T ≫ X.hom) ⟶ X :=
  Over.homMk (reducedClosedSmoothPieceι X.hom T) rfl

instance reducedClosedSmoothPieceMap_isImmersion (T : Closeds X.left) :
    IsImmersion (reducedClosedSmoothPieceMap X T).left := by
  change IsImmersion (reducedClosedSmoothPieceι X.hom T)
  infer_instance

end AlgebraicGeometry.ComplexPoint

end

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) {Y : Over (Spec ↧ℂ)}

/-- Forgetting a complex point to its underlying Zariski point is continuous for the actual
analytic topology. -/
theorem continuous_underlying_to_zariski :
    Continuous (Point.underlying : Point ℂ X → X.left) := by
  rw [continuous_def]
  exact fun S hS => Point.isOpen_overOpen ⟨S, hS⟩

/-- The complex points of a locally closed subscheme map onto exactly the complex points
whose underlying scheme point belongs to its range. -/
theorem range_map_of_isImmersion (i : Y ⟶ X)
    [IsImmersion i.left] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    Set.range (Point.map i) =
      (Point.underlying : Point ℂ X → X.left) ⁻¹' Set.range i.left := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.underlying, rfl⟩
  · rintro ⟨y, hy⟩
    have hyclosed : IsClosed ({y} : Set Y.left) := by
      have h := ((pointEquivClosedPoint X.hom) ⟨z.left, z.w⟩).2.preimage i.left.continuous
      change IsClosed (i.left ⁻¹' ({z.underlying} : Set X.left)) at h
      have he : i.left ⁻¹' ({z.underlying} : Set X.left) = {y} := by
        rw [← hy]
        ext a
        exact i.left.isEmbedding.injective.eq_iff
      rwa [he] at h
    let p := (pointEquivClosedPoint Y.hom).symm ⟨y, hyclosed⟩
    let w : Point ℂ Y := Over.homMk p.1 p.2
    refine ⟨w, ?_⟩
    apply Over.OverMorphism.ext
    have heq :
        (⟨(Point.map i w).left, (Point.map i w).w⟩ :
          {q : Spec ↧ℂ ⟶ X.left // q ≫ X.hom = 𝟙 _}) = ⟨z.left, z.w⟩ := by
      apply (pointEquivClosedPoint X.hom).injective
      apply Subtype.ext
      change i.left w.underlying = z.underlying
      have hw : w.underlying = y :=
        congrArg Subtype.val
          ((pointEquivClosedPoint Y.hom).apply_symm_apply ⟨y, hyclosed⟩)
      rw [hw]
      exact hy
    exact congrArg Subtype.val heq

end AlgebraicGeometry.ComplexPoint
