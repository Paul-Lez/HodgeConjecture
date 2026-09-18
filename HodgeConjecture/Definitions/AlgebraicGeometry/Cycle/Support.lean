/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Locus
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Geometric support of a closed subvariety

A closed embedding `i : Y ⟶ X` over `Spec ℂ` has a support: the complex points of `X` in the
image of `i`. When the source is irreducible the image is the closure of one ambient point, the
ambient generic point of `i`.

An algebraic cycle in Mathlib is indexed by the generic points of its irreducible components.
This file also constructs the reduced integral closed subscheme attached to such a point, and
the closed embedding it carries.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

/-- The reduced closed subscheme whose underlying space is the closure of `x`. -/
def cycleComponent (X : Scheme) (x : X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩).subscheme

/-- The canonical closed immersion of the reduced closure of `x`. -/
def cycleComponentι (X : Scheme) (x : X) : cycleComponent X x ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩).subschemeι

instance (X : Scheme) (x : X) : IsClosedImmersion (cycleComponentι X x) := by
  change IsClosedImmersion
    ((Scheme.IdealSheafData.vanishingIdeal
      (X := X) ⟨closure {x}, isClosed_closure⟩).subschemeι)
  infer_instance

instance (X : Scheme) (x : X) : IsReduced (cycleComponent X x) := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩
  change IsReduced I.subscheme
  rw [IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover]
  intro U
  let U' : X.affineOpens := U
  change IsReduced (Spec ↧(Γ(X, U') ⧸ I.ideal U'))
  rw [affine_isReduced_iff, ← Ideal.isRadical_iff_quotient_reduced]
  change (PrimeSpectrum.vanishingIdeal (U'.2.fromSpec ⁻¹' closure {x})).IsRadical
  exact PrimeSpectrum.isRadical_vanishingIdeal _

instance (X : Scheme) (x : X) : IrreducibleSpace (cycleComponent X x) :=
  Subtype.irreducibleSpace isIrreducible_singleton.closure

instance (X : Scheme) (x : X) : IsIntegral (cycleComponent X x) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The reduced closure of `x`, over `Spec ℂ`. -/
def cycleComponentOver (X : Over (Spec ↧ℂ)) (x : X.left) : Over (Spec ↧ℂ) :=
  Over.mk (cycleComponentι X.left x ≫ X.hom)

/-- The closed embedding of the reduced closure of `x`, over `Spec ℂ`. -/
def cycleComponentOverι (X : Over (Spec ↧ℂ)) (x : X.left) : cycleComponentOver X x ⟶ X :=
  Over.homMk (cycleComponentι X.left x) rfl

instance (X : Over (Spec ↧ℂ)) (x : X.left) : IsIntegral (cycleComponentOver X x).left :=
  inferInstanceAs (IsIntegral (cycleComponent X.left x))

instance (X : Over (Spec ↧ℂ)) (x : X.left) :
    IsClosedImmersion (cycleComponentOverι X x).left :=
  inferInstanceAs (IsClosedImmersion (cycleComponentι X.left x))

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)

/-- The complex points of `X` in the image of a closed embedding. -/
def closedEmbeddingSupport : Set (ComplexPoint X) :=
  Point.underlying ⁻¹' Set.range i.left

/-- The ambient point of a closed embedding whose source is irreducible. -/
def closedEmbeddingGenericPoint [IrreducibleSpace Y.left] : X.left :=
  i.left (genericPoint Y.left)

/-- A closed embedding of a projective variety is projective over `ℂ`. -/
theorem closedEmbedding_isProjective [IsProjective X.hom] [IsClosedImmersion i.left] :
    IsProjective Y.hom := by
  rcases ‹IsProjective X.hom›.nonempty_presentation with ⟨P⟩
  refine ⟨⟨
    { ambientDimension := P.ambientDimension
      immersion := i.left ≫ P.immersion
      isClosedImmersion := by
        let := P.isClosedImmersion
        infer_instance
      immersion_toBase := ?_ }
  ⟩⟩
  rw [Category.assoc, P.immersion_toBase]
  exact Over.w i

end AlgebraicGeometry
