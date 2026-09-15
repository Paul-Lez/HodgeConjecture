/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Locus
public import HodgeConjecture.Mathlib.AlgebraicGeometry.ReducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# A finite smooth decomposition of reduced closed subschemes

Each step takes the actual reduced closed subscheme on a closed subset, removes its smooth
locus, and continues on the closed remainder. Noetherian induction makes this construction
finite. The pieces are actual smooth locally closed subschemes, not supplied stratification
data. This is an algebraic prerequisite for dimension induction; it does not assert a
Whitney or frontier condition, triangulation, analytic homology vanishing, or extension of an
orientation across singularities.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

variable {K : Type u} [Field K]
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

/-- The structure morphism of the actual reduced closed subscheme. -/
def reducedClosedStructureMap (S : Closeds X) :
    X.reducedClosedSubscheme S ⟶ Spec (.of K) :=
  X.reducedClosedSubschemeι S ≫ f

instance reducedClosedStructureMap_locallyOfFiniteType (S : Closeds X) :
    LocallyOfFiniteType (reducedClosedStructureMap f S) := by
  dsimp [reducedClosedStructureMap]
  infer_instance

/-- The singular remainder, regarded as a closed subset of the original scheme. -/
def reducedClosedSingularRemainder (S : Closeds X) : Closeds X :=
  ⟨X.reducedClosedSubschemeι S ''
    ((reducedClosedStructureMap f S).smoothLocus : Set (X.reducedClosedSubscheme S))ᶜ,
    (X.reducedClosedSubschemeι S).isClosedEmbedding.isClosedMap _
      (reducedClosedStructureMap f S).smoothLocus.isOpen.isClosed_compl⟩

local instance reducedSmoothStratificationWellFoundedRelation [NoetherianSpace X] :
    WellFoundedRelation (Closeds X) :=
  ⟨(· < ·), wellFounded_lt⟩

end AlgebraicGeometry
