/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Locus
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# A finite smooth decomposition of reduced closed subschemes

Each step takes the reduced closed subscheme on a closed subset, removes its smooth
locus, and continues on the closed remainder. Noetherian induction makes this construction
finite. The pieces are smooth locally closed subschemes. The decomposition is the algebraic
input for dimension induction; Whitney and frontier conditions, triangulation, analytic homology
vanishing, and extension of an orientation across singularities are all outside its scope.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- The reduced closed subscheme on a closed subset. -/
def reducedClosedSubscheme (S : Closeds X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal S).subscheme

/-- The canonical inclusion of the reduced closed subscheme. -/
def reducedClosedSubschemeι (S : Closeds X) : reducedClosedSubscheme S ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal S).subschemeι

instance reducedClosedSubschemeι_isClosedImmersion (S : Closeds X) :
    IsClosedImmersion (reducedClosedSubschemeι S) := by
  change IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal S).subschemeι
  infer_instance

instance reducedClosedSubscheme_isReduced (S : Closeds X) :
    IsReduced (reducedClosedSubscheme S) := by
  let I := Scheme.IdealSheafData.vanishingIdeal S
  change IsReduced I.subscheme
  rw [IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover]
  intro U
  let U' : X.affineOpens := U
  change IsReduced (Spec (.of (Γ(X, U') ⧸ I.ideal U')))
  rw [affine_isReduced_iff, ← Ideal.isRadical_iff_quotient_reduced]
  exact PrimeSpectrum.isRadical_vanishingIdeal _

variable {K : Type u} [Field K]
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

/-- The structure morphism of the reduced closed subscheme. -/
def reducedClosedStructureMap (S : Closeds X) :
    reducedClosedSubscheme S ⟶ Spec (.of K) :=
  reducedClosedSubschemeι S ≫ f

instance reducedClosedStructureMap_locallyOfFiniteType (S : Closeds X) :
    LocallyOfFiniteType (reducedClosedStructureMap f S) := by
  dsimp [reducedClosedStructureMap]
  infer_instance

/-- The singular remainder, regarded as a closed subset of the original scheme. -/
def reducedClosedSingularRemainder (S : Closeds X) : Closeds X :=
  ⟨reducedClosedSubschemeι S ''
    ((reducedClosedStructureMap f S).smoothLocus : Set (reducedClosedSubscheme S))ᶜ,
    (reducedClosedSubschemeι S).isClosedEmbedding.isClosedMap _
      (reducedClosedStructureMap f S).smoothLocus.isOpen.isClosed_compl⟩

local instance reducedSmoothStratificationWellFoundedRelation [NoetherianSpace X] :
    WellFoundedRelation (Closeds X) :=
  ⟨(· < ·), wellFounded_lt⟩

variable [PerfectField K] [NoetherianSpace X]

end AlgebraicGeometry
