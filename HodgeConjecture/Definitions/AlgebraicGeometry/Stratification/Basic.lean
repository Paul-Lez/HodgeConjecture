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

For a scheme over a field and a closed subset, take the reduced closed subscheme,
remove its smooth locus, and repeat on the closed remainder. Under the hypotheses used
below, Noetherian induction makes the resulting list finite. The differences between
successive closed subsets, with their induced reduced scheme structures, are smooth
locally closed subschemes.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- Let `X` be a scheme and `S` a closed subset of its underlying space. This is the reduced closed
subscheme defined by the vanishing ideal sheaf of `S`; on each affine open, its ring is the
quotient by the radical ideal of functions vanishing on `S`. -/
def reducedClosedSubscheme (S : Closeds X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal S).subscheme

/-- Let `X` be a scheme and `S ⊆ X` closed. This is the closed immersion into `X` of the reduced
subscheme defined by the vanishing ideal of `S`. On underlying spaces it is the inclusion of
`S`. -/
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

/-- Let `f : X → Spec K` be a scheme locally of finite type over a field `K` and let `S ⊆ X` be
closed. This is the structure morphism of the reduced subscheme on `S`, obtained by composing
its inclusion into `X` with `f`. -/
def reducedClosedStructureMap (S : Closeds X) :
    reducedClosedSubscheme S ⟶ Spec (.of K) :=
  reducedClosedSubschemeι S ≫ f

instance reducedClosedStructureMap_locallyOfFiniteType (S : Closeds X) :
    LocallyOfFiniteType (reducedClosedStructureMap f S) := by
  dsimp [reducedClosedStructureMap]
  infer_instance

/-- Let `f : X → Spec K` be a scheme locally of finite type over a field `K`. This is the closed
subset of points where `f` is not smooth, the complement of its open smooth locus. -/
def singularLocusClosed : Closeds X := f.smoothLocus.compl

/-- Let `f : X → Spec K` be locally of finite type over a field and `S ⊆ X` closed. Form the reduced
subscheme on `S` and remove its smooth locus over `K`. This is the image of the remaining closed
subset in the original space `X`. -/
def reducedClosedSingularRemainder (S : Closeds X) : Closeds X :=
  ⟨reducedClosedSubschemeι S ''
    ((reducedClosedStructureMap f S).smoothLocus : Set (reducedClosedSubscheme S))ᶜ,
    (reducedClosedSubschemeι S).isClosedEmbedding.isClosedMap _
      (reducedClosedStructureMap f S).smoothLocus.isOpen.isClosed_compl⟩

/-- Let `f : X → Spec K` be locally of finite type over a field and `S ⊆ X` closed. Define `S₀ = S`;
to obtain `S_{k+1}`, give `S_k` its reduced scheme structure and remove its smooth locus over
`K`. This is the resulting decreasing sequence of closed subsets of `X`, indexed by natural
numbers. -/
def reducedSmoothClosedFiltration (S : Closeds X) : ℕ → Closeds X
  | 0 => S
  | k + 1 => reducedClosedSingularRemainder f (reducedSmoothClosedFiltration S k)

local instance reducedSmoothStratificationWellFoundedRelation [NoetherianSpace X] :
    WellFoundedRelation (Closeds X) :=
  ⟨(· < ·), wellFounded_lt⟩

end AlgebraicGeometry
