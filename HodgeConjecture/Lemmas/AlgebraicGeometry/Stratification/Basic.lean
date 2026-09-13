/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Stratification.Basic
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Locus
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# A finite smooth decomposition of reduced closed subschemes

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Stratification.Basic`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section
open CategoryTheory Topology TopologicalSpace
namespace AlgebraicGeometry
universe u
variable {X : Scheme.{u}}

@[simp] lemma range_reducedClosedSubschemeι (S : Closeds X) :
    Set.range (reducedClosedSubschemeι S) = (S : Set X) :=
  Scheme.IdealSheafData.range_subschemeι _

end AlgebraicGeometry
end

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

variable {K : Type u} [Field K]
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

lemma reducedClosedSingularRemainder_le (S : Closeds X) :
    reducedClosedSingularRemainder f S ≤ S := by
  rintro _ ⟨x, _, rfl⟩
  exact (range_reducedClosedSubschemeι S).le ⟨x, rfl⟩

lemma reducedClosedSingularRemainder_lt [PerfectField K] (S : Closeds X) (hS : S ≠ ⊥) :
    reducedClosedSingularRemainder f S < S := by
  refine lt_of_le_of_ne (reducedClosedSingularRemainder_le f S) ?_
  have hne : Nonempty (reducedClosedSubscheme S) := by
    obtain ⟨x, hx⟩ := Closeds.coe_nonempty.mpr hS
    obtain ⟨y, _⟩ := (range_reducedClosedSubschemeι S).ge hx
    exact ⟨y⟩
  obtain ⟨x, hx⟩ :=
    (reducedClosedStructureMap f S).dense_smoothLocus_of_perfectField.nonempty
  intro h
  have hmem : reducedClosedSubschemeι S x ∈ reducedClosedSingularRemainder f S := by
    rw [h]
    exact (range_reducedClosedSubschemeι S).le ⟨x, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hmem
  exact hy ((reducedClosedSubschemeι S).isClosedEmbedding.injective hxy ▸ hx)

/-- The smooth piece removed from a closed subset at one step. -/
def reducedClosedSmoothPiece (S : Closeds X) : Scheme :=
  (reducedClosedStructureMap f S).smoothLocus

/-- This piece is locally closed in the original ambient scheme. -/
def reducedClosedSmoothPieceι (S : Closeds X) : reducedClosedSmoothPiece f S ⟶ X :=
  (reducedClosedStructureMap f S).smoothLocus.ι ≫ reducedClosedSubschemeι S

set_option backward.isDefEq.respectTransparency false in
instance reducedClosedSmoothPieceι_isImmersion (S : Closeds X) :
    IsImmersion (reducedClosedSmoothPieceι f S) := by
  change IsImmersion
    ((reducedClosedStructureMap f S).smoothLocus.ι ≫ reducedClosedSubschemeι S)
  infer_instance

instance reducedClosedSmoothPiece_smooth (S : Closeds X) :
    Smooth (reducedClosedSmoothPieceι f S ≫ f) := by
  change Smooth ((reducedClosedStructureMap f S).smoothLocus.ι ≫
    reducedClosedSubschemeι S ≫ f)
  exact (reducedClosedStructureMap f S).smooth_restrict_smoothLocus

attribute [local instance] reducedSmoothStratificationWellFoundedRelation

/-- The finite, explicitly recursive sequence of nonempty closed remainders. The actual
smooth strata are `reducedClosedSmoothPiece f S` for the members of this list. -/
def reducedSmoothStratification [PerfectField K] [NoetherianSpace X]
    (S : Closeds X) : List (Closeds X) := by
  classical
  exact if hS : S = ⊥ then []
    else S :: reducedSmoothStratification (reducedClosedSingularRemainder f S)
termination_by S
decreasing_by exact reducedClosedSingularRemainder_lt f S hS

variable [PerfectField K] [NoetherianSpace X]

end AlgebraicGeometry

end

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

variable {K : Type u} [Field K]
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

lemma reducedClosedSmoothPiece_range (S : Closeds X) :
    Set.range (reducedClosedSmoothPieceι f S) =
      (S : Set X) \ (reducedClosedSingularRemainder f S : Set X) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(range_reducedClosedSubschemeι S).le ⟨y.1, rfl⟩, ?_⟩
    rintro ⟨z, hz, he⟩
    exact hz ((reducedClosedSubschemeι S).isClosedEmbedding.injective he ▸ y.2)
  · rintro ⟨hx, hnot⟩
    obtain ⟨y, rfl⟩ := (range_reducedClosedSubschemeι S).ge hx
    have hy : y ∈ (reducedClosedStructureMap f S).smoothLocus := by
      by_contra hn
      exact hnot ⟨y, hn, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

attribute [local instance] reducedSmoothStratificationWellFoundedRelation

variable [PerfectField K] [NoetherianSpace X]

end AlgebraicGeometry
