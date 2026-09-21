/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Topology.Dimension.ClosedSubset
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.Basic
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalGeometry
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.Dimension
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# The singular locus has smaller algebraic dimension

Over a perfect field the complement of the smooth locus of a reduced irreducible scheme is
a proper closed subset. This file proves the strict Krull-dimension bound of that reduced
closed subscheme, including the `d - p` bound for cycle components. The bounds are on
algebraic dimension throughout.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

/-- The singular locus equipped with its reduced closed-subscheme structure. -/
def reducedSingularLocus : Scheme := reducedClosedSubscheme (singularLocusClosed f)

/-- Its canonical closed immersion in the original scheme. -/
def reducedSingularLocusι : reducedSingularLocus f ⟶ X :=
  reducedClosedSubschemeι (singularLocusClosed f)

instance reducedSingularLocus_isReduced : IsReduced (reducedSingularLocus f) :=
  inferInstanceAs (IsReduced (reducedClosedSubscheme (singularLocusClosed f)))

instance reducedSingularLocusι_isClosedImmersion :
    IsClosedImmersion (reducedSingularLocusι f) :=
  inferInstanceAs (IsClosedImmersion (reducedClosedSubschemeι (singularLocusClosed f)))

variable (Y : Over (Spec ↧ℂ))
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- Let `X` be a smooth integral projective scheme over `ℂ`, and let `Z` be the reduced closure of a
scheme point `x ∈ X`. Starting with the singular locus of `Z`, repeatedly take the singular
locus of the reduced closed subscheme to obtain descending closed subsets `S_k`. This finite
list records those successive closed subsets until the empty set is reached. Each difference
between consecutive terms, with its induced reduced structure, is smooth over `ℂ`. -/
def cycleComponentSingularStratification (x : Y.left) :
    List (Closeds (cycleComponent Y.left x)) :=
  letI := cycleComponent_isNoetherian Y x
  reducedSmoothStratification (cycleComponentι Y.left x ≫ Y.hom)
    (singularLocusClosed (cycleComponentι Y.left x ≫ Y.hom))

end AlgebraicGeometry

end

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

@[simp] theorem range_reducedSingularLocusι :
    Set.range (reducedSingularLocusι f) = (f.smoothLocus : Set X)ᶜ :=
  range_reducedClosedSubschemeι _

/-- Generic smoothness makes the singular locus proper. -/
theorem singularLocusClosed_ne_top [PerfectField K] [IsReduced X] [Nonempty X] :
    singularLocusClosed f ≠ ⊤ := by
  obtain ⟨x, hx⟩ := f.dense_smoothLocus_of_perfectField.nonempty
  intro he
  have : x ∈ singularLocusClosed f := by rw [he]; trivial
  exact this hx

/-- The algebraic dimension drops strictly across the singular locus of a reduced
irreducible scheme. -/
theorem topologicalKrullDim_reducedSingularLocus_lt [PerfectField K] [IsIntegral X]
    {n : ℕ} (hdim : topologicalKrullDim X ≤ n) :
    topologicalKrullDim (reducedSingularLocus f) < n :=
  topologicalKrullDim_lt_of_isClosed_of_ne_univ (singularLocusClosed f).isClosed
    (fun he => singularLocusClosed_ne_top f (SetLike.coe_injective he)) hdim

/-- Each smooth piece has dimension at most that of any containing closed set. -/
theorem topologicalKrullDim_reducedClosedSmoothPiece_le {S T : Closeds X} (hTS : T ≤ S) :
    topologicalKrullDim (reducedClosedSmoothPiece f T) ≤ topologicalKrullDim S := by
  calc
    _ ≤ topologicalKrullDim (reducedClosedSubscheme T) :=
      (reducedClosedStructureMap f T).smoothLocus.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le
    _ ≤ topologicalKrullDim S :=
      (IsEmbedding.inclusion hTS).isInducing.topologicalKrullDim_le

/-- On a smooth complex scheme of algebraic dimension below `m`, every point has a
standard-smooth affine neighborhood of some relative dimension below `m`. -/
theorem Smooth.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt
    {Z : Scheme} (g : Z ⟶ Spec ↧ℂ) [Smooth g] {m : ℕ}
    (hdim : topologicalKrullDim Z < m) (z : Z) :
    ∃ (U : Z.Opens) (_ : IsAffineOpen U), z ∈ U ∧
      ∃ n : ℕ, n < m ∧
        (g.appLE ⊤ U (by simp)).hom.IsStandardSmoothOfRelativeDimension n := by
  obtain ⟨U, hU, hzU, hs⟩ := Smooth.exists_affine_isStandardSmooth g z
  obtain ⟨n, hn⟩ := RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension hs
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have hdimU : topologicalKrullDim U = n := by
    rw [Scheme.topologicalKrullDim_eq_orderKrullDim U.toScheme]
    exact orderKrullDim_eq_of_isStandardSmoothOfRelativeDimension g hU hn
  have hlt := U.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans_lt hdim
  rw [hdimU] at hlt
  exact ⟨U, hU, hzU, n, by exact_mod_cast hlt, hn⟩

variable (Y : Over (Spec ↧ℂ))
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- For a codimension-`p` component of a smooth projective complex `d`-fold, the reduced
singular locus has algebraic dimension strictly less than `d - p`. -/
theorem topologicalKrullDim_cycleComponent_singularLocus_lt
    (x : Y.left) {d p : ℕ} [SmoothOfRelativeDimension d Y.hom]
    (hx : Order.coheight x = p) :
    topologicalKrullDim
      (reducedSingularLocus (cycleComponentι Y.left x ≫ Y.hom)) < (d - p : ℕ) :=
  topologicalKrullDim_reducedSingularLocus_lt _
    (topologicalKrullDim_cycleComponent_le_sub Y x hx)

end AlgebraicGeometry
