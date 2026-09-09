/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.ClosedSubsetDimensionDrop
public import Other.AlgebraicGeometry.ReducedSmoothStratification
public import Other.AlgebraicGeometry.CycleComponentNormalGeometry
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothEquidimensional

import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothComplexCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.CycleComponentDimension

/-!
# The actual singular locus has smaller algebraic dimension

Over a perfect field the complement of the smooth locus of a reduced irreducible scheme is
a proper closed subset. This file constructs that reduced closed subscheme and proves its
strict Krull-dimension bound, including the `d - p` bound for cycle components.

This is an algebraic dimension theorem. It is not the missing comparison with analytic
homological dimension and does not by itself extend the smooth orientation.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

/-- The closed complement of the actual smooth locus. -/
def singularLocusClosed : Closeds X := f.smoothLocus.compl

/-- The singular locus equipped with its reduced closed-subscheme structure. -/
def reducedSingularLocus : Scheme := reducedClosedSubscheme (singularLocusClosed f)

/-- Its canonical closed immersion in the original scheme. -/
def reducedSingularLocusι : reducedSingularLocus f ⟶ X :=
  reducedClosedSubschemeι (singularLocusClosed f)

instance reducedSingularLocus_isReduced : IsReduced (reducedSingularLocus f) := by
  dsimp [reducedSingularLocus]
  infer_instance

instance reducedSingularLocusι_isClosedImmersion :
    IsClosedImmersion (reducedSingularLocusι f) := by
  change IsClosedImmersion (reducedClosedSubschemeι (singularLocusClosed f))
  infer_instance

@[simp] theorem range_reducedSingularLocusι :
    Set.range (reducedSingularLocusι f) = (f.smoothLocus : Set X)ᶜ :=
  range_reducedClosedSubschemeι _

/-- Generic smoothness makes the actual singular locus proper; no singular-locus bound
is supplied as an input. -/
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
    topologicalKrullDim (reducedSingularLocus f) < n := by
  apply topologicalKrullDim_lt_of_isClosed_of_ne_univ
    (singularLocusClosed f).isClosed _ hdim
  exact fun he => singularLocusClosed_ne_top f (SetLike.coe_injective he)

/-- Each actual smooth piece has dimension at most that of any containing closed set. -/
theorem topologicalKrullDim_reducedClosedSmoothPiece_le {S T : Closeds X} (hTS : T ≤ S) :
    topologicalKrullDim (reducedClosedSmoothPiece f T) ≤ topologicalKrullDim S := by
  calc
    _ ≤ topologicalKrullDim (reducedClosedSubscheme T) :=
      (reducedClosedStructureMap f T).smoothLocus.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le
    _ ≤ topologicalKrullDim S :=
      (IsEmbedding.inclusion hTS).isInducing.topologicalKrullDim_le

/-- On a smooth complex scheme of algebraic dimension below `m`, every point has an
actual standard-smooth affine neighborhood of some relative dimension below `m`.
No global equidimensionality assumption is needed. -/
theorem Smooth.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt
    {Z : Scheme} (g : Z ⟶ Spec (.of ℂ)) [Smooth g] {m : ℕ}
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

variable (Y : Over (Spec (.of ℂ)))
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

/-- The singular locus of every cycle component admits the actual finite smooth
decomposition constructed by Noetherian recursion. -/
def cycleComponentSingularStratification (x : Y.left) :
    List (Closeds (cycleComponent Y.left x)) := by
  letI := cycleComponent_isNoetherian Y x
  exact reducedSmoothStratification (cycleComponentι Y.left x ≫ Y.hom)
    (singularLocusClosed (cycleComponentι Y.left x ≫ Y.hom))

theorem cycleComponentSingularStratification_covers
    (x : Y.left) (y : cycleComponent Y.left x) :
    (∃ T ∈ cycleComponentSingularStratification Y x,
      y ∈ Set.range (reducedClosedSmoothPieceι (cycleComponentι Y.left x ≫ Y.hom) T)) ↔
        y ∉ (cycleComponentι Y.left x ≫ Y.hom).smoothLocus := by
  let := cycleComponent_isNoetherian Y x
  exact reducedSmoothStratification_covers _ _ y

/-- Every constructed smooth stratum of the singular locus has strictly smaller algebraic
dimension than the cycle component. -/
theorem cycleComponentSingularStratification_piece_dimension_lt
    (x : Y.left) {d p : ℕ} [SmoothOfRelativeDimension d Y.hom]
    (hx : Order.coheight x = p) (T : Closeds (cycleComponent Y.left x))
    (hT : T ∈ cycleComponentSingularStratification Y x) :
    topologicalKrullDim
      (reducedClosedSmoothPiece (cycleComponentι Y.left x ≫ Y.hom) T) < (d - p : ℕ) := by
  let := cycleComponent_isNoetherian Y x
  exact (topologicalKrullDim_reducedClosedSmoothPiece_le _
    (reducedSmoothStratification_mem_le _ _ T hT)).trans_lt
      (topologicalKrullDim_cycleComponent_singularLocus_lt Y x hx)

/-- The algebraic dimension bound is realized by actual lower-dimensional smooth affine
charts on each constructed singular-locus stratum. -/
theorem cycleComponentSingularStratification_exists_affine_relativeDimension_lt
    (x : Y.left) {d p : ℕ} [SmoothOfRelativeDimension d Y.hom]
    (hx : Order.coheight x = p) (T : Closeds (cycleComponent Y.left x))
    (hT : T ∈ cycleComponentSingularStratification Y x)
    (z : reducedClosedSmoothPiece (cycleComponentι Y.left x ≫ Y.hom) T) :
    ∃ (U : (reducedClosedSmoothPiece (cycleComponentι Y.left x ≫ Y.hom) T).Opens)
      (_ : IsAffineOpen U), z ∈ U ∧ ∃ n : ℕ, n < d - p ∧
        RingHom.IsStandardSmoothOfRelativeDimension n
          ((reducedClosedSmoothPieceι (cycleComponentι Y.left x ≫ Y.hom) T ≫
            (cycleComponentι Y.left x ≫ Y.hom)).appLE ⊤ U (by simp)).hom :=
  Smooth.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt _
    (cycleComponentSingularStratification_piece_dimension_lt Y x hx T hT) z

end AlgebraicGeometry
