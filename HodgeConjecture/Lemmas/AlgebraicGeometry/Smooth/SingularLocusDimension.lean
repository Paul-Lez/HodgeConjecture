/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Smooth.SingularLocusDimension

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
import HodgeConjecture.Mathlib.AlgebraicGeometry.PointClosure
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Support
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import HodgeConjecture.Mathlib.Topology.KrullDimension

/-!
# The actual singular locus has smaller algebraic dimension

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Smooth.SingularLocusDimension`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

/-- The singular locus equipped with its reduced closed-subscheme structure. -/
def reducedSingularLocus : Scheme := X.reducedClosedSubscheme (singularLocusClosed f)

/-- Its canonical closed immersion in the original scheme. -/
def reducedSingularLocusι : reducedSingularLocus f ⟶ X :=
  X.reducedClosedSubschemeι (singularLocusClosed f)

instance reducedSingularLocus_isReduced : IsReduced (reducedSingularLocus f) :=
  inferInstanceAs (IsReduced (X.reducedClosedSubscheme (singularLocusClosed f)))

instance reducedSingularLocusι_isClosedImmersion :
    IsClosedImmersion (reducedSingularLocusι f) :=
  inferInstanceAs (IsClosedImmersion (X.reducedClosedSubschemeι (singularLocusClosed f)))

variable (Y : Over (Spec ↧ℂ)) [IsNoetherian Y.left] [LocallyOfFiniteType Y.hom]

namespace CycleComponent

/-- The finite smooth stratification of the singular locus of the cycle component at `x`. -/
def singularStratification (x : Y.left) :
    List (Closeds (Y.left.pointClosure x)) :=
  reducedSmoothStratification (Y.left.pointClosureι x ≫ Y.hom)
    (singularLocusClosed (Y.left.pointClosureι x ≫ Y.hom))

end CycleComponent

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
  X.range_reducedClosedSubschemeι _

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
    topologicalKrullDim (reducedSingularLocus f) < n :=
  topologicalKrullDim_lt_of_isClosed_of_ne_univ (singularLocusClosed f).isClosed
    (fun he => singularLocusClosed_ne_top f (SetLike.coe_injective he)) hdim

/-- Each actual smooth piece has dimension at most that of any containing closed set. -/
theorem topologicalKrullDim_reducedClosedSmoothPiece_le {S T : Closeds X} (hTS : T ≤ S) :
    topologicalKrullDim (reducedClosedSmoothPiece f T) ≤ topologicalKrullDim S := by
  calc
    _ ≤ topologicalKrullDim (X.reducedClosedSubscheme T) :=
      (reducedClosedStructureMap f T).smoothLocus.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le
    _ ≤ topologicalKrullDim S :=
      (IsEmbedding.inclusion hTS).isInducing.topologicalKrullDim_le

/-- On a smooth complex scheme of algebraic dimension below `m`, every point has an
actual standard-smooth affine neighborhood of some relative dimension below `m`.
No global equidimensionality assumption is needed. -/
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
    rw [topologicalKrullDim_eq_krullDim U.toScheme]
    exact orderKrullDim_eq_of_isStandardSmoothOfRelativeDimension g hU hn
  have hlt := U.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans_lt hdim
  rw [hdimU] at hlt
  exact ⟨U, hU, hzU, n, by exact_mod_cast hlt, hn⟩

variable (Y : Over (Spec ↧ℂ))
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

namespace CycleComponent

/-- For a codimension-`p` component of a smooth projective complex `d`-fold, the reduced
singular locus has algebraic dimension strictly less than `d - p`. -/
theorem topologicalKrullDim_singularLocus_lt
    (x : Y.left) {d p : ℕ} [SmoothOfRelativeDimension d Y.hom]
    (hx : Order.coheight x = p) :
    topologicalKrullDim
      (reducedSingularLocus (Y.left.pointClosureι x ≫ Y.hom)) < (d - p : ℕ) :=
  topologicalKrullDim_reducedSingularLocus_lt _
    (topologicalKrullDim_le_sub Y x hx)

end CycleComponent

end AlgebraicGeometry
