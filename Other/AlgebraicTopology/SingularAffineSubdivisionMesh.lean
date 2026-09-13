/-
Copyright 2026 Paul Lezeau and The Formal Conjectures Authors.

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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Subdivision.AffineMesh

import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.Lebesgue
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Affine barycentric subdivision mesh estimates

The quantitative mesh estimates and cover-smallness bridge for affine barycentric subdivision.
This module is ported from Paul Lezeau's corresponding `sphere-six-complex` pull request #49,
under the Apache-2.0 license.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits PartialOrder Set Simplicial

namespace AlgebraicTopology.Singular

/-- The finite set of barycenters occurring as the vertices of an affine flag simplex. -/
public noncomputable def affineFlagVertexSet (n k : ℕ)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) :
    Set (Fin (n + 1) → ℝ) :=
  Set.range fun j ↦
    (nonemptyFiniteChainBarycenter (F.obj j) : Fin (n + 1) → ℝ)

/-- The vertices of any affine flag simplex satisfy the barycentric mesh estimate. -/
public theorem diam_affineFlagVertexSet_le
    (n k : ℕ) (hn : 1 ≤ n)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) :
    Metric.diam (affineFlagVertexSet n k F) ≤
      barycentricContractionFactor n := by
  apply Metric.diam_le_of_forall_dist_le
    (barycentricContractionFactor_nonneg n)
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  change dist (nonemptyFiniteChainBarycenter (F.obj i))
      (nonemptyFiniteChainBarycenter (F.obj j)) ≤ _
  rcases le_total i j with hij | hji
  · exact dist_nonemptyFiniteChainBarycenter_le n hn _ _
      (CategoryTheory.leOfHom (F.map (CategoryTheory.homOfLE hij)))
  · simpa [dist_comm] using
      dist_nonemptyFiniteChainBarycenter_le n hn _ _
        (CategoryTheory.leOfHom (F.map (CategoryTheory.homOfLE hji)))

/-- Every point of an affine flag simplex lies in the convex hull of its barycenter vertices. -/
public theorem affineFlagContinuousMap_mem_convexHull_vertices
    (n k : ℕ)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k)))
    (w : stdSimplex ℝ (Fin (k + 1))) :
    (affineFlagContinuousMap n k F w : Fin (n + 1) → ℝ) ∈
      convexHull ℝ (affineFlagVertexSet n k F) := by
  classical
  change (fun i ↦ ∑ j, w j * nonemptyFiniteChainBarycenter (F.obj j) i) ∈ _
  have hmem := (convex_convexHull ℝ (affineFlagVertexSet n k F)).sum_mem
    (t := Finset.univ) (w := fun j ↦ w j)
    (z := fun j ↦
      (nonemptyFiniteChainBarycenter (F.obj j) : Fin (n + 1) → ℝ))
    (fun j _ ↦ w.2.1 j) w.2.2 (fun j _ ↦
      subset_convexHull ℝ (affineFlagVertexSet n k F) ⟨j, rfl⟩)
  convert hmem using 1
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The image of every affine flag map contracts the mesh by the factor `n / (n + 1)`.  The
diameter is stated after the isometric inclusion into the ambient function space. -/
public theorem diam_range_affineFlagContinuousMap_coe_le
    (n k : ℕ) (hn : 1 ≤ n)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) :
    Metric.diam (Set.range fun w ↦
      (affineFlagContinuousMap n k F w : Fin (n + 1) → ℝ)) ≤
      barycentricContractionFactor n := by
  calc
    Metric.diam (Set.range fun w ↦
        (affineFlagContinuousMap n k F w : Fin (n + 1) → ℝ)) ≤
        Metric.diam (convexHull ℝ (affineFlagVertexSet n k F)) := by
      apply Metric.diam_mono
      · rintro _ ⟨w, rfl⟩
        exact affineFlagContinuousMap_mem_convexHull_vertices n k F w
      · rw [isBounded_convexHull]
        apply (bounded_stdSimplex (Fin (n + 1))).subset
        rintro _ ⟨j, rfl⟩
        exact (nonemptyFiniteChainBarycenter (F.obj j)).2
    _ = Metric.diam (affineFlagVertexSet n k F) := convexHull_diam _
    _ ≤ _ := diam_affineFlagVertexSet_le n k hn F

/-- Intrinsic version of the affine-flag mesh estimate. -/
public theorem diam_range_affineFlagContinuousMap_le
    (n k : ℕ) (hn : 1 ≤ n)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) :
    Metric.diam (Set.range (affineFlagContinuousMap n k F)) ≤
      barycentricContractionFactor n := by
  apply Metric.diam_le_of_forall_dist_le
    (barycentricContractionFactor_nonneg n)
  rintro _ ⟨w, rfl⟩ _ ⟨w', rfl⟩
  change dist
    (affineFlagContinuousMap n k F w : Fin (n + 1) → ℝ)
    (affineFlagContinuousMap n k F w' : Fin (n + 1) → ℝ) ≤ _
  exact Metric.dist_le_diam_of_mem
    (by
      rw [isBounded_convexHull]
      apply (bounded_stdSimplex (Fin (n + 1))).subset
      rintro _ ⟨j, rfl⟩
      exact (nonemptyFiniteChainBarycenter (F.obj j)).2)
    (affineFlagContinuousMap_mem_convexHull_vertices n k F w)
    (affineFlagContinuousMap_mem_convexHull_vertices n k F w') |>.trans
      (by rw [convexHull_diam]; exact diam_affineFlagVertexSet_le n k hn F)

/-- One actual affine flag cell in the subdivision of a singular simplex maps into a cover
member as soon as the barycentric contraction factor is below the pulled-back Lebesgue number.
This is the direct bridge between the metric estimate in this file and cover-smallness. -/
public theorem singularSimplex_affineFlag_image_subset_cover_of_factor_lt
    {ι : Type} (X : TopCat.{0}) (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ)
    (n : ℕ) (hn : 1 ≤ n)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    ∃ δ > 0, barycentricContractionFactor n < δ →
      ∃ i, X.toSSetObjEquiv _ x '' Set.range (affineFlagContinuousMap n n F) ⊆ U i := by
  let s : Set (stdSimplex ℝ (Fin (n + 1))) :=
    Set.range (affineFlagContinuousMap n n F)
  have hsne : s.Nonempty := Set.range_nonempty _
  have hsbounded : Bornology.IsBounded s :=
    isCompact_univ.isBounded.subset (Set.subset_univ s)
  obtain ⟨δ, hδ, hsmall⟩ := singularSimplex_image_subset_cover_of_diam_lt
    X U hUopen hUcover n x hsne hsbounded
  refine ⟨δ, hδ, fun hfactor ↦ hsmall ?_⟩
  exact (diam_range_affineFlagContinuousMap_le n n hn F).trans_lt hfactor

/-- The proven one-step estimate is the root case of relative mesh contraction. -/
public theorem affineFlagRelativeMeshContraction_at_identity
    (n : ℕ) (hn : 1 ≤ n) (F : TopAffineFlag n) :
    Metric.diam (Set.range
      ((ContinuousMap.id _).comp (affineFlagContinuousMap n n F))) ≤
      barycentricContractionFactor n *
        Metric.diam (Set.range (ContinuousMap.id
          (stdSimplex ℝ (Fin (n + 1))))) := by
  rw [ContinuousMap.id_comp, ContinuousMap.coe_id, Set.range_id,
    diam_univ_stdSimplex n hn, mul_one]
  exact diam_range_affineFlagContinuousMap_le n n hn F

end AlgebraicTopology.Singular
