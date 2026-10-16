/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# The sup metric on finite standard simplices
-/

public noncomputable section

namespace Convexity.StdSimplex

lemma weights_map_apply {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (t : StdSimplex ℝ ι) (y : κ) :
    (t.map f).weights y = ∑ x with f x = y, t.weights x := by
  classical
  simp [weights_map, Finsupp.mapDomain_apply, Finsupp.sum_fintype, Finsupp.single_apply,
    Finset.sum_filter]

instance {ι : Type*} [Fintype ι] : MetricSpace (StdSimplex ℝ ι) :=
  (isEmbedding_toFun_comp_weights ℝ ι).comapMetricSpace (fun t ↦ (t.weights : ι → ℝ))

lemma isometry_weights {ι : Type*} [Fintype ι] :
    Isometry (fun t ↦ (t.weights : ι → ℝ) : StdSimplex ℝ ι → ι → ℝ) := by
  rw [isometry_iff_dist_eq]
  intros
  rfl

end Convexity.StdSimplex
