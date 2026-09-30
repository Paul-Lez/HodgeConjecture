/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Maps.OpenQuotient

/-!
# Local convexity passes to open quotients

If `f : E → F` is a linear open quotient map (e.g. the projection onto a quotient of a
topological vector space) and `E` is locally convex, then so is `F`
(`LocallyConvexSpace.of_isOpenQuotientMap`): neighbourhoods of `f x` are images of
neighbourhoods of `x`, and images of convex sets under linear maps are convex.
-/

@[expose] public section

open Topology Filter Set

/-- **Local convexity passes to open quotients.** -/
theorem LocallyConvexSpace.of_isOpenQuotientMap {𝕜 E F : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] [LocallyConvexSpace 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] (f : E →ₗ[𝕜] F)
    (hf : IsOpenQuotientMap f) : LocallyConvexSpace 𝕜 F := by
  refine LocallyConvexSpace.ofBases 𝕜 F
    (fun _ s ↦ f '' s) (fun y s ↦ s ∈ 𝓝 (Function.surjInv hf.surjective y) ∧ Convex 𝕜 s)
    (fun y ↦ ?_) fun _ s hs ↦ hs.2.linear_image f
  have h := (LocallyConvexSpace.convex_basis (𝕜 := 𝕜)
    (Function.surjInv hf.surjective y)).map f
  rwa [hf.map_nhds_eq, Function.surjInv_eq hf.surjective y] at h

end
