/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicGeometry.ChernWindingBoundary
public import Other.AlgebraicGeometry.ChernWindingNormalChartBoundary

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular

namespace ChernWinding

variable {M : Type} [TopologicalSpace M]

/-- Relative winding classes commute with the support-inclusion map of pairs. -/
theorem windingRelativeClass_supportMap
    {W S T : Set M}
    (gS : C(puncturedSpace W S, ℂ)) (hgS : ∀ y, gS y ≠ 0)
    (gT : C(puncturedSpace W T, ℂ)) (hgT : ∀ y, gT y ≠ 0)
    (p : supportPair W T ⟶ supportPair W S)
    (hcomp : gS.comp (topMap (TopPair.Hom.snd p)) = gT)
    (hS : HasRationalWindingPeriod W S gS hgS)
    (hT : HasRationalWindingPeriod W T gT hgT) :
    relativeCohomologyMap ℚ 2 p (windingRelativeClass W S hS) =
      windingRelativeClass W T hT := by
  refine windingRelativeClass_unique W T hT _ ?_
  ext z
  simp only [LinearMap.comp_apply]
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap]
  change (((relativeCohomologyEquivDualHomology ℚ (supportPair W S) 2
    (windingRelativeClass W S hS) (relativeHomologyMap ℚ 2 p z) : ℚ) : ℂ)) = _
  rw [windingRelativeClass_apply W S hS, relativeWindingPeriod_apply]
  rw [relativeWindingPeriod_apply W T gT hgT]
  have hb := relativeSingularBoundary_relativeHomologyMap p 1 z
  rw [hb]
  have hmap := AlgebraicTopology.Singular.homologyMap_eq_chainPairFunctor_left p 1
    ((relativeSingularBoundary (supportPair W T) 1).hom z)
  rw [← hmap]
  have hgf : ∀ y, (gS.comp (topMap (TopPair.Hom.snd p))) y ≠ 0 := by
    intro y
    rw [hcomp]
    exact hgT y
  have hw := windingPeriod_map gS (TopPair.Hom.snd p) hgS hgf
    ((relativeSingularBoundary (supportPair W T) 1).hom z)
  exact hw.symm.trans (by simp only [hcomp])

end ChernWinding
