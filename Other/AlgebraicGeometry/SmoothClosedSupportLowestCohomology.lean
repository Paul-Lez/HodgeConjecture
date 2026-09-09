/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SmoothClosedSupportCohomologySheaf
public import Other.AlgebraicTopology.FlasqueSupportedSections
public import Other.AlgebraicTopology.LowestFlasqueCohomology

/-!
# Actual lowest-degree globalization for smooth closed supports

The geometric cohomology-sheaf concentration theorem supplies the lower
vanishing needed by the canonical lowest-degree comparison. Flasqueness of
the supported injective model is proved from its actual kernel definition.
Thus the comparison below has no purity, acyclicity, or group-equivalence
input: its forward map is the already constructed sheafification comparison.
This still does not define the normalized section of the surviving sheaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (sX : X ⟶ Spec (.of ℂ))

local instance smoothClosedSupportLowestAnalyticTopology :
    TopologicalSpace (ComplexPoint X sX) := Point.analyticTopology

/-- The actual supported injective coefficient sheaves are flasque, by the
proved gluing-with-zero theorem for the defining support kernel. -/
theorem complexSupportInjectiveComplex_isFlasque
    (S : Closeds (ComplexPoint X sX)) (n : ℤ) :
    ((complexSupportInjectiveComplex sX S).X n).IsFlasque := by
  exact TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
    (TopCat.of (ComplexPoint X sX)) S.compl ((ambientRationalInjectiveComplex sX).X n)

variable [IsIntegral X] [Smooth sX] [IsProjective sX]
  {Y : Scheme} (sY : Y ⟶ Spec (.of ℂ)) (i : Y ⟶ X) (hi : i ≫ sX = sY)
  (m d : ℕ) [SmoothOfRelativeDimension m sY] [SmoothOfRelativeDimension d sX]
  [IsClosedImmersion i]

/-- Actual supported cohomology in twice the normal complex dimension is
the section group of the actual cohomology sheaf, on every open set. -/
def smoothClosedSupportLowestSectionCohomologyIso (U : Opens (ComplexPoint X sX)) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X sX)) U).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex sX
        (smoothClosedAnalyticSupport sX sY i hi)))).homology (2 * ((d - m : ℕ) : ℤ)) ≅
      ((complexSupportInjectiveComplex sX (smoothClosedAnalyticSupport sX sY i hi)).homology
        (2 * ((d - m : ℕ) : ℤ))).obj.obj (op U) :=
  TopCat.Sheaf.lowestSectionCohomologyIso (TopCat.of (ComplexPoint X sX))
    (complexSupportInjectiveComplex sX (smoothClosedAnalyticSupport sX sY i hi)) 0
    (2 * ((d - m : ℕ) : ℤ))
    (fun j hj => smoothClosedSupportInjective_homology_isZero_of_ne
      sX sY i hi m d j (ne_of_lt hj))
    (complexSupportInjectiveComplex_isFlasque sX _) U

/-- The forward map is exactly the canonical local-cohomology-to-sheaf-section
map, rather than an independently chosen comparison of groups. -/
@[simp]
theorem smoothClosedSupportLowestSectionCohomologyIso_hom (U : Opens (ComplexPoint X sX)) :
    (smoothClosedSupportLowestSectionCohomologyIso sX sY i hi m d U).hom =
      TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X sX))
        (complexSupportInjectiveComplex sX (smoothClosedAnalyticSupport sX sY i hi))
        (2 * ((d - m : ℕ) : ℤ)) U := rfl

/-- Supported cohomology itself vanishes below twice the normal complex
dimension on every open. Higher-degree global vanishing is not asserted. -/
theorem smoothClosedSupportSectionCohomology_isZero_of_lt
    (U : Opens (ComplexPoint X sX)) (n : ℤ) (hn : n < 2 * ((d - m : ℕ) : ℤ)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X sX)) U).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex sX
        (smoothClosedAnalyticSupport sX sY i hi))).homology n) := by
  let e := TopCat.Sheaf.lowestSectionCohomologyIso (TopCat.of (ComplexPoint X sX))
    (complexSupportInjectiveComplex sX (smoothClosedAnalyticSupport sX sY i hi)) 0 n
    (fun j hj => smoothClosedSupportInjective_homology_isZero_of_ne
      sX sY i hi m d j (ne_of_lt (hj.trans hn)))
    (complexSupportInjectiveComplex_isFlasque sX _) U
  exact ((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X sX)) U).map_isZero
    (smoothClosedSupportInjective_homology_isZero_of_ne sX sY i hi m d n (ne_of_lt hn))).of_iso e

end AlgebraicGeometry.ComplexPoint
