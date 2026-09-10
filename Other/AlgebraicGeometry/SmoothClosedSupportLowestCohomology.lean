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

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))

local instance smoothClosedSupportLowestAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- The actual supported injective coefficient sheaves are flasque, by the
proved gluing-with-zero theorem for the defining support kernel. -/
theorem complexSupportInjectiveComplex_isFlasque
    (S : Closeds (ComplexPoint X)) (n : ℤ) :
    ((complexSupportInjectiveComplex X S).X n).IsFlasque :=
  TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
    (TopCat.of (ComplexPoint X)) S.compl ((ambientRationalInjectiveComplex X).X n)

variable [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (Y : Over (Spec (.of ℂ))) (i : Y ⟶ X)
  (m d : ℕ) [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

/-- Actual supported cohomology in twice the normal complex dimension is
the section group of the actual cohomology sheaf, on every open set. -/
def smoothClosedSupportLowestSectionCohomologyIso (U : Opens (ComplexPoint X)) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X
        (smoothClosedAnalyticSupport X Y i)))).homology (2 * ((d - m : ℕ) : ℤ)) ≅
      ((complexSupportInjectiveComplex X (smoothClosedAnalyticSupport X Y i)).homology
        (2 * ((d - m : ℕ) : ℤ))).obj.obj (op U) :=
  TopCat.Sheaf.lowestSectionCohomologyIso (TopCat.of (ComplexPoint X))
    (complexSupportInjectiveComplex X (smoothClosedAnalyticSupport X Y i)) 0
    (2 * ((d - m : ℕ) : ℤ))
    (fun j hj => smoothClosedSupportInjective_homology_isZero_of_ne
      X Y i m d j (ne_of_lt hj))
    (complexSupportInjectiveComplex_isFlasque X _) U

/-- The forward map is exactly the canonical local-cohomology-to-sheaf-section
map, rather than an independently chosen comparison of groups. -/
@[simp]
theorem smoothClosedSupportLowestSectionCohomologyIso_hom (U : Opens (ComplexPoint X)) :
    (smoothClosedSupportLowestSectionCohomologyIso X Y i m d U).hom =
      TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X (smoothClosedAnalyticSupport X Y i))
        (2 * ((d - m : ℕ) : ℤ)) U := rfl

/-- Supported cohomology itself vanishes below twice the normal complex
dimension on every open. Higher-degree global vanishing is not asserted. -/
theorem smoothClosedSupportSectionCohomology_isZero_of_lt
    (U : Opens (ComplexPoint X)) (n : ℤ) (hn : n < 2 * ((d - m : ℕ) : ℤ)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X
        (smoothClosedAnalyticSupport X Y i))).homology n) := by
  let e := TopCat.Sheaf.lowestSectionCohomologyIso (TopCat.of (ComplexPoint X))
    (complexSupportInjectiveComplex X (smoothClosedAnalyticSupport X Y i)) 0 n
    (fun j hj => smoothClosedSupportInjective_homology_isZero_of_ne
      X Y i m d j (ne_of_lt (hj.trans hn)))
    (complexSupportInjectiveComplex_isFlasque X _) U
  exact ((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) U).map_isZero
    (smoothClosedSupportInjective_homology_isZero_of_ne X Y i m d n (ne_of_lt hn))).of_iso e

end AlgebraicGeometry.ComplexPoint
