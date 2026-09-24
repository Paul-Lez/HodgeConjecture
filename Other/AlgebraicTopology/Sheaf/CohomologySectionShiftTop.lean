/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.Sheaf.CohomologySectionShiftTransport
public import Other.AlgebraicGeometry.Cohomology.HypercohomologyShift

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TopCat.Sheaf

lemma sectionCohomologyPresheafShiftShortComplex_top_homology
    (Y : TopCat.{0}) (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ)
    (s n n' : ℤ) (h : s + n = n') :
    ShortComplex.homologyMap
      (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (op ⊤)).mapShortComplex.map
        (sectionCohomologyPresheafShiftShortComplex Y K s n n' h)) =
      ShortComplex.homologyMap
        (globalSectionsShiftShortComplex Y K s n n' (by omega)) := by
  apply ShortComplex.homologyMap_eq_of_middle_eq
  subst n'
  simp [sectionCohomologyPresheafShiftShortComplex, globalSectionsShiftShortComplex,
    HomologicalComplex.XIsoOfEq]
  exact (Category.id_comp _).symm

end TopCat.Sheaf
