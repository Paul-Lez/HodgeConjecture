/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.Sheaf.CohomologySectionNaturality
public import Other.AlgebraicTopology.Sheaf.CohomologySectionShiftTop

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace TopCat.Sheaf

lemma sectionCohomologyToSheafSection_restrict_eq_of_homologyMap
    (Y : TopCat.{0})
    (K L : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ)
    (m : K ⟶ L) (n : ℤ)
    (a : (TopCat.Sheaf.globalSectionsComplexInt Y K).homology n)
    (b : (TopCat.Sheaf.globalSectionsComplexInt Y L).homology n)
    (hm : HomologicalComplex.homologyMap
      (((TopCat.Sheaf.supportEvaluation Y ⊤).mapHomologicalComplex (.up ℤ)).map m) n a = b)
    (W : Opens Y)
    (t : (L.homology n).obj.obj (op W))
    (hL : (L.homology n).obj.map (homOfLE (le_top : W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y L n ⊤ b) = t) :
    (HomologicalComplex.homologyMap m n).hom.app (op W)
        ((K.homology n).obj.map (homOfLE (le_top : W ≤ ⊤)).op
          (TopCat.Sheaf.sectionCohomologyToSheafSection Y K n ⊤ a)) = t := by
  change HomologicalComplex.homologyMap
      (((TopCat.Sheaf.supportEvaluation Y ⊤).mapHomologicalComplex (.up ℤ)).map m) n a = b at hm
  let H := HomologicalComplex.homologyMap m n
  have hnat := ConcreteCategory.congr_hom
    (TopCat.Sheaf.sectionCohomologyToSheafSection_naturality Y m n ⊤) a
  have hnatW := ConcreteCategory.congr_hom
    (H.hom.naturality (homOfLE (le_top : W ≤ ⊤)).op)
    (TopCat.Sheaf.sectionCohomologyToSheafSection Y K n ⊤ a)
  have hnat' := hnat
  have hnatW' := hnatW
  simp only [ConcreteCategory.comp_apply] at hnat' hnatW'
  rw [hnatW', ← hnat', hm, hL]

lemma sectionCohomologyShift_restrict_eq
    (Y : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ)
    (n : ℤ)
    (a : (TopCat.Sheaf.globalSectionsComplexInt Y (K⟦(1 : ℤ)⟧)).homology (n - 1))
    (W : Opens Y)
    (t : ((K⟦(1 : ℤ)⟧).homology (n - 1)).obj.obj (op W))
    (ht : ((K⟦(1 : ℤ)⟧).homology (n - 1)).obj.map
      (homOfLE (le_top : W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y (K⟦(1 : ℤ)⟧)
        (n - 1) ⊤ a) = t) :
    (K.homology n).obj.map (homOfLE (le_top : W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y K n ⊤
        (ShortComplex.homologyMap
          (TopCat.Sheaf.globalSectionsShiftShortComplex Y K 1 (n - 1) n (by omega)) a)) =
      (TopCat.Sheaf.sectionCohomologySheafShiftMap Y K 1 (n - 1) n (by omega)).hom.app
        (op W) t := by
  let h : (1 : ℤ) + (n - 1) = n := by omega
  have hshiftTop := TopCat.Sheaf.sectionCohomologyToSheafSection_shift_naturality
    Y K 1 (n - 1) n h ⊤
  have htop := TopCat.Sheaf.sectionCohomologyPresheafShiftShortComplex_top_homology
    Y K 1 (n - 1) n h
  rw [htop] at hshiftTop
  have hshiftTopA := ConcreteCategory.congr_hom hshiftTop a
  have hshiftTopR := congrArg
    (fun y => (K.homology n).obj.map (homOfLE (le_top : W ≤ ⊤)).op y) hshiftTopA
  have hnat := ConcreteCategory.congr_hom
    ((TopCat.Sheaf.sectionCohomologySheafShiftMap Y K 1 (n - 1) n h).hom.naturality
      (homOfLE (le_top : W ≤ ⊤)).op)
    (TopCat.Sheaf.sectionCohomologyToSheafSection Y (K⟦(1 : ℤ)⟧)
      (n - 1) ⊤ a)
  have ht' := congrArg
    (fun y => (TopCat.Sheaf.sectionCohomologySheafShiftMap Y K 1 (n - 1) n h).hom.app
      (op W) y) ht
  simp only [ConcreteCategory.comp_apply] at hshiftTopA hshiftTopR hnat ht'
  dsimp [h] at hshiftTopA hshiftTopR hnat ht' ⊢
  exact hshiftTopR.trans (hnat.symm.trans ht')

end TopCat.Sheaf
