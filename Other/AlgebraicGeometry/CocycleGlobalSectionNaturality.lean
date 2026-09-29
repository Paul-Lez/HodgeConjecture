/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CocycleGlobalSections
public import Other.AlgebraicTopology.CohomologySheafSectionDerivedVanishing

/-!
# Naturality and local vanishing of the actual global cocycle section

The explicit global cycle, its class, and its canonical cohomology-sheaf section
commute with postcomposition by a coefficient map. In particular, a map which
vanishes after derived restriction contributes zero to the normalized section
on that open. The representative is the original Hom-complex representative.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open CochainComplex.HomComplex
set_option autoImplicit false
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000

namespace TopCat.Sheaf

variable (Y : TopCat.{0}) {K L : CochainComplex (Sheaf AddCommGrpCat Y) ℤ}
  (f : K ⟶ L) (n : ℤ) (z : Cocycle (integerConstantSingleComplex Y) K n)

/-- The prescribed cycle representative commutes with postcomposition. -/
lemma integerCocycleGlobalSection_postcomp :
    integerCocycleGlobalSection Y L n (z.postcomp f) =
      cyclesMap (((IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
        (.up ℤ)).map f) n (integerCocycleGlobalSection Y K n z) := by
  apply (AddCommGrpCat.mono_iff_injective ((globalSectionsComplexInt Y L).iCycles n)).mp
    inferInstance
  rw [iCycles_integerCocycleGlobalSection]
  have hcycle := ConcreteCategory.congr_hom (cyclesMap_i
    (((IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
      (.up ℤ)).map f) n) (integerCocycleGlobalSection Y K n z)
  have hcomponent :
      ((postcompMap (integerConstantSingleComplex Y) f).f n) ≫
        (homComplexSingleIntegerIsoGlobalSections Y L).hom.f n =
      (homComplexSingleIntegerIsoGlobalSections Y K).hom.f n ≫
        (((IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
          (.up ℤ)).map f).f n :=
    HomologicalComplex.congr_hom (homComplexSingleIntegerIsoGlobalSections_naturality Y f) n
  have hnat := ConcreteCategory.congr_hom hcomponent z.1
  exact hnat.trans (hcycle.trans (congrArg
    ((((IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
      (.up ℤ)).map f).f n) (iCycles_integerCocycleGlobalSection Y K n z))).symm

/-- The actual global cohomology class commutes with the actual coefficient map. -/
lemma homologyπ_integerCocycleGlobalSection_postcomp :
    (globalSectionsComplexInt Y L).homologyπ n (integerCocycleGlobalSection Y L n (z.postcomp f)) =
      homologyMap (((IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
        (.up ℤ)).map f) n
        ((globalSectionsComplexInt Y K).homologyπ n (integerCocycleGlobalSection Y K n z)) := by
  rw [integerCocycleGlobalSection_postcomp]
  exact (ConcreteCategory.congr_hom (homologyπ_naturality
    (((IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
      (.up ℤ)).map f) n) (integerCocycleGlobalSection Y K n z)).symm

/-- Postcomposition is compatible with the original cohomology-sheaf section
normalization, including the actual global cocycle representative. -/
lemma sectionCohomology_integerCocycleGlobalSection_postcomp :
    sectionCohomologyToSheafSection Y L n ⊤
      ((globalSectionsComplexInt Y L).homologyπ n
        (integerCocycleGlobalSection Y L n (z.postcomp f))) =
      (homologyMap f n).hom.app (op ⊤)
        (sectionCohomologyToSheafSection Y K n ⊤
          ((globalSectionsComplexInt Y K).homologyπ n (integerCocycleGlobalSection Y K n z))) := by
  rw [homologyπ_integerCocycleGlobalSection_postcomp]
  exact ConcreteCategory.congr_hom (sectionCohomologyToSheafSection_naturality Y f n ⊤)
    ((globalSectionsComplexInt Y K).homologyπ n (integerCocycleGlobalSection Y K n z))

variable [HasDerivedCategory (Sheaf AddCommGrpCat Y)] (U : Opens Y)
  [HasDerivedCategory (Sheaf AddCommGrpCat ((Opens.toTopCat Y).obj U))]

/-- A postcomposed cocycle has zero normalized section locally whenever its
coefficient map is zero after actual derived restriction. -/
lemma sectionCohomology_integerCocycleGlobalSection_postcomp_onOpen_eq_zero
    (hf : (U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapDerivedCategory.map
      (DerivedCategory.Q.map f) = 0) (W : Opens (TopCat.of U)) :
    (L.homology n).obj.map (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
      (sectionCohomologyToSheafSection Y L n ⊤
        ((globalSectionsComplexInt Y L).homologyπ n
          (integerCocycleGlobalSection Y L n (z.postcomp f)))) = 0 := by
  rw [sectionCohomology_integerCocycleGlobalSection_postcomp]
  have hnat := ConcreteCategory.congr_hom ((homologyMap f n).hom.naturality
    (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op)
    (sectionCohomologyToSheafSection Y K n ⊤
      ((globalSectionsComplexInt Y K).homologyπ n (integerCocycleGlobalSection Y K n z)))
  have hz := homologyMap_onOpen_eq_zero_of_derived_restriction_eq_zero Y f U hf n W
  exact hnat.symm.trans (by rw [hz]; rfl)

omit f n z in
/-- In degree zero, the section of the actual cocycle of a derived-null map
from the constant integer complex vanishes on the restricted open. -/
lemma sectionCohomology_integerCocycleGlobalSection_ofHom_onOpen_eq_zero
    (g : integerConstantSingleComplex Y ⟶ K)
    (hg : (U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapDerivedCategory.map
      (DerivedCategory.Q.map g) = 0) (W : Opens (TopCat.of U)) :
    (K.homology 0).obj.map (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
      (sectionCohomologyToSheafSection Y K 0 ⊤
        ((globalSectionsComplexInt Y K).homologyπ 0
          (integerCocycleGlobalSection Y K 0 (Cocycle.ofHom g)))) = 0 := by
  have he : (Cocycle.ofHom (𝟙 (integerConstantSingleComplex Y))).postcomp g =
      Cocycle.ofHom g := by
    apply Subtype.ext
    exact Cochain.id_comp (Cochain.ofHom g)
  exact (congrArg (fun w => (K.homology 0).obj.map
    (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
      (sectionCohomologyToSheafSection Y K 0 ⊤
        ((globalSectionsComplexInt Y K).homologyπ 0
          (integerCocycleGlobalSection Y K 0 w)))) he).symm.trans
    (sectionCohomology_integerCocycleGlobalSection_postcomp_onOpen_eq_zero Y g 0
      (Cocycle.ofHom (𝟙 (integerConstantSingleComplex Y))) U hg W)

end TopCat.Sheaf
