/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.Sheaf.CohomologySectionNaturality
public import Other.AlgebraicTopology.Sheaf.CohomologyOpenRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Local cohomology-sheaf sections of maps vanishing in the derived category

The canonical section-to-cohomology-sheaf map kills the image of a coefficient
map which becomes zero after derived restriction. The proof retains the actual
section normalization and the exact restriction comparison. It does not assert
that taking sections on an open set is exact.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
set_option autoImplicit false
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

/-- A map which is zero in the derived category induces the zero homology map. -/
lemma homologyMap_eq_zero_of_Q_map_eq_zero (hf : DerivedCategory.Q.map f = 0) (n : ℤ) :
    homologyMap f n = 0 := by
  apply (cancel_epi ((DerivedCategory.homologyFunctorFactors C n).hom.app K)).mp
  have h := DerivedCategory.homologyFunctorFactors_hom_naturality f n
  simpa only [hf, Functor.map_zero, zero_comp, comp_zero] using h.symm

end HomologicalComplex

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

/-- Exact functoriality transports derived vanishing to the actual mapped complex. -/
lemma Q_map_mapHomologicalComplex_eq_zero_of_mapDerivedCategory_eq_zero
    (hf : F.mapDerivedCategory.map (DerivedCategory.Q.map f) = 0) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) = 0 := by
  apply (cancel_epi (F.mapDerivedCategoryFactors.hom.app K)).mp
  have h := F.mapDerivedCategoryFactors_hom_naturality f
  simpa only [hf, zero_comp, comp_zero] using h.symm

/-- The actual homology map after an exact functor vanishes whenever its
derived map vanishes. -/
lemma homologyMap_mapHomologicalComplex_eq_zero_of_mapDerivedCategory_eq_zero
    (hf : F.mapDerivedCategory.map (DerivedCategory.Q.map f) = 0) (n : ℤ) :
    homologyMap ((F.mapHomologicalComplex (.up ℤ)).map f) n = 0 :=
  homologyMap_eq_zero_of_Q_map_eq_zero _
    (F.Q_map_mapHomologicalComplex_eq_zero_of_mapDerivedCategory_eq_zero f hf) n

end CategoryTheory.Functor

namespace TopCat.Sheaf

universe u
variable (Y : TopCat.{u}) [HasDerivedCategory (Sheaf AddCommGrpCat.{u} Y)]
  {K L : CochainComplex (Sheaf AddCommGrpCat.{u} Y) ℤ} (f : K ⟶ L)

/-- The prescribed local section normalization kills the image of a
coefficient map which is zero in the derived category. -/
lemma sectionCohomologyToSheafSection_map_eq_zero_of_Q_map_eq_zero
    (hf : DerivedCategory.Q.map f = 0) (n : ℤ) (U : Opens Y) :
    homologyMap (((supportEvaluation Y U).mapHomologicalComplex (.up ℤ)).map f) n ≫
      sectionCohomologyToSheafSection Y L n U = 0 := by
  rw [sectionCohomologyToSheafSection_naturality,
    homologyMap_eq_zero_of_Q_map_eq_zero f hf n]
  exact comp_zero

variable (U : Opens Y)
  [HasDerivedCategory (Sheaf AddCommGrpCat.{u} ((Opens.toTopCat Y).obj U))]

/-- Vanishing after actual derived restriction makes the existing homology
sheaf map zero on every open of the restricted space. -/
lemma homologyMap_onOpen_eq_zero_of_derived_restriction_eq_zero
    (hf : (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapDerivedCategory.map
      (DerivedCategory.Q.map f) = 0) (n : ℤ) (W : Opens (TopCat.of U)) :
    (homologyMap f n).hom.app (op (U.isOpenEmbedding.functor.obj W)) = 0 := by
  let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}
  have hz := F.homologyMap_mapHomologicalComplex_eq_zero_of_mapDerivedCategory_eq_zero
    f hf n
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor _ (.up ℤ) n).map f) F
  change homologyMap ((F.mapHomologicalComplex (.up ℤ)).map f) n ≫
    ((L.sc n).mapHomologyIso F).hom =
      ((K.sc n).mapHomologyIso F).hom ≫ F.map (homologyMap f n) at hn
  have hm : F.map (homologyMap f n) = 0 := by
    apply (cancel_epi ((K.sc n).mapHomologyIso F).hom).mp
    simpa only [hz, zero_comp, comp_zero] using hn.symm
  exact congrArg (fun a => a.hom.app (op W)) hm

/-- Local classes in the image of a map vanishing after derived restriction
have zero image under the original ambient cohomology-sheaf normalization. -/
lemma sectionCohomologyToSheafSection_map_eq_zero_of_derived_restriction_eq_zero
    (hf : (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapDerivedCategory.map
      (DerivedCategory.Q.map f) = 0) (n : ℤ) (W : Opens (TopCat.of U)) :
    homologyMap (((supportEvaluation Y (U.isOpenEmbedding.functor.obj W)).mapHomologicalComplex
      (.up ℤ)).map f) n ≫
      sectionCohomologyToSheafSection Y L n (U.isOpenEmbedding.functor.obj W) = 0 := by
  rw [sectionCohomologyToSheafSection_naturality,
    homologyMap_onOpen_eq_zero_of_derived_restriction_eq_zero Y f U hf n W, comp_zero]

end TopCat.Sheaf
