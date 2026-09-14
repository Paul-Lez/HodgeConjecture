/-
Copyright 2026 The Formal Conjectures Authors.

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

public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.GlobalSections
public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Hypercohomology

For a topological space `X` and an abelian coefficient category `C`, hypercohomology is the
cohomology of derived global sections. The construction is a functor from the bounded-below
derived category to `C`. For `C = ModuleCat R`, it retains the `R`-module structure and gives
`R`-linear maps.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat.Sheaf

universe u v w

variable (C : Type u) [Category.{v} C] [Abelian C]
  (X : TopCat.{w}) [HasSheafify (Opens.grothendieckTopology X) C]

variable [HasDerivedCategory C] [HasDerivedCategory (Sheaf C X)]
  [EnoughInjectives (Sheaf C X)]

/-- Hypercohomology in degree `n`: cohomology after bounded-below derived global sections.

Use `DerivedCategory.Plus.Q` to apply this functor to a bounded-below complex. -/
def hypercohomologyFunctor (n : ℤ) : DerivedCategory.Plus (Sheaf C X) ⥤ C :=
  (globalSectionsFunctor C X).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor C n

instance hypercohomologyFunctor_additive (n : ℤ) :
    (hypercohomologyFunctor C X n).Additive := by
  dsimp only [hypercohomologyFunctor]
  infer_instance

/-- Passing the ordinary global-sections complex through the bounded derived category does not
change its homology, naturally in the bounded-below complex. -/
def globalSectionsHomologyIso (n : ℤ) :
    HomotopyCategory.Plus.quotient (Sheaf C X) ⋙
        (globalSectionsFunctor C X).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.homologyFunctor C n ≅
      CochainComplex.Plus.ι (Sheaf C X) ⋙
        (globalSectionsFunctor C X).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor C (.up ℤ) n :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (HomotopyCategory.Plus.quotient (Sheaf C X) ⋙
          (globalSectionsFunctor C X).mapHomotopyCategoryPlus)
        (DerivedCategory.Plus.QhCompιIsoιCompQh C))
      (DerivedCategory.homologyFunctor C n) ≪≫
    Functor.isoWhiskerLeft
      (HomotopyCategory.Plus.quotient (Sheaf C X) ⋙
        (globalSectionsFunctor C X).mapHomotopyCategoryPlus ⋙
        HomotopyCategory.Plus.ι C)
      (DerivedCategory.homologyFunctorFactorsh C n) ≪≫
    Functor.isoWhiskerRight (Iso.refl _)
      (HomotopyCategory.homologyFunctor C (.up ℤ) n) ≪≫
    Functor.isoWhiskerLeft
      (CochainComplex.Plus.ι (Sheaf C X) ⋙
        (globalSectionsFunctor C X).mapHomologicalComplex (.up ℤ))
      (HomotopyCategory.homologyFunctorFactors C (.up ℤ) n)

/-- The canonical natural transformation from ordinary global-section cohomology to
hypercohomology.

This is the right-derived unit followed by degree-`n` cohomology. -/
def toHypercohomology (n : ℤ) :
    CochainComplex.Plus.ι (Sheaf C X) ⋙
        (globalSectionsFunctor C X).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor C (.up ℤ) n ⟶
      DerivedCategory.Plus.Q ⋙ hypercohomologyFunctor C X n :=
  (globalSectionsHomologyIso C X n).inv ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (HomotopyCategory.Plus.quotient (Sheaf C X))
        (globalSectionsFunctor C X).rightDerivedFunctorPlusUnit)
      (DerivedCategory.Plus.homologyFunctor C n)
instance (K : CochainComplex.Plus (Sheaf C X)) (n : ℤ)
    [∀ i, Injective (K.obj.X i)] : IsIso ((toHypercohomology C X n).app K) := by
  unfold toHypercohomology
  dsimp
  apply IsIso.comp_isIso'
  · infer_instance
  have unit_isIso : IsIso ((globalSectionsFunctor C X).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient _).obj K)) := by
    infer_instance
  exact @Functor.map_isIso _ _ _ _ _ _
    (DerivedCategory.Plus.homologyFunctor C n) _ unit_isIso

/-- A termwise-injective bounded-below complex computes its own hypercohomology. -/
def hypercohomologyIsoOfInjective (K : CochainComplex.Plus (Sheaf C X)) (n : ℤ)
    [∀ i, Injective (K.obj.X i)] :
    (hypercohomologyFunctor C X n).obj (DerivedCategory.Plus.Q.obj K) ≅
      (((globalSectionsFunctor C X).mapHomologicalComplex (.up ℤ)).obj K.obj).homology n :=
  (asIso ((toHypercohomology C X n).app K)).symm

/-- The injective-complex computation of hypercohomology is natural in maps between
termwise-injective bounded-below complexes. -/
@[reassoc]
lemma hypercohomologyIsoOfInjective_hom_naturality
    {K L : CochainComplex.Plus (Sheaf C X)}
    [∀ i, Injective (K.obj.X i)] [∀ i, Injective (L.obj.X i)]
    (f : K ⟶ L) (n : ℤ) :
    (hypercohomologyFunctor C X n).map (DerivedCategory.Plus.Q.map f) ≫
        (hypercohomologyIsoOfInjective C X L n).hom =
      (hypercohomologyIsoOfInjective C X K n).hom ≫
        (CochainComplex.Plus.ι (Sheaf C X) ⋙
          (globalSectionsFunctor C X).mapHomologicalComplex (.up ℤ) ⋙
          HomologicalComplex.homologyFunctor C (.up ℤ) n).map f := by
  change (hypercohomologyFunctor C X n).map (DerivedCategory.Plus.Q.map f) ≫
      inv ((toHypercohomology C X n).app L) =
    inv ((toHypercohomology C X n).app K) ≫
      (CochainComplex.Plus.ι (Sheaf C X) ⋙
        (globalSectionsFunctor C X).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor C (.up ℤ) n).map f
  apply (cancel_mono ((toHypercohomology C X n).app L)).1
  rw [Category.assoc, IsIso.inv_hom_id]
  simp only [Category.comp_id]
  slice_rhs 2 3 =>
    rw [(toHypercohomology C X n).naturality f]
  slice_rhs 1 2 => rw [IsIso.inv_hom_id]
  simp only [Category.id_comp, Functor.comp_map]

end TopCat.Sheaf
