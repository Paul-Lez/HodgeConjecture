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
public import HodgeConjecture.Mathlib.Algebra.Homology.CochainComplexPlus
public import HodgeConjecture.Mathlib.Algebra.Homology.MapExtend
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Hypercohomology

For a topological space `X` and an abelian coefficient category `C`, derived global sections form
a functor between bounded-below derived categories. Degree-`n` hypercohomology is obtained by
composing this functor with degree-`n` cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat.Sheaf

universe u v w

variable (C : Type u) [Category.{v} C] [Abelian C]
  (X : TopCat.{w}) [HasSheafify (Opens.grothendieckTopology X) C]

variable [HasDerivedCategory C] [HasDerivedCategory (Sheaf C X)]
  [EnoughInjectives (Sheaf C X)]

/-- Derived global sections on bounded-below derived categories. -/
def derivedGlobalSectionsFunctor :
    DerivedCategory.Plus (Sheaf C X) ⥤ DerivedCategory.Plus C :=
  (globalSectionsFunctor C X).rightDerivedFunctorPlus

/-- Hypercohomology in degree `n`, as a functor on bounded-below sheaf complexes. -/
def hypercohomologyFunctor (n : ℤ) : CochainComplex.Plus (Sheaf C X) ⥤ C :=
  DerivedCategory.Plus.Q ⋙ derivedGlobalSectionsFunctor C X ⋙
    DerivedCategory.Plus.homologyFunctor C n

/-- Notation for the degree-`n` hypercohomology functor on bounded-below sheaf complexes. -/
scoped notation3:max "ℍ[" C "]^" n:max "(" X ")" =>
  hypercohomologyFunctor C X n

instance derivedGlobalSectionsFunctor_additive :
    (derivedGlobalSectionsFunctor C X).Additive := by
  dsimp only [derivedGlobalSectionsFunctor]
  infer_instance

instance hypercohomologyFunctor_additive (n : ℤ) :
    (hypercohomologyFunctor C X n).Additive := by
  dsimp only [hypercohomologyFunctor]
  infer_instance

instance hypercohomologyFunctor_map_isIso
    {K L : CochainComplex.Plus (Sheaf C X)} (f : K ⟶ L) [QuasiIso f.hom] (n : ℤ) :
    IsIso ((hypercohomologyFunctor C X n).map f) := by
  unfold hypercohomologyFunctor
  dsimp only [Functor.comp_map]
  infer_instance

/-- The cohomology in degree zero of the global sections of an object placed in degree zero is
canonically its object of global sections. -/
def globalSectionsSingle₀HomologyIso (A : Sheaf C X) :
    (((globalSectionsFunctor C X).mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.Plus.single₀ (Sheaf C X)).obj A).obj).homology 0 ≅
      (globalSectionsFunctor C X).obj A :=
  let Γ := globalSectionsFunctor C X
  let e := ComplexShape.embeddingUpNat
  let K := (CochainComplex.single₀ (Sheaf C X)).obj A
  HomologicalComplex.homologyMapIso
      (HomologicalComplex.mapExtendCanonicalIso Γ K e ≪≫
        (e.extendFunctor C).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℕ) 0).app A) ≪≫
        HomologicalComplex.extendSingleIso e (Γ.obj A) 0 0 rfl) 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 ((globalSectionsFunctor C X).obj A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasDerivedCategory C] [HasDerivedCategory (Sheaf C X)]
  [EnoughInjectives (Sheaf C X)] in
/-- The degree-zero comparison for an object placed in degree zero is natural in that object. -/
@[reassoc]
lemma globalSectionsSingle₀HomologyIso_hom_naturality
    {A B : Sheaf C X} (f : A ⟶ B) :
    HomologicalComplex.homologyMap
        (((globalSectionsFunctor C X).mapHomologicalComplex (.up ℤ)).map
          ((CochainComplex.Plus.single₀ (Sheaf C X)).map f).hom) 0 ≫
        (globalSectionsSingle₀HomologyIso C X B).hom =
      (globalSectionsSingle₀HomologyIso C X A).hom ≫
        (globalSectionsFunctor C X).map f := by
  let Γ := globalSectionsFunctor C X
  let e := ComplexShape.embeddingUpNat
  let KA := (CochainComplex.single₀ (Sheaf C X)).obj A
  let KB := (CochainComplex.single₀ (Sheaf C X)).obj B
  let g : KA ⟶ KB := (CochainComplex.single₀ (Sheaf C X)).map f
  let EA := HomologicalComplex.mapExtendCanonicalIso Γ KA e ≪≫
    (e.extendFunctor C).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℕ) 0).app A) ≪≫
    HomologicalComplex.extendSingleIso e (Γ.obj A) 0 0 rfl
  let EB := HomologicalComplex.mapExtendCanonicalIso Γ KB e ≪≫
      (e.extendFunctor C).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℕ) 0).app B) ≪≫
      HomologicalComplex.extendSingleIso e (Γ.obj B) 0 0 rfl
  have hE :
      (Γ.mapHomologicalComplex (.up ℤ)).map
          ((CochainComplex.Plus.single₀ (Sheaf C X)).map f).hom ≫ EB.hom =
        EA.hom ≫
          (HomologicalComplex.single C (.up ℤ) 0).map (Γ.map f) := by
    change (Γ.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap g e) ≫ EB.hom =
      EA.hom ≫ (HomologicalComplex.single C (.up ℤ) 0).map (Γ.map f)
    dsimp only [EA, EB, Iso.trans_hom]
    have hM := (HomologicalComplex.mapExtendCanonicalNatIso Γ e).hom.naturality g
    dsimp only [Functor.comp_map, ComplexShape.Embedding.extendFunctor] at hM
    change (Γ.mapHomologicalComplex (.up ℤ)).map (HomologicalComplex.extendMap g e) ≫
        (HomologicalComplex.mapExtendCanonicalIso Γ KB e).hom =
      (HomologicalComplex.mapExtendCanonicalIso Γ KA e).hom ≫
        HomologicalComplex.extendMap ((Γ.mapHomologicalComplex (.up ℕ)).map g) e at hM
    rw [← Category.assoc, hM]
    simp only [Category.assoc]
    apply (cancel_epi (HomologicalComplex.mapExtendCanonicalIso Γ KA e).hom).2
    change HomologicalComplex.extendMap ((Γ.mapHomologicalComplex (.up ℕ)).map g) e ≫
        (e.extendFunctor C).map
          ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℕ) 0).hom.app B) ≫
        (HomologicalComplex.extendSingleIso e (Γ.obj B) 0 0 rfl).hom =
      (e.extendFunctor C).map
          ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℕ) 0).hom.app A) ≫
        (HomologicalComplex.extendSingleIso e (Γ.obj A) 0 0 rfl).hom ≫
        (HomologicalComplex.single C (.up ℤ) 0).map (Γ.map f)
    have hS := congrArg (fun k => (e.extendFunctor C).map k)
      ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℕ) 0).hom.naturality f)
    rw [Functor.map_comp, Functor.map_comp] at hS
    change HomologicalComplex.extendMap ((Γ.mapHomologicalComplex (.up ℕ)).map g) e ≫
        (e.extendFunctor C).map
          ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℕ) 0).hom.app B) =
      (e.extendFunctor C).map
          ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℕ) 0).hom.app A) ≫
        HomologicalComplex.extendMap
          ((HomologicalComplex.single C (.up ℕ) 0).map (Γ.map f)) e at hS
    rw [← Category.assoc, hS]
    simp only [Category.assoc]
    apply (cancel_epi ((e.extendFunctor C).map
      ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℕ) 0).hom.app A))).2
    have hSingle :=
      (HomologicalComplex.extendSingleNatIso e 0 0 rfl).hom.naturality (Γ.map f)
    change HomologicalComplex.extendMap
          ((HomologicalComplex.single C (.up ℕ) 0).map (Γ.map f)) e ≫
        (HomologicalComplex.extendSingleIso e (Γ.obj B) 0 0 rfl).hom =
      (HomologicalComplex.extendSingleIso e (Γ.obj A) 0 0 rfl).hom ≫
        (HomologicalComplex.single C (.up ℤ) 0).map (Γ.map f) at hSingle
    exact hSingle
  rw [show (globalSectionsSingle₀HomologyIso C X B).hom =
      HomologicalComplex.homologyMap EB.hom 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (Γ.obj B)).hom from rfl]
  rw [show (globalSectionsSingle₀HomologyIso C X A).hom =
      HomologicalComplex.homologyMap EA.hom 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (Γ.obj A)).hom from rfl]
  rw [← Category.assoc]
  have hH := congrArg (fun k => HomologicalComplex.homologyMap k 0) hE
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hH
  rw [hH]
  rw [Category.assoc, HomologicalComplex.singleObjHomologySelfIso_hom_naturality]
  rw [← Category.assoc]

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

/-- The canonical natural transformation from the cohomology of global sections to
hypercohomology.

This is the right-derived unit followed by degree-`n` cohomology. -/
def toHypercohomology (n : ℤ) :
    CochainComplex.Plus.ι (Sheaf C X) ⋙
        (globalSectionsFunctor C X).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor C (.up ℤ) n ⟶
      hypercohomologyFunctor C X n :=
  show CochainComplex.Plus.ι (Sheaf C X) ⋙
        (globalSectionsFunctor C X).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor C (.up ℤ) n ⟶
      DerivedCategory.Plus.Q ⋙ derivedGlobalSectionsFunctor C X ⋙
        DerivedCategory.Plus.homologyFunctor C n from
    (globalSectionsHomologyIso C X n).inv ≫
      Functor.whiskerRight
        (Functor.whiskerLeft (HomotopyCategory.Plus.quotient (Sheaf C X))
          (globalSectionsFunctor C X).rightDerivedFunctorPlusUnit)
        (DerivedCategory.Plus.homologyFunctor C n)

instance toHypercohomology_app_isIso (K : CochainComplex.Plus (Sheaf C X)) (n : ℤ)
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
    (hypercohomologyFunctor C X n).obj K ≅
      (((globalSectionsFunctor C X).mapHomologicalComplex (.up ℤ)).obj K.obj).homology n :=
  (asIso ((toHypercohomology C X n).app K)).symm

/-- A quasi-isomorphism to a termwise-injective bounded-below complex computes
hypercohomology by the complex of global sections of its target. -/
def hypercohomologyIsoOfQuasiIsoToInjective
    {K I : CochainComplex.Plus (Sheaf C X)} (f : K ⟶ I)
    [QuasiIso f.hom] [∀ i, Injective (I.obj.X i)] (n : ℤ) :
    (hypercohomologyFunctor C X n).obj K ≅
      (((globalSectionsFunctor C X).mapHomologicalComplex (.up ℤ)).obj I.obj).homology n :=
  asIso ((hypercohomologyFunctor C X n).map f) ≪≫
    hypercohomologyIsoOfInjective C X I n

/-- The comparison associated to an injective resolution carries the derived unit to the map
on the cohomology of complexes of global sections. -/
@[reassoc]
lemma toHypercohomology_hypercohomologyIsoOfQuasiIsoToInjective_hom
    {K I : CochainComplex.Plus (Sheaf C X)} (f : K ⟶ I)
    [QuasiIso f.hom] [∀ i, Injective (I.obj.X i)] (n : ℤ) :
    (toHypercohomology C X n).app K ≫
        (hypercohomologyIsoOfQuasiIsoToInjective C X f n).hom =
      (CochainComplex.Plus.ι (Sheaf C X) ⋙
        (globalSectionsFunctor C X).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor C (.up ℤ) n).map f := by
  change (toHypercohomology C X n).app K ≫
      (hypercohomologyFunctor C X n).map f ≫
      inv ((toHypercohomology C X n).app I) = _
  rw [← Category.assoc, ← (toHypercohomology C X n).naturality f,
    Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The injective-complex computation of hypercohomology is natural in maps between
termwise-injective bounded-below complexes. -/
@[reassoc]
lemma hypercohomologyIsoOfInjective_hom_naturality
    {K L : CochainComplex.Plus (Sheaf C X)}
    [∀ i, Injective (K.obj.X i)] [∀ i, Injective (L.obj.X i)]
    (f : K ⟶ L) (n : ℤ) :
    (hypercohomologyFunctor C X n).map f ≫
        (hypercohomologyIsoOfInjective C X L n).hom =
      (hypercohomologyIsoOfInjective C X K n).hom ≫
        (CochainComplex.Plus.ι (Sheaf C X) ⋙
          (globalSectionsFunctor C X).mapHomologicalComplex (.up ℤ) ⋙
          HomologicalComplex.homologyFunctor C (.up ℤ) n).map f := by
  change (hypercohomologyFunctor C X n).map f ≫
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
  simp only [Category.id_comp]

end TopCat.Sheaf
