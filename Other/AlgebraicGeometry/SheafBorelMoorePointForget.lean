/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SheafBorelMoorePointClass
public import Other.AlgebraicTopology.DerivedClosedSupportTruncationNaturality

/-!
# Forgetting support on the literal sheaf Borel--Moore point class

This file identifies support enlargement of the constructed point morphism with
the literal enlargement of its point-chain cocycle before passage to derived
sections.  It also isolates the exact augmentation statement which detects the
resulting whole-space class.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec (.of ℂ))) (d : ℕ)

noncomputable local instance sheafBorelMoorePointForgetAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

local instance sheafBorelMoorePointForgetSheafDerivedCategory :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) :=
  HasDerivedCategory.standard _

local instance sheafBorelMoorePointForgetGroupsDerivedCategory :
    HasDerivedCategory AddCommGrpCat := HasDerivedCategory.standard _

variable [SmoothOfRelativeDimension d X.hom] [T2Space (ComplexPoint X)]
  (x : ComplexPoint X)

local instance sheafBorelMoorePointForgetChainIsGE :
    (singularChainSheafCochainComplex ℚ
      (TopCat.of (ComplexPoint X))).IsGE (-((2 * d : ℕ) : ℤ)) :=
  complexChainSheaf_isGE X d

/-- Enlarge the literal singleton-supported point morphism to whole-space support. -/
def sheafBorelMoorePointTopMorphism :
    (DerivedCategory.Plus.singleFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℚ) ⟶
      complexAmbientSheafBorelMooreObject X d ⊤ :=
  sheafBorelMoorePointMorphism X d x ≫
    (TopCat.Sheaf.derivedClosedSupportSectionsMap
      (TopCat.of (ComplexPoint X))
      (show sheafBorelMoorePointSupport X x ≤ (⊤ : Closeds (ComplexPoint X)) from le_top)).app
        (complexChainSheafPlusObject X d)

/-- The whole-space point morphism is still exactly the literal point cocycle:
support enlargement occurs before the good-truncation comparison. -/
theorem sheafBorelMoorePointTopMorphism_underlying :
    DerivedCategory.Plus.ι.map (sheafBorelMoorePointTopMorphism X d x) =
      DerivedCategory.Q.map
          (pointSupportedChainCocycle ℚ (TopCat.of (ComplexPoint X)) x) ≫
        DerivedCategory.Q.map
          (((TopCat.Sheaf.closedSupportSectionsMap
            (TopCat.of (ComplexPoint X))
            (show sheafBorelMoorePointSupport X x ≤
              (⊤ : Closeds (ComplexPoint X)) from le_top)).mapHomologicalComplex
                (.up ℤ)).app
            (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X)))) ≫
        TopCat.Sheaf.termwiseToDerivedClosedSupport
          (TopCat.of (ComplexPoint X))
          (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X)))
          (-((2 * d : ℕ) : ℤ)) ⊤ := by
  let S := sheafBorelMoorePointSupport X x
  let K := singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X))
  let h : S ≤ (⊤ : Closeds (ComplexPoint X)) := le_top
  have hC : complexChainSheafPlusObject X d =
      TopCat.Sheaf.supportCoefficientPlus
        (TopCat.of (ComplexPoint X)) K (-((2 * d : ℕ) : ℤ)) := by
    apply ObjectProperty.FullSubcategory.ext
    rfl
  let m := (TopCat.Sheaf.derivedClosedSupportSectionsMap
    (TopCat.of (ComplexPoint X)) h).app (complexChainSheafPlusObject X d)
  have hm₀ := TopCat.Sheaf.termwiseToDerivedClosedSupport_naturality
    (TopCat.of (ComplexPoint X)) K (-((2 * d : ℕ) : ℤ)) h
  have hm :
      TopCat.Sheaf.termwiseToDerivedClosedSupport
          (TopCat.of (ComplexPoint X)) K (-((2 * d : ℕ) : ℤ)) S ≫
        DerivedCategory.Plus.ι.map m =
      DerivedCategory.Q.map
          (((TopCat.Sheaf.closedSupportSectionsMap
            (TopCat.of (ComplexPoint X)) h).mapHomologicalComplex (.up ℤ)).app K) ≫
        TopCat.Sheaf.termwiseToDerivedClosedSupport
          (TopCat.of (ComplexPoint X)) K (-((2 * d : ℕ) : ℤ)) ⊤ := by
    cases hC
    exact hm₀
  calc
    _ = DerivedCategory.Plus.ι.map (sheafBorelMoorePointMorphism X d x) ≫
          DerivedCategory.Plus.ι.map m := by
      unfold sheafBorelMoorePointTopMorphism m h S
      rw [Functor.map_comp]
    _ = (DerivedCategory.Q.map
          (pointSupportedChainCocycle ℚ (TopCat.of (ComplexPoint X)) x) ≫
        TopCat.Sheaf.termwiseToDerivedClosedSupport
          (TopCat.of (ComplexPoint X)) K (-((2 * d : ℕ) : ℤ)) S) ≫
          DerivedCategory.Plus.ι.map m := by
      rw [sheafBorelMoorePointMorphism_underlying]
    _ = DerivedCategory.Q.map
          (pointSupportedChainCocycle ℚ (TopCat.of (ComplexPoint X)) x) ≫
        (TopCat.Sheaf.termwiseToDerivedClosedSupport
          (TopCat.of (ComplexPoint X)) K (-((2 * d : ℕ) : ℤ)) S ≫
          DerivedCategory.Plus.ι.map m) := Category.assoc _ _ _
    _ = _ := by
      rw [hm]

/-- Homology of a degree-zero single object, stated directly for the bounded-below
derived-category functors used by Borel--Moore homology. -/
def plusSingleZeroHomologyIso :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat 0).obj
        ((DerivedCategory.Plus.singleFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℚ)) ≅
      AddCommGrpCat.of ℚ :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso AddCommGrpCat 0).app
    (AddCommGrpCat.of ℚ)

/-- The additive whole-space class map carried by the enlarged point morphism. -/
def sheafBorelMoorePointTopClassMap :
    AddCommGrpCat.of ℚ ⟶ ComplexAmbientSheafBorelMooreHomology X d ⊤ 0 :=
  (plusSingleZeroHomologyIso).inv ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat 0).map
        (sheafBorelMoorePointTopMorphism X d x)

/-- Support enlargement of the singleton class is evaluation of the enlarged
literal point morphism at the same coefficient `1`. -/
theorem complexAmbientSheafBorelMooreSupportMap_pointClass :
    complexAmbientSheafBorelMooreSupportMap X d
        (show sheafBorelMoorePointSupport X x ≤
          (⊤ : Closeds (ComplexPoint X)) from le_top) 0
        (sheafBorelMoorePointClass X d x) =
      sheafBorelMoorePointTopClassMap X d x 1 := by
  change ((sheafBorelMoorePointClassMap X d x ≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat 0).map
      ((TopCat.Sheaf.derivedClosedSupportSectionsMap
        (TopCat.of (ComplexPoint X)) le_top).app
          (complexChainSheafPlusObject X d))).hom 1) = _
  unfold sheafBorelMoorePointTopClassMap sheafBorelMoorePointClassMap
  rw [Category.assoc, ← Functor.map_comp]
  rfl

/-- A derived augmentation of the whole-space chain object detects the enlarged
point class as soon as it sends the literal point morphism back to the identity. -/
theorem complexAmbientSheafBorelMooreSupportMap_pointClass_ne_zero_of_retraction
    (augmentation : complexAmbientSheafBorelMooreObject X d ⊤ ⟶
      (DerivedCategory.Plus.singleFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℚ))
    (haugmentation : sheafBorelMoorePointTopMorphism X d x ≫ augmentation = 𝟙 _) :
    complexAmbientSheafBorelMooreSupportMap X d
        (show sheafBorelMoorePointSupport X x ≤
          (⊤ : Closeds (ComplexPoint X)) from le_top) 0
        (sheafBorelMoorePointClass X d x) ≠ 0 := by
  rw [complexAmbientSheafBorelMooreSupportMap_pointClass]
  intro hz
  have hmap : sheafBorelMoorePointTopClassMap X d x ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat 0).map augmentation ≫
      (plusSingleZeroHomologyIso).hom = 𝟙 _ := by
    unfold sheafBorelMoorePointTopClassMap
    change (plusSingleZeroHomologyIso).inv ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat 0).map
        (sheafBorelMoorePointTopMorphism X d x) ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat 0).map augmentation ≫
      (plusSingleZeroHomologyIso).hom = 𝟙 _
    rw [← Functor.map_comp_assoc, haugmentation]
    simp
  have hone := ConcreteCategory.congr_hom hmap (1 : ℚ)
  change (((DerivedCategory.Plus.homologyFunctor AddCommGrpCat 0).map augmentation ≫
      (plusSingleZeroHomologyIso).hom).hom
        ((sheafBorelMoorePointTopClassMap X d x).hom 1)) = 1 at hone
  rw [hz] at hone
  simpa using hone

end AlgebraicGeometry.ComplexPoint
