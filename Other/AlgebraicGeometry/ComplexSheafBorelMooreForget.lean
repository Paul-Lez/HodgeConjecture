/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ComplexSheafBorelMoore
public import Other.AlgebraicTopology.DerivedSheafSupportForget

/-!
# From ambient Borel–Moore classes to actual derived ordinary cohomology

The map is the constructed complex-orientation duality followed by the actual
derived support-forgetting map. We prove that forgetting Borel–Moore support first
gives exactly the same result. All targets here use actual derived global sections;
comparison with the repository's separate `FieldCohomology` presentation remains
a further theorem. In particular, no cycle-component fundamental class is supplied
or constructed by the transport map alone.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ)) (d : ℕ)

local instance complexSheafForgetAnalyticTopology :
    TopologicalSpace (ComplexPoint X structureMap) := Point.analyticTopology

local instance complexSheafForgetSheafDerivedCategory : HasDerivedCategory
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap))) :=
  HasDerivedCategory.standard _

local instance complexSheafForgetGroupDerivedCategory : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

/-- Ordinary rational sheaf cohomology in the actual derived-global-sections model. -/
def ComplexDerivedCohomology (n : ℤ) : AddCommGrpCat :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
    ((TopCat.Sheaf.derivedGlobalSections (TopCat.of (ComplexPoint X structureMap))).obj
      (complexConstantRationalSheafPlusObject structureMap))

/-- The actual derived inclusion of supported cohomology into ordinary cohomology. -/
def complexDerivedSupportedCohomologyForgetSupport
    (Z : Closeds (ComplexPoint X structureMap)) (n : ℤ) :
    ComplexDerivedSupportedCohomology structureMap Z n ⟶
      ComplexDerivedCohomology structureMap n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedForgetClosedSupport
      (TopCat.of (ComplexPoint X structureMap)) Z).app
        (complexConstantRationalSheafPlusObject structureMap))

/-- Whole-space support is canonically ordinary cohomology through support forgetting. -/
def complexDerivedSupportedCohomologyTopIso (n : ℤ) :
    ComplexDerivedSupportedCohomology structureMap ⊤ n ≅
      ComplexDerivedCohomology structureMap n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).mapIso
    ((TopCat.Sheaf.derivedClosedSupportSectionsTopIso
      (TopCat.of (ComplexPoint X structureMap))).app
        (complexConstantRationalSheafPlusObject structureMap))

@[simp]
theorem complexDerivedSupportedCohomologyTopIso_hom (n : ℤ) :
    (complexDerivedSupportedCohomologyTopIso structureMap n).hom =
      complexDerivedSupportedCohomologyForgetSupport structureMap ⊤ n := rfl

/-- Support enlargement and forgetting support induce the same ordinary class. -/
@[reassoc (attr := simp)]
theorem complexDerivedSupportedCohomologySupportMap_forget
    {Z W : Closeds (ComplexPoint X structureMap)} (h : Z ≤ W) (n : ℤ) :
    complexDerivedSupportedCohomologySupportMap structureMap h n ≫
        complexDerivedSupportedCohomologyForgetSupport structureMap W n =
      complexDerivedSupportedCohomologyForgetSupport structureMap Z n := by
  unfold complexDerivedSupportedCohomologySupportMap complexDerivedSupportedCohomologyForgetSupport
  rw [← Functor.map_comp]
  congr 1
  exact NatTrans.congr_app (TopCat.Sheaf.derivedClosedSupportSectionsMap_forget
    (TopCat.of (ComplexPoint X structureMap)) h) _

variable [SmoothOfRelativeDimension d structureMap] [T2Space (ComplexPoint X structureMap)]

/-- Transport an actual ambient Borel–Moore class to ordinary derived cohomology,
using the constructed complex orientation and the actual support inclusion. -/
def complexAmbientSheafBorelMooreToCohomology
    (Z : Closeds (ComplexPoint X structureMap)) (i : ℤ) :
    ComplexAmbientSheafBorelMooreHomology structureMap d Z i ⟶
      ComplexDerivedCohomology structureMap (2 * (d : ℤ) - i) :=
  (complexAmbientSheafBorelMooreHomologyIso structureMap d Z i).hom ≫
    complexDerivedSupportedCohomologyForgetSupport structureMap Z (2 * (d : ℤ) - i)

/-- Enlarging Borel–Moore support does not change the resulting ordinary cohomology class. -/
@[reassoc (attr := simp)]
theorem complexAmbientSheafBorelMooreToCohomology_naturality
    {Z W : Closeds (ComplexPoint X structureMap)} (h : Z ≤ W) (i : ℤ) :
    complexAmbientSheafBorelMooreSupportMap structureMap d h i ≫
        complexAmbientSheafBorelMooreToCohomology structureMap d W i =
      complexAmbientSheafBorelMooreToCohomology structureMap d Z i := by
  unfold complexAmbientSheafBorelMooreToCohomology
  rw [complexAmbientSheafBorelMooreHomologyIso_naturality_assoc,
    complexDerivedSupportedCohomologySupportMap_forget]

/-- Forgetting Borel–Moore support first, then applying whole-space duality, is exactly
the supported-duality construction. No independent whole-space comparison is chosen. -/
theorem complexAmbientSheafBorelMooreToCohomology_eq_forgetSupport
    (Z : Closeds (ComplexPoint X structureMap)) (i : ℤ) :
    complexAmbientSheafBorelMooreToCohomology structureMap d Z i =
      complexAmbientSheafBorelMooreForgetSupport structureMap d Z i ≫
        (complexAmbientSheafBorelMooreHomologyIso structureMap d ⊤ i).hom ≫
        (complexDerivedSupportedCohomologyTopIso structureMap (2 * (d : ℤ) - i)).hom :=
  (complexAmbientSheafBorelMooreToCohomology_naturality structureMap d le_top i).symm

/-- The cycle-degree transport, with the dimension arithmetic already proved in duality. -/
def complexAmbientSheafBorelMooreCycleDegreeToCohomology
    (Z : Closeds (ComplexPoint X structureMap)) (p : ℕ) (hp : p ≤ d) :
    ComplexAmbientSheafBorelMooreHomology structureMap d Z
        (2 * ((d - p : ℕ) : ℤ)) ⟶
      ComplexDerivedCohomology structureMap (2 * (p : ℤ)) :=
  (complexAmbientSheafBorelMooreCycleDegreeIso structureMap d Z p hp).hom ≫
    complexDerivedSupportedCohomologyForgetSupport structureMap Z (2 * (p : ℤ))

end AlgebraicGeometry.ComplexPoint
