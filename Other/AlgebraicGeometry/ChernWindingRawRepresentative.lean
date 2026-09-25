/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.OpenRawCochainRepresentatives
public import Other.AlgebraicGeometry.ChernWindingSupportedBoundary

/-!
# Literal representatives of the normalized raw winding class

The existing raw winding cohomology class is represented by the actual rational
winding cochain, transported only by the prescribed integer-grading term iso.
The proof follows cycles and their homology classes through the original raw/dual
and coefficient-forgetting comparisons. No exponential class is assumed equal
to this class here.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace ChernWinding
variable {Y : TopCat.{0}} (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)
/-- The actual winding cocycle after extension from natural to integer degrees. -/
def rationalWindingIntCocycle :
    ((singularChains Y).linearDualCochainComplex.extend
      ComplexShape.embeddingUpNat).cycles (1 : ℤ) :=
  ((singularChains Y).linearDualCochainComplex.extendCyclesIso
    ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) rfl).inv
      (rationalWindingCocycle g hg)

lemma homologyπ_rationalWindingIntCocycle :
    ((singularChains Y).linearDualCochainComplex.extend ComplexShape.embeddingUpNat).homologyπ 1
      (rationalWindingIntCocycle g hg) = rationalWindingIntCohomologyClass g hg :=
  (ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_extendHomologyIso_inv
    (singularChains Y).linearDualCochainComplex ComplexShape.embeddingUpNat
    (j := 1) (j' := (1 : ℤ)) rfl) (rationalWindingCocycle g hg)).symm

lemma iCycles_rationalWindingIntCocycle :
    ((singularChains Y).linearDualCochainComplex.extend ComplexShape.embeddingUpNat).iCycles 1
      (rationalWindingIntCocycle g hg) =
    ((singularChains Y).linearDualCochainComplex.extendXIso
      ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) rfl).inv
      (rationalWindingCochain g hg).hom := by
  have h := ConcreteCategory.congr_hom (HomologicalComplex.extendCyclesIso_inv_iCycles
    (singularChains Y).linearDualCochainComplex ComplexShape.embeddingUpNat
    (j := 1) (j' := (1 : ℤ)) rfl) (rationalWindingCocycle g hg)
  exact h.trans (congrArg (((singularChains Y).linearDualCochainComplex.extendXIso
    ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) rfl).inv)
      (iCycles_rationalWindingCocycle g hg))
end ChernWinding

namespace ChernWinding
variable (X : TopCat.{0}) (V : Opens X) (g : C(TopCat.of V, ℂ)) (hg : ∀ y, g y ≠ 0)
/-- The integer raw winding cocycle through the actual coefficient-forgetting
and open-cochain identifications. -/
def openRawRationalWindingCocycle :
    ((openRawSingularCochainComplex ℚ X V).extend ComplexShape.embeddingUpNat).cycles (1 : ℤ) :=
  HomologicalComplex.cyclesMap (openRawSingularCochainComplexIntIsoDual ℚ X V).inv 1
    (((((singularChains (TopCat.of V)).linearDualCochainComplex.extend
      ComplexShape.embeddingUpNat).sc 1).mapCyclesIso
        (forget₂ (ModuleCat ℚ) AddCommGrpCat)).inv (rationalWindingIntCocycle g hg))

lemma homologyπ_openRawRationalWindingCocycle :
    ((openRawSingularCochainComplex ℚ X V).extend ComplexShape.embeddingUpNat).homologyπ 1
      (openRawRationalWindingCocycle X V g hg) = openRawRationalWindingClass X V g hg := by
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let K := (singularChains (TopCat.of V)).linearDualCochainComplex.extend ComplexShape.embeddingUpNat
  let e := openRawSingularCochainComplexIntIsoDual ℚ X V
  let eC := (K.sc 1).mapCyclesIso F
  let eH := (K.sc 1).mapHomologyIso F
  let b := eC.inv (rationalWindingIntCocycle g hg)
  have hn := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality e.inv 1) b
  have he (w) : HomologicalComplex.homologyMap e.hom 1
      (HomologicalComplex.homologyMap e.inv 1 w) = w :=
    (HomologicalComplex.homologyMapIso e 1).addCommGroupIsoToAddEquiv.apply_symm_apply w
  have hr := (congrArg (HomologicalComplex.homologyMap e.hom 1) hn.symm).trans (he _)
  have hπ := ConcreteCategory.congr_hom
    (ShortComplex.homologyπ_mapHomologyIso_hom (K.sc 1) F) b
  have hC : eC.hom b = rationalWindingIntCocycle g hg :=
    eC.addCommGroupIsoToAddEquiv.apply_symm_apply _
  have hπ' := hπ.trans ((congrArg (K.homologyπ 1) hC).trans
    (homologyπ_rationalWindingIntCocycle g hg))
  apply (openRawCochainHomologyEquivDual ℚ X V 1).injective
  have hR : openRawCochainHomologyEquivDual ℚ X V 1 (openRawRationalWindingClass X V g hg) =
      rationalWindingIntCohomologyClass g hg := AddEquiv.apply_symm_apply _ _
  exact ((congrArg eH.hom hr).trans hπ').trans hR.symm
end ChernWinding

namespace ChernWinding
open AlgebraicTopology.Singular
variable (X : TopCat.{0}) (V : Opens X) (g : C(TopCat.of V, ℂ)) (hg : ∀ y, g y ≠ 0)
/-- The representative of the normalized raw class is exactly the original
rational winding cochain, transported only by the grading term isomorphism. -/
lemma iCycles_openRawRationalWindingCocycle :
    ((openRawSingularCochainComplex ℚ X V).extend ComplexShape.embeddingUpNat).iCycles 1
      (openRawRationalWindingCocycle X V g hg) =
    ((openRawSingularCochainComplex ℚ X V).extendXIso ComplexShape.embeddingUpNat
      (i := 1) (i' := (1 : ℤ)) rfl).inv (rationalWindingCochain g hg).hom := by
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let K := (singularChains (TopCat.of V)).linearDualCochainComplex.extend ComplexShape.embeddingUpNat
  let e := openRawSingularCochainComplexIntIsoDual ℚ X V
  let eC := (K.sc 1).mapCyclesIso F
  let b := eC.inv (rationalWindingIntCocycle g hg)
  have hn := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i e.inv 1) b
  have hi := ConcreteCategory.congr_hom (ShortComplex.mapCyclesIso_hom_iCycles (K.sc 1) F) b
  have hC : eC.hom b = rationalWindingIntCocycle g hg :=
    eC.addCommGroupIsoToAddEquiv.apply_symm_apply _
  have hi' := hi.symm.trans ((congrArg (K.iCycles 1) hC).trans
    (iCycles_rationalWindingIntCocycle g hg))
  have hcoeff := ConcreteCategory.congr_hom
    (openRawSingularCochainComplexIntIsoDual_inv_f ℚ X V 1) (rationalWindingCochain g hg).hom
  exact hn.trans ((congrArg (e.inv.f 1) hi').trans hcoeff)
end ChernWinding
