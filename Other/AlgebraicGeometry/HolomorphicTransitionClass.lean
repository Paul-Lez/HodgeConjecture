/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticSheafSections
public import Other.AlgebraicGeometry.SheafExtHypercohomology
public import Other.AlgebraicGeometry.ExponentialClassHodge
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# Classes of actual holomorphic transition functions

A holomorphic unit on the intersection of a two-open cover determines a sheaf cohomology
class by the actual Mayer-Vietoris extension. Its exponential class has rational de Rham
image in the first Hodge filtration. The transition function is explicit input; no
cohomology class or filtered lift is supplied as an assumption.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 5000

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

local instance transitionSheafAbelian : Abelian (AnalyticAdditiveSheaf X) := CategoryTheory.sheafIsAbelian

local instance transitionHasExt : HasExt.{1} (AnalyticAdditiveSheaf X) := analyticHasExt X

/-- A two-open analytic cover, with the whole variety as the last vertex. -/
def analyticCoverMayerVietorisSquare (U V : Opens (TopCat.of (ComplexPoint X)))
    (hcover : U ⊔ V = ⊤) :
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := U ⊓ V
      X₂ := U
      X₃ := V
      X₄ := ⊤
      f₁₂ := homOfLE inf_le_left
      f₁₃ := homOfLE inf_le_right
      f₂₄ := homOfLE le_top
      f₃₄ := homOfLE le_top
      fac := Subsingleton.elim _ _ } hcover.symm rfl

/-- The actual Mayer-Vietoris class of a section on the overlap of a two-open cover. -/
def analyticTransitionExtClass (F : AnalyticAdditiveSheaf X)
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (a : F.obj.obj (.op (U ⊓ V))) : Abelian.Ext.{1} (constantIntegerSheaf X) F 1 :=
  let δ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X ⊤)
      (analyticOpenFreeAbelianSheaf X (U ⊓ V)) 1 :=
    (analyticCoverMayerVietorisSquare X U V hcover).shortComplex_shortExact.extClass
      (C := AnalyticAdditiveSheaf X)
  let a₀ : Abelian.Ext.{1} (constantIntegerSheaf X) (analyticOpenFreeAbelianSheaf X ⊤) 0 :=
    Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso X).inv
  let a₁ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X (U ⊓ V)) F 0 :=
    Abelian.Ext.mk₀ (analyticSectionSheafHom X F (U ⊓ V) a)
  a₀.comp (δ.comp a₁ (show 1 + 0 = 1 from rfl)) (show 0 + 1 = 1 from rfl)

@[simp]
theorem analyticTransitionExtClass_zero (F : AnalyticAdditiveSheaf X)
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤) :
    analyticTransitionExtClass X F U V hcover 0 = 0 := by
  simp [analyticTransitionExtClass]

variable [IsIntegral X.left] [Smooth X.hom]

/-- The units cohomology class defined by an actual holomorphic transition function. -/
def holomorphicTransitionUnitsClass
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (u : (OpenHolomorphicFunctions X (dim X.left) (.op (U ⊓ V)))ˣ) :
    Hypercohomology X (holomorphicUnitsComplexInt X) 2 :=
  sheafExtHypercohomologyEquiv X (holomorphicUnitsSheaf X (dim X.left)) 1 1
    (analyticTransitionExtClass X (holomorphicUnitsSheaf X (dim X.left)) U V hcover (Additive.ofMul u))

@[simp]
theorem holomorphicTransitionUnitsClass_one
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤) :
    holomorphicTransitionUnitsClass X U V hcover 1 = 0 := by
  change sheafExtHypercohomologyEquiv X (holomorphicUnitsSheaf X (dim X.left)) 1 1
    (analyticTransitionExtClass X (holomorphicUnitsSheaf X (dim X.left)) U V hcover 0) = 0
  rw [analyticTransitionExtClass_zero, sheafExtHypercohomologyEquiv_zero]

/-- The integral exponential class of the actual transition function. -/
def integralHolomorphicTransitionClass
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (u : (OpenHolomorphicFunctions X (dim X.left) (.op (U ⊓ V)))ˣ) :
    Hypercohomology X (constantIntegerSheafComplexInt X) 2 :=
  integralExponentialClass X 2 (holomorphicTransitionUnitsClass X U V hcover u)

/-- The rational class constructed from the actual transition function. -/
def rationalHolomorphicTransitionClass
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (u : (OpenHolomorphicFunctions X (dim X.left) (.op (U ⊓ V)))ˣ) : FieldCohomology ℚ X 2 :=
  rationalExponentialClass X 2 (holomorphicTransitionUnitsClass X U V hcover u)

/-- The trivial transition function gives the zero rational class. -/
@[simp]
theorem rationalHolomorphicTransitionClass_one
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤) :
    rationalHolomorphicTransitionClass X U V hcover 1 = 0 := by
  simp [rationalHolomorphicTransitionClass]

/-- The class constructed from a holomorphic transition function on an actual analytic open
cover is a Hodge class of the underlying variety. -/
theorem rationalHolomorphicTransitionClass_isHodge
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (u : (OpenHolomorphicFunctions X (dim X.left) (.op (U ⊓ V)))ˣ) :
    IsHodgeClass ℚ X 1 (rationalHolomorphicTransitionClass X U V hcover u) :=
  rationalExponentialClass_isHodge X _

end AlgebraicGeometry.ComplexPoint
