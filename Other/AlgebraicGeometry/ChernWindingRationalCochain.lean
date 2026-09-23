/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingRational
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# An additive rational cochain representing winding

The integer winding cochain uses a pointwise branch of logarithm and need not be additive in
the unit. The complex winding cochain is additive. Composing the latter with a rational-linear
retraction `ℂ → ℚ` gives an additive rational cochain with the same periods. The retraction
need not be continuous: singular cochains impose no continuity on their values on simplices.

This construction also preserves the cochain identity for the exponential of a function. It
supplies the cochains for comparing the exponential sequence with rational singular cohomology.
The periods are independent of the chosen retraction, as proved below.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Simplicial AlgebraicTopology.Singular

namespace ChernWinding

/-- A rational-linear retraction of the inclusion of rational numbers into complex numbers. -/
def rationalProjection : ModuleCat.of ℚ ℂ ⟶ ModuleCat.of ℚ ℚ :=
  ModuleCat.ofHom (Algebra.linearMap ℚ ℂ).leftInverse

@[reassoc (attr := simp)]
theorem ratToComplex_comp_rationalProjection :
    ratToComplex ≫ rationalProjection = 𝟙 (ModuleCat.of ℚ ℚ) := by
  apply ModuleCat.hom_ext
  exact LinearMap.leftInverse_comp_of_inj
    (LinearMap.ker_eq_bot.mpr (Rat.cast_injective (α := ℂ)))

@[simp]
theorem rationalProjection_rat (q : ℚ) : rationalProjection (q : ℂ) = q :=
  congrArg (fun f : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ => f q)
    ratToComplex_comp_rationalProjection

variable {Y : TopCat.{0}} (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)

/-- The additive rational winding cochain. -/
def rationalWindingCochain : (singularChains Y).X 1 ⟶ ModuleCat.of ℚ ℚ :=
  windingCochain g hg ≫ rationalProjection

theorem d_comp_rationalWindingCochain :
    (singularChains Y).d 2 1 ≫ rationalWindingCochain g hg = 0 := by
  rw [rationalWindingCochain, ← Category.assoc, d_comp_windingCochain, zero_comp]

theorem rationalWindingCochain_mul (h k : C(Y, ℂ)) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    rationalWindingCochain k hk = rationalWindingCochain g hg + rationalWindingCochain h hh := by
  rw [rationalWindingCochain, windingCochain_mul g h k hg hh hk hmul,
    Preadditive.add_comp]
  rfl

/-- Every rational-linear retraction gives the same normalized winding periods. -/
theorem iCycles_comp_windingCochain_retraction
    (ρ : ModuleCat.of ℚ ℂ ⟶ ModuleCat.of ℚ ℚ) (hρ : ratToComplex ≫ ρ = 𝟙 _) :
    (singularChains Y).iCycles 1 ≫ windingCochain g hg ≫ ρ =
      (singularChains Y).homologyπ 1 ≫ windingRationalPeriodHom g hg := by
  rw [windingCochain_eq_coboundary_add_integer,
    Preadditive.add_comp, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
    HomologicalComplex.iCycles_d, zero_comp, zero_comp, zero_add,
    Category.assoc, hρ, Category.comp_id,
    homologyπ_comp_windingRationalPeriodHom]

/-- The projected cochain has exactly the normalized rational winding periods. -/
theorem iCycles_comp_rationalWindingCochain :
    (singularChains Y).iCycles 1 ≫ rationalWindingCochain g hg =
      (singularChains Y).homologyπ 1 ≫ windingRationalPeriodHom g hg :=
  iCycles_comp_windingCochain_retraction g hg rationalProjection ratToComplex_comp_rationalProjection

/-- Projecting a complex vertex cochain gives a rational vertex cochain. -/
def rationalVertexCochain (f : C(Y, ℂ)) : (singularChains Y).X 0 ⟶ ModuleCat.of ℚ ℚ :=
  vertexCochain f ≫ rationalProjection

/-- The exponential identity survives rational projection at the level of cochains. -/
theorem rationalWindingCochain_eq_d_comp_rationalVertexCochain (f : C(Y, ℂ))
    (hfg : ∀ y, Complex.exp (f y) = g y) :
    rationalWindingCochain g hg = (singularChains Y).d 1 0 ≫ rationalVertexCochain f := by
  rw [rationalWindingCochain, windingCochain_eq_d_comp_vertexCochain g f hg hfg,
    Category.assoc]
  rfl

/-- Evaluation of a complex-valued function as a rational zero-cochain. -/
def rationalFunctionCochain (f : Y → ℂ) : (singularChains Y).X 0 ⟶ ModuleCat.of ℚ ℚ :=
  vertexCochainFun (fun y => twoPiI * f y) ≫ rationalProjection

theorem scalarHom_comp_rationalProjection (z : ℂ) :
    scalarHom z ≫ rationalProjection = scalarHomRat (rationalProjection z) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  exact rationalProjection.hom.map_smul q z

@[reassoc]
theorem ιChainComplex_comp_rationalFunctionCochain (f : Y → ℂ)
    (v : (TopCat.toSSet.obj Y) _⦋0⦌) :
    (TopCat.toSSet.obj Y).ιChainComplex v ≫ rationalFunctionCochain f =
      scalarHomRat (rationalProjection (f (simplexMap v default))) := by
  rw [rationalFunctionCochain, ← Category.assoc, ιChainComplex_comp_vertexCochainFun,
    mul_div_cancel_left₀ _ twoPiI_ne_zero, scalarHom_comp_rationalProjection]

theorem rationalFunctionCochain_add (f h : Y → ℂ) :
    rationalFunctionCochain (fun y => f y + h y) =
      rationalFunctionCochain f + rationalFunctionCochain h := by
  refine SSet.chainComplex_hom_ext fun v => ?_
  rw [Preadditive.comp_add, ιChainComplex_comp_rationalFunctionCochain,
    ιChainComplex_comp_rationalFunctionCochain, ιChainComplex_comp_rationalFunctionCochain,
    map_add]
  ext
  simp [scalarHomRat, LinearMap.toSpanSingleton, mul_add]

theorem rationalFunctionCochain_zero :
    rationalFunctionCochain (Y := Y) (fun _ => 0) = 0 := by
  refine SSet.chainComplex_hom_ext fun v => ?_
  rw [ιChainComplex_comp_rationalFunctionCochain, comp_zero, map_zero]
  ext
  simp [scalarHomRat, LinearMap.toSpanSingleton]

/-- The normalized exponential has the differential of evaluation as its winding cochain. -/
theorem rationalWindingCochain_eq_d_comp_rationalFunctionCochain (f : C(Y, ℂ))
    (hfg : ∀ y, Complex.exp (twoPiI * f y) = g y) :
    rationalWindingCochain g hg = (singularChains Y).d 1 0 ≫ rationalFunctionCochain f :=
  rationalWindingCochain_eq_d_comp_rationalVertexCochain g hg
    ⟨fun y => twoPiI * f y, continuous_const.mul f.continuous⟩ hfg

set_option backward.isDefEq.respectTransparency false in
theorem rationalWindingCochain_one :
    rationalWindingCochain (1 : C(Y, ℂ)) (fun _ => one_ne_zero) = 0 := by
  rw [rationalWindingCochain_eq_d_comp_rationalFunctionCochain _ _ (0 : C(Y, ℂ))
    (by simp), show rationalFunctionCochain (0 : C(Y, ℂ)) = 0 from
      rationalFunctionCochain_zero, comp_zero]

variable {Y' : TopCat.{0}} (f : Y' ⟶ Y)

theorem chainComplexMap_comp_rationalWindingCochain
    (hgf : ∀ y, (g.comp (topMap f)) y ≠ 0) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f 1 ≫
        rationalWindingCochain g hg = rationalWindingCochain (g.comp (topMap f)) hgf := by
  rw [rationalWindingCochain, ← Category.assoc, chainComplexMap_comp_windingCochain g f hg hgf]
  rfl

/-- Evaluation cochains commute with arbitrary continuous pullbacks. -/
theorem chainComplexMap_comp_rationalFunctionCochain (h : Y → ℂ) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f 0 ≫
        rationalFunctionCochain h = rationalFunctionCochain (fun y => h (f y)) := by
  refine SSet.chainComplex_hom_ext fun v => ?_
  rw [← Category.assoc, SSet.ι_chainComplexMap_f,
    ιChainComplex_comp_rationalFunctionCochain, ιChainComplex_comp_rationalFunctionCochain]
  rfl

end ChernWinding
