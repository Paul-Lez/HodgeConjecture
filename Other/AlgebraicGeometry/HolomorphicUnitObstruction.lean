/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticTransitionCoboundary
public import Mathlib.Analysis.Complex.CoveringMap

/-!
# The actual cohomological obstruction to a holomorphic logarithm

A holomorphic unit on an analytic open determines a degree-one integral sheaf cohomology
class through the actual exponential extension. The class vanishes exactly when the unit
has a holomorphic logarithm on that open. This is the local exponential class used in the
comparison with normal divisor coclasses.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 5000

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ)

local instance unitObstructionSheafAbelian : Abelian (AnalyticAdditiveSheaf s) :=
  CategoryTheory.sheafIsAbelian

local instance unitObstructionHasExt : HasExt.{1} (AnalyticAdditiveSheaf s) := analyticHasExt s

variable (d : ℕ) [SmoothOfRelativeDimension d s]

/-- The actual integral cohomology class obstructing a logarithm of a holomorphic unit. -/
def holomorphicUnitLogarithmObstruction
    (U : Opens (TopCat.of (ComplexPoint X s)))
    (u : (OpenHolomorphicFunctions s d (.op U))ˣ) :
    Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf s U) (constantIntegerSheaf s) 1 :=
  let a : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf s U) (holomorphicUnitsSheaf s d) 0 :=
    Abelian.Ext.mk₀ (analyticSectionSheafHom s (holomorphicUnitsSheaf s d) U (Additive.ofMul u))
  let δ : Abelian.Ext.{1} (holomorphicUnitsSheaf s d) (constantIntegerSheaf s) 1 :=
    (holomorphicExponentialSequence_shortExact s d).extClass (C := AnalyticAdditiveSheaf s)
  a.comp δ (show 0 + 1 = 1 from rfl)

/-- The local exponential class is zero exactly when an actual logarithm exists. -/
theorem holomorphicUnitLogarithmObstruction_eq_zero_iff
    (U : Opens (TopCat.of (ComplexPoint X s)))
    (u : (OpenHolomorphicFunctions s d (.op U))ˣ) :
    holomorphicUnitLogarithmObstruction s d U u = 0 ↔
      ∃ f : OpenHolomorphicFunctions s d (.op U), holomorphicExpUnit s d (.op U) f = u := by
  let T : ShortComplex (AnalyticAdditiveSheaf s) := holomorphicExponentialSequence s d
  have hT : T.ShortExact := holomorphicExponentialSequence_shortExact s d
  let a : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf s U) (holomorphicUnitsSheaf s d) 0 :=
    Abelian.Ext.mk₀ (analyticSectionSheafHom s (holomorphicUnitsSheaf s d) U (Additive.ofMul u))
  constructor
  · intro hu
    obtain ⟨a₂, ha₂⟩ := Abelian.Ext.covariant_sequence_exact₃ (analyticOpenFreeAbelianSheaf s U)
      hT a (show 0 + 1 = 1 from rfl) hu
    obtain ⟨η, rfl⟩ := (Abelian.Ext.mk₀_bijective (C := AnalyticAdditiveSheaf s)
      (analyticOpenFreeAbelianSheaf s U) T.X₂).surjective a₂
    obtain ⟨f, hf⟩ := (analyticSectionSheafHomEquiv s (holomorphicAdditiveFunctionSheaf s d) U).surjective η
    have hη : η ≫ T.g = analyticSectionSheafHom s (holomorphicUnitsSheaf s d) U (Additive.ofMul u) := by
      apply (Abelian.Ext.mk₀_bijective (C := AnalyticAdditiveSheaf s)
        (analyticOpenFreeAbelianSheaf s U) T.X₃).injective
      simpa only [Abelian.Ext.mk₀_comp_mk₀] using ha₂
    refine ⟨f, ?_⟩
    have hsec : analyticSectionSheafHom s (holomorphicUnitsSheaf s d) U
        (Additive.ofMul (holomorphicExpUnit s d (.op U) f)) =
          analyticSectionSheafHom s (holomorphicUnitsSheaf s d) U (Additive.ofMul u) :=
      (analyticSectionSheafHom_postcomp s (holomorphicAdditiveFunctionSheaf s d)
        (holomorphicUnitsSheaf s d) (holomorphicExpSheaf s d) U f).symm.trans
          ((congrArg (fun z : analyticOpenFreeAbelianSheaf s U ⟶ T.X₂ => z ≫ T.g) hf).trans hη)
    exact (analyticSectionSheafHomEquiv s (holomorphicUnitsSheaf s d) U).injective hsec
  · rintro ⟨f, rfl⟩
    let b : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf s U)
        (holomorphicAdditiveFunctionSheaf s d) 0 :=
      Abelian.Ext.mk₀ (analyticSectionSheafHom s (holomorphicAdditiveFunctionSheaf s d) U f)
    let δ : Abelian.Ext.{1} (holomorphicUnitsSheaf s d) (constantIntegerSheaf s) 1 := hT.extClass
    change (Abelian.Ext.mk₀ (analyticSectionSheafHom s (holomorphicUnitsSheaf s d) U
      (Additive.ofMul (holomorphicExpUnit s d (.op U) f)))).comp δ
        (show 0 + 1 = 1 from rfl) = 0
    have hf : analyticSectionSheafHom s (holomorphicAdditiveFunctionSheaf s d) U f ≫
        holomorphicExpSheaf s d = analyticSectionSheafHom s (holomorphicUnitsSheaf s d) U
          (Additive.ofMul (holomorphicExpUnit s d (.op U) f)) :=
      analyticSectionSheafHom_postcomp s (holomorphicAdditiveFunctionSheaf s d)
        (holomorphicUnitsSheaf s d) (holomorphicExpSheaf s d) U f
    rw [← hf, ← Abelian.Ext.mk₀_comp_mk₀]
    let e : Abelian.Ext.{1} (holomorphicAdditiveFunctionSheaf s d) (holomorphicUnitsSheaf s d) 0 :=
      Abelian.Ext.mk₀ (holomorphicExpSheaf s d)
    change (b.comp e (show 0 + 0 = 0 from rfl)).comp δ
      (show 0 + 1 = 1 from rfl) = 0
    have hz : e.comp δ (show 0 + 1 = 1 from rfl) = 0 := hT.comp_extClass
    rw [Abelian.Ext.comp_assoc b e δ (show 0 + 0 = 0 from rfl)
      (show 0 + 1 = 1 from rfl) (show 0 + 0 + 1 = 1 from rfl), hz, Abelian.Ext.comp_zero]

/-- A unit with no holomorphic logarithm gives a nonzero actual integral cohomology class. -/
theorem holomorphicUnitLogarithmObstruction_ne_zero
    (U : Opens (TopCat.of (ComplexPoint X s)))
    (u : (OpenHolomorphicFunctions s d (.op U))ˣ)
    (hu : ¬ ∃ f : OpenHolomorphicFunctions s d (.op U), holomorphicExpUnit s d (.op U) f = u) :
    holomorphicUnitLogarithmObstruction s d U u ≠ 0 :=
  mt (holomorphicUnitLogarithmObstruction_eq_zero_iff s d U u).1 hu

/-- One positive turn of the value of a unit along an actual analytic loop obstructs a
holomorphic logarithm. The normalization is exactly the exponential period `2πi`. -/
theorem holomorphicUnitLogarithmObstruction_ne_zero_of_loop
    (U : Opens (TopCat.of (ComplexPoint X s)))
    (u : (OpenHolomorphicFunctions s d (.op U))ˣ)
    (γ : ℝ → U) (hγ : Continuous γ) (hclose : γ 1 = γ 0)
    (hturn : ∀ t : ℝ, u.val.1 (γ t) = u.val.1 (γ 0) *
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ))) :
    holomorphicUnitLogarithmObstruction s d U u ≠ 0 := by
  apply holomorphicUnitLogarithmObstruction_ne_zero
  rintro ⟨f, hf⟩
  have hexp (x : U) : Complex.exp (f.1 x) = u.val.1 x :=
    congrArg (fun v : (OpenHolomorphicFunctions s d (.op U))ˣ => v.val.1 x) hf
  let g₁ : ℝ → ℂ := fun t => f.1 (γ t)
  let g₂ : ℝ → ℂ := fun t => f.1 (γ 0) + (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)
  have hg₁ : Continuous g₁ := (holomorphicFunctionSheaf_section_analytic s d f).continuous.comp hγ
  have hg₂ : Continuous g₂ := by unfold g₂; fun_prop
  have he : (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ g₁ =
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ g₂ := by
    funext t
    apply Subtype.ext
    change Complex.exp (f.1 (γ t)) =
      Complex.exp (f.1 (γ 0) + (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ))
    rw [Complex.exp_add, hexp, hexp, hturn]
  have heq := Complex.isCoveringMap_exp.eq_of_comp_eq hg₁ hg₂ he 0 (by simp [g₁, g₂])
  have hone := congrFun heq 1
  simp only [g₁, g₂, hclose, Complex.ofReal_one, mul_one] at hone
  exact Complex.two_pi_I_ne_zero (add_left_cancel (show
    f.1 (γ 0) + (2 * (Real.pi : ℂ) * Complex.I) = f.1 (γ 0) + 0 by simpa using hone.symm))

end AlgebraicGeometry.ComplexPoint
