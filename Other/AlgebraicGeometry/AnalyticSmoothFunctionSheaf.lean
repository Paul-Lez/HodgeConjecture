/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicExponential
public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The smooth-function sheaf underlying a complex analytic variety

This file views the complex analytic atlas on the complex points of a smooth scheme over `ℂ`
over the restricted scalar field `ℝ`.  It packages real-smooth complex-valued functions as an
actual sheaf of additive groups and constructs the inclusion of holomorphic functions into it.

The construction is the degree-zero sheaf needed by a future Dolbeault resolution.  It is separate
from the global `SmoothCFunctions` space used by Kirov's curve-specific Dolbeault development.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ)

set_option backward.isDefEq.respectTransparency false

/-- Real-smooth complex-valued functions on the complex analytic atlas, as an additive sheaf. -/
def smoothComplexFunctionSheaf [SmoothOfRelativeDimension d X.hom] :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
  smoothSheafAddCommGroup 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) (ComplexPoint X) ℂ

/-- A holomorphic section is smooth after restricting scalars from `ℂ` to `ℝ`. -/
theorem holomorphicFunctionSheaf_section_realSmooth
    [SmoothOfRelativeDimension d X.hom]
    {U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ}
    (s : (holomorphicFunctionSheaf X d).presheaf.obj U) :
    ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) ∞ s.1 := by
  intro x
  rw [contMDiffAt_iff]
  have hs := (holomorphicFunctionSheaf_section_analytic X d s) x
  rw [contMDiffAt_iff] at hs
  refine ⟨hs.1, ?_⟩
  exact (hs.2.of_le le_top).restrict_scalars ℝ

/-- Inclusion of the additive presheaf of holomorphic functions into real-smooth functions. -/
def holomorphicToSmoothFunctionPresheaf [SmoothOfRelativeDimension d X.hom] :
    holomorphicAdditiveFunctionPresheaf X d ⟶
      (smoothComplexFunctionSheaf X d).presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun := fun f =>
        ⟨f.1, holomorphicFunctionSheaf_section_realSmooth X d f⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality {_ _} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    rfl

/-- Inclusion of holomorphic functions into the sheaf of real-smooth complex functions. -/
def holomorphicToSmoothFunctionSheaf [SmoothOfRelativeDimension d X.hom] :
    holomorphicAdditiveFunctionSheaf X d ⟶ smoothComplexFunctionSheaf X d :=
  ⟨holomorphicToSmoothFunctionPresheaf X d⟩

/-- The inclusion of holomorphic functions into smooth functions is a monomorphism of sheaves. -/
instance [SmoothOfRelativeDimension d X.hom] :
    Mono (holomorphicToSmoothFunctionSheaf X d) := by
  apply (TopCat.Sheaf.forget AddCommGrpCat (TopCat.of (ComplexPoint X))).mono_of_mono_map
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [AddCommGrpCat.mono_iff_injective]
  intro f g h
  apply Subtype.ext
  exact congrArg
    (fun q : (smoothComplexFunctionSheaf X d).presheaf.obj U => q.1) h

end AlgebraicGeometry.ComplexPoint
