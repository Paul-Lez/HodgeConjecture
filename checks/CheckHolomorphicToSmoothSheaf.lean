import Other.AlgebraicGeometry.HolomorphicExponential
import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.Analysis.Calculus.ContDiff.Operations

open CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

noncomputable section

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ)

def smoothComplexFunctionSheaf [SmoothOfRelativeDimension d X.hom] :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
  smoothSheafAddCommGroup 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) (ComplexPoint X) ℂ

set_option backward.isDefEq.respectTransparency false in
lemma holomorphicFunctionSheaf_section_smooth [SmoothOfRelativeDimension d X.hom]
    {U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ}
    (s : (holomorphicFunctionSheaf X d).presheaf.obj U) :
    ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) ∞ s.1 := by
  intro x
  rw [contMDiffAt_iff]
  have hs := (holomorphicFunctionSheaf_section_analytic X d s) x
  rw [contMDiffAt_iff] at hs
  refine ⟨hs.1, ?_⟩
  exact (hs.2.of_le le_top).restrict_scalars ℝ

def holomorphicToSmoothFunctionPresheaf [SmoothOfRelativeDimension d X.hom] :
    holomorphicAdditiveFunctionPresheaf X d ⟶
      (smoothComplexFunctionSheaf X d).presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun := fun f =>
        ⟨f.1, holomorphicFunctionSheaf_section_smooth X d f⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality {_ _} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    rfl

def holomorphicToSmoothFunctionSheaf [SmoothOfRelativeDimension d X.hom] :
    holomorphicAdditiveFunctionSheaf X d ⟶ smoothComplexFunctionSheaf X d :=
  ⟨holomorphicToSmoothFunctionPresheaf X d⟩

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

end

end AlgebraicGeometry.ComplexPoint
