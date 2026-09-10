/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicExponential
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Local holomorphic logarithms

Every holomorphic unit has a holomorphic logarithm on a neighborhood of each point. The branch
is constructed by dividing by the value at the point, taking the principal logarithm near one,
and adding a logarithm of that value. Consequently the actual exponential morphism of sheaves
is locally surjective.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ) (d : ℕ) [SmoothOfRelativeDimension d s]

/-- The value of a holomorphic unit is nonzero at every point. -/
theorem holomorphicUnit_apply_ne_zero
    (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ)
    (u : (OpenHolomorphicFunctions s d U)ˣ)
    (x : (Opposite.unop U : Opens (ComplexPoint X s))) :
    (u.val).1 x ≠ 0 := by
  have h := congrArg (fun f : OpenHolomorphicFunctions s d U => f.1 x) u.val_inv
  exact left_ne_zero_of_mul_eq_one h

/-- The principal logarithm of a holomorphic function with values in the slit plane. -/
def holomorphicLog (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ)
    (f : OpenHolomorphicFunctions s d U)
    (hf : ∀ x, f.1 x ∈ Complex.slitPlane) : OpenHolomorphicFunctions s d U := by
  change C^ω⟮𝓘(ℂ, Fin d → ℂ), (Opposite.unop U : Opens (ComplexPoint X s)); ℂ⟯
  refine ⟨fun x => Complex.log (f.1 x), fun x => ?_⟩
  exact (Complex.contDiffAt_log (hf x)).contMDiffAt.comp x
    (holomorphicFunctionSheaf_section_analytic s d f).contMDiffAt

@[simp]
theorem holomorphicExp_log (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ)
    (f : OpenHolomorphicFunctions s d U) (hf : ∀ x, f.1 x ∈ Complex.slitPlane) :
    holomorphicExp s d U (holomorphicLog s d U f hf) = f := by
  apply ContMDiffMap.ext
  intro x
  exact Complex.exp_log (Complex.slitPlane_ne_zero (hf x))

/-- A holomorphic unit admits an actual logarithm after restriction around any chosen point. -/
theorem exists_holomorphicLog_neighborhood
    (U : Opens (TopCat.of (ComplexPoint X s)))
    (u : (OpenHolomorphicFunctions s d (Opposite.op U))ˣ) (x : U) :
    ∃ (V : Opens (TopCat.of (ComplexPoint X s))) (hVU : V ≤ U),
      x.1 ∈ V ∧ ∃ f : OpenHolomorphicFunctions s d (Opposite.op V),
        holomorphicExpUnit s d (Opposite.op V) f =
          Units.map (holomorphicRestrictionAlgHom s d (homOfLE hVU).op).toMonoidHom u := by
  let c : ℂ := u.val.1 x
  have hc : c ≠ 0 := holomorphicUnit_apply_ne_zero s d (Opposite.op U) u x
  let W : Set U := (fun y => c⁻¹ * u.val.1 y) ⁻¹' Complex.slitPlane
  have hW : IsOpen W := Complex.isOpen_slitPlane.preimage
    ((holomorphicFunctionSheaf_section_analytic s d u.val).continuous.const_mul c⁻¹)
  let V : Opens (TopCat.of (ComplexPoint X s)) :=
    ⟨Subtype.val '' W, U.isOpen.isOpenMap_subtype_val W hW⟩
  have hVU : V ≤ U := by
    rintro y ⟨z, hz, rfl⟩
    exact z.2
  have hxV : x.1 ∈ V := by
    refine ⟨x, ?_, rfl⟩
    change c⁻¹ * c ∈ Complex.slitPlane
    rw [inv_mul_cancel₀ hc]
    exact Complex.one_mem_slitPlane
  let g := holomorphicRestrictionAlgHom s d (homOfLE hVU).op u.val
  let r : OpenHolomorphicFunctions s d (Opposite.op V) := c⁻¹ • g
  have hr : ∀ y, r.1 y ∈ Complex.slitPlane := by
    intro y
    rcases y.2 with ⟨z, hz, heq⟩
    have hyz : (⟨y.1, hVU y.2⟩ : U) = z := Subtype.ext heq.symm
    change c⁻¹ * u.val.1 ⟨y.1, hVU y.2⟩ ∈ Complex.slitPlane
    rw [hyz]
    exact hz
  refine ⟨V, hVU, hxV,
    algebraMap ℂ _ (Complex.log c) + holomorphicLog s d (Opposite.op V) r hr, ?_⟩
  apply Units.ext
  change holomorphicExp s d (Opposite.op V) _ = g
  rw [holomorphicExp_add, holomorphicExp_log]
  apply ContMDiffMap.ext
  intro y
  change Complex.exp (Complex.log c) * (c⁻¹ * g.1 y) = g.1 y
  rw [Complex.exp_log hc, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- The actual exponential morphism is locally surjective on the analytic site. -/
instance holomorphicExpPresheaf_isLocallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s)))
      (holomorphicExpPresheaf s d) where
  imageSieve_mem {U} u := by
    intro x hx
    obtain ⟨V, hVU, hxV, f, hf⟩ :=
      exists_holomorphicLog_neighborhood s d U u.toMul ⟨x, hx⟩
    exact ⟨V, homOfLE hVU, ⟨f, hf⟩, hxV⟩

instance holomorphicExpSheaf_isLocallySurjective :
    CategoryTheory.Sheaf.IsLocallySurjective (holomorphicExpSheaf s d) :=
  holomorphicExpPresheaf_isLocallySurjective s d

/-- The exponential is an epimorphism of actual holomorphic sheaves. -/
instance holomorphicExpSheaf_epi : Epi (holomorphicExpSheaf s d) :=
  CategoryTheory.Sheaf.epi_of_isLocallySurjective _

end AlgebraicGeometry.ComplexPoint
