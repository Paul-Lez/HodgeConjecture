module

public import Mathlib.LinearAlgebra.Dual.Defs

public section

/-- The dual of the zero map is zero. -/
@[simp]
theorem LinearMap.dualMap_zero {R M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] : (0 : M₁ →ₗ[R] M₂).dualMap = 0 := by
  rw [LinearMap.dualMap_def, map_zero]

/-- The dual of a difference of maps is the difference of the duals. -/
theorem LinearMap.dualMap_add {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (f g : M₁ →ₗ[R] M₂) :
    (f + g).dualMap = f.dualMap + g.dualMap := by
  rw [LinearMap.dualMap_def, LinearMap.dualMap_def, LinearMap.dualMap_def, map_add]

/-- The dual of a difference of maps is the difference of the duals. -/
theorem LinearMap.dualMap_sub {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (f g : M₁ →ₗ[R] M₂) :
    (f - g).dualMap = f.dualMap - g.dualMap := by
  rw [LinearMap.dualMap_def, LinearMap.dualMap_def, LinearMap.dualMap_def, map_sub]

/-- The dual of a split injection is surjective: a functional on the source is extended by
precomposing with a retraction.

Over a field every injection splits, which is `LinearMap.dualMap_surjective_of_injective`; over a
general ring the splitting has to be supplied. -/
theorem LinearMap.dualMap_surjective_of_comp_eq_id {R M₁ M₂ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
    {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₁} (h : g.comp f = LinearMap.id) :
    Function.Surjective f.dualMap :=
  fun φ => ⟨φ.comp g, LinearMap.ext fun x => congrArg φ (LinearMap.congr_fun h x)⟩
