import Other.AlgebraicTopology.SingularCohomologyCoefficientNonvanishing
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicTopology
open scoped Simplicial TensorProduct

namespace AlgebraicTopology.Singular

local instance (X : TopCat) (n : ℕ) : Module ℚ ((CChains X).homology n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (X : TopCat) (n : ℕ) : IsScalarTower ℚ ℂ ((CChains X).homology n) :=
  IsScalarTower.of_compHom ℚ ℂ _

#synth Module ℂ (ComplexPeriodSpace (Homology ℚ (TopCat.of PUnit) 0))

def test (X : TopCat) (n : ℕ) :
    Cohomology ℂ X n →ₗ[ℂ] ComplexPeriodSpace (Homology ℚ X n) where
  toFun a :=
    { toFun := fun z => a (qToCHomology X n z)
      map_add' := by intro x y; simp
      map_smul' := by intro q z; simp [Algebra.smul_def] }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp] theorem test_apply (X : TopCat) (n : ℕ)
    (a : Cohomology ℂ X n) (z : Homology ℚ X n) :
    test X n a z = a (qToCHomology X n z) := rfl

theorem test_inj (X : TopCat) (n : ℕ) : Function.Injective (test X n) := by
  intro a b h
  ext w
  apply (qToCHomology_isBaseChange X n).inductionOn w (fun w => a w = b w)
  · simp
  · intro z
    exact LinearMap.congr_fun h z
  · intro c w hw
    simp [hw]
  · intro x y hx hy
    simp [hx, hy]

end AlgebraicTopology.Singular
