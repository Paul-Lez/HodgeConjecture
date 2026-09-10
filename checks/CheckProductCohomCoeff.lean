import Other.AlgebraicTopology.SingularProductCoefficientChange

open CategoryTheory Limits MonoidalCategory
open AlgebraicTopology
open scoped Simplicial TensorProduct

namespace AlgebraicTopology.Singular

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance (X : TopCat) (n : ℕ) : Module ℚ ((CChains X).homology n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (X : TopCat) (n : ℕ) : IsScalarTower ℚ ℂ ((CChains X).homology n) :=
  IsScalarTower.of_compHom ℚ ℂ _

lemma exists_rationalTwoCycleRepresenting (X : TopCat)
    (z : Homology ℚ X 2) :
    ∃ (c : Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) 2)
      (hc : Simplicial.boundary ℚ 1 c = 0),
      Simplicial.homologyClassOfTwoCycle ℚ c hc = z := by
  let K := QChains X
  let S := K.sc 2
  obtain ⟨eta, heta⟩ := S.moduleCatHomologyClass_surjective z
  have hc : Simplicial.boundary ℚ 1 eta.1 = 0 := by
    change (K.d 2 1).hom eta.1 = 0
    have hetaCycle := eta.2
    change (K.d 2 ((ComplexShape.down ℕ).next 2)).hom eta.1 = 0 at hetaCycle
    rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1]
      at hetaCycle
    exact hetaCycle
  refine ⟨eta.1, hc, ?_⟩
  change S.moduleCatHomologyClass eta = z
  exact heta

lemma degreeOneExternalCohomologyClass_homologyClassOfTwoCycle
    (R : Type) [Field R] {X Y : TopCat}
    (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1)
    (psi : Simplicial.Cochain R (TopCat.toSSet.obj Y) 1)
    (hphi : Simplicial.coboundary R 1 phi = 0)
    (hpsi : Simplicial.coboundary R 1 psi = 0)
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj (X ⊗ Y)) 2)
    (hc : Simplicial.boundary R 1 c = 0) :
    degreeOneExternalCohomologyClass R phi psi hphi hpsi
        (Simplicial.homologyClassOfTwoCycle R c hc) =
      degreeOneExternalCochain R phi psi c := by
  unfold degreeOneExternalCohomologyClass
  exact Simplicial.cochainClassOfTwoCocycle_pair R
    (degreeOneExternalCochain R phi psi)
    (coboundary_degreeOneExternalCochain R phi psi hphi hpsi) c hc

theorem rationalToComplexCohomologyMap_degreeOneExternalCohomologyClass
    {X Y : TopCat}
    (phi : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) 1)
    (psi : Simplicial.Cochain ℚ (TopCat.toSSet.obj Y) 1)
    (hphi : Simplicial.coboundary ℚ 1 phi = 0)
    (hpsi : Simplicial.coboundary ℚ 1 psi = 0) :
    rationalToComplexCohomologyMap (X ⊗ Y) 2
        (degreeOneExternalCohomologyClass ℚ phi psi hphi hpsi) =
      degreeOneExternalCohomologyClass ℂ
        (qToCSingularCochain X 1 phi)
        (qToCSingularCochain Y 1 psi)
        (by rw [← qToCSingularCochain_coboundary X 1 phi, hphi, map_zero])
        (by rw [← qToCSingularCochain_coboundary Y 1 psi, hpsi, map_zero]) := by
  apply LinearMap.ext
  intro w
  apply (qToCHomology_isBaseChange (X ⊗ Y) 2).inductionOn w
    (fun w =>
      rationalToComplexCohomologyMap (X ⊗ Y) 2
          (degreeOneExternalCohomologyClass ℚ phi psi hphi hpsi) w =
        degreeOneExternalCohomologyClass ℂ
          (qToCSingularCochain X 1 phi)
          (qToCSingularCochain Y 1 psi)
          (by rw [← qToCSingularCochain_coboundary X 1 phi, hphi, map_zero])
          (by rw [← qToCSingularCochain_coboundary Y 1 psi, hpsi, map_zero]) w)
  · simp
  · intro z
    obtain ⟨c, hc, hz⟩ := exists_rationalTwoCycleRepresenting (X ⊗ Y) z
    subst z
    let beta := degreeOneExternalCohomologyClass ℚ phi psi hphi hpsi
    let zQ := Simplicial.homologyClassOfTwoCycle ℚ c hc
    have hdual :
        rationalToComplexCohomologyMap (X ⊗ Y) 2 beta
            (qToCHomology (X ⊗ Y) 2 zQ) =
          algebraMap ℚ ℂ (beta zQ) := by
      exact (qToCHomology_isBaseChange (X ⊗ Y) 2).toDual_comp_apply beta zQ
    change rationalToComplexCohomologyMap (X ⊗ Y) 2 beta
        (qToCHomology (X ⊗ Y) 2 zQ) = _
    calc
      _ = algebraMap ℚ ℂ (beta zQ) := hdual
      _ = algebraMap ℚ ℂ (degreeOneExternalCochain ℚ phi psi c) := by
        rw [degreeOneExternalCohomologyClass_homologyClassOfTwoCycle]
      _ = qToCSingularCochain (X ⊗ Y) 2
          (degreeOneExternalCochain ℚ phi psi)
          (qToCChainGroup (X ⊗ Y) 2 c) := by
        rw [qToCSingularCochain_apply_qToCChain]
      _ = degreeOneExternalCochain ℂ
          (qToCSingularCochain X 1 phi)
          (qToCSingularCochain Y 1 psi)
          (qToCChainGroup (X ⊗ Y) 2 c) := by
        rw [qToCSingularCochain_degreeOneExternalCochain]
      _ = degreeOneExternalCohomologyClass ℂ
          (qToCSingularCochain X 1 phi)
          (qToCSingularCochain Y 1 psi)
          (by rw [← qToCSingularCochain_coboundary X 1 phi, hphi, map_zero])
          (by rw [← qToCSingularCochain_coboundary Y 1 psi, hpsi, map_zero])
          (Simplicial.homologyClassOfTwoCycle ℂ
            (qToCChainGroup (X ⊗ Y) 2 c)
            (by rw [boundary_qToCChainGroup (X ⊗ Y) 1 c, hc, map_zero])) := by
        rw [degreeOneExternalCohomologyClass_homologyClassOfTwoCycle]
      _ = _ := by
        rw [← qToCHomology_homologyClassOfTwoCycle]
  · intro a z hz
    simp [hz]
  · intro x y hx hy
    simp [hx, hy]

end

end AlgebraicTopology.Singular
