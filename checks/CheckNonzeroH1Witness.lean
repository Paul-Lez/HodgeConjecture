import Other.AlgebraicTopology.SingularProductDegreeOne

open CategoryTheory Limits Simplicial MonoidalCategory
open scoped Simplicial

universe u

namespace AlgebraicTopology.Simplicial

variable (R : Type u) [Field R]

theorem test_exists_pair {X : SSet.{u}}
    (alpha : Module.Dual R ((X.chainComplex (ModuleCat.of R R)).homology 1))
    (halpha : alpha ≠ 0) :
    ∃ (c : ChainGroup R X 1) (phi : Cochain R X 1),
      boundary R 0 c = 0 ∧ coboundary R 1 phi = 0 ∧ phi c ≠ 0 := by
  let K := X.chainComplex (ModuleCat.of R R)
  let S := K.sc 1
  let alpha' : Module.Dual R S.homology := alpha
  have halpha' : alpha' ≠ 0 := halpha
  obtain ⟨z, hz⟩ : ∃ z, alpha' z ≠ 0 := by
    by_contra hall
    push Not at hall
    apply halpha'
    ext z
    exact hall z
  obtain ⟨x, hx⟩ := S.moduleCatHomologyClass_surjective z
  obtain ⟨eta, heta⟩ := S.linearDual.moduleCatHomologyClass_surjective
    (S.linearDualHomologyEquiv.symm alpha')
  let phi : Cocycle R X 1 := cohomologyCycleToCocycle R 1 eta
  have hpair := S.linearDualHomologyEquiv_class_apply_class eta x
  rw [heta, S.linearDualHomologyEquiv.apply_symm_apply, hx] at hpair
  have hphi_eval : phi.1 x.1 ≠ 0 := by
    change (show Module.Dual R S.X₂ from eta.1) x.1 ≠ 0
    rw [← hpair]
    exact hz
  have hxcycle := x.2
  have hc : boundary R 0 x.1 = 0 := by
    change (K.d 1 0).hom x.1 = 0
    change (K.d 1 ((ComplexShape.down ℕ).next 1)).hom x.1 = 0 at hxcycle
    rw [show (ComplexShape.down ℕ).next 1 = 0 from ChainComplex.next_nat_succ 0]
      at hxcycle
    exact hxcycle
  exact ⟨x.1, phi.1, hc, phi.2, hphi_eval⟩

end AlgebraicTopology.Simplicial

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

theorem test_exists_pair_top {X : TopCat.{u}}
    (alpha : Cohomology R X 1) (halpha : alpha ≠ 0) :
    ∃ (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 1)
        (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1),
      Simplicial.boundary R 0 c = 0 ∧
        Simplicial.coboundary R 1 phi = 0 ∧ phi c ≠ 0 :=
  Simplicial.test_exists_pair R alpha halpha

end AlgebraicTopology.Singular
