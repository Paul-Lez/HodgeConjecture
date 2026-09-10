import Other.AlgebraicTopology.SingularProductDegreeOne

open CategoryTheory Limits Simplicial MonoidalCategory
open scoped Simplicial

universe u


namespace AlgebraicTopology.Simplicial

variable (R : Type u) [Field R]

noncomputable def testCochainClass {X : SSet.{u}}
    (phi : Cochain R X 2) (hphi : coboundary R 2 phi = 0) :
    CochainCohomology R X 2 := by
  let K := X.chainComplex (ModuleCat.of R R)
  let S := K.sc 2
  have hphi' : phi ∈ LinearMap.ker
      (((X.chainComplex (ModuleCat.of R R)).sc 2).f.hom.dualMap) := by
    change (((X.chainComplex (ModuleCat.of R R)).sc 2).f.hom.dualMap) phi = 0
    apply LinearMap.ext
    intro b
    rw [LinearMap.zero_apply]
    let hprev : (ComplexShape.down ℕ).prev 2 = 3 := ChainComplex.prev ℕ 2
    let b' : ChainGroup R X 3 := (K.XIsoOfEq hprev).hom.hom b
    have hd := ConcreteCategory.congr_hom
      (K.XIsoOfEq_hom_comp_d hprev 2) b
    have hv := LinearMap.congr_fun hphi b'
    rw [coboundary_apply] at hv
    change phi (S.f.hom b) = 0
    change phi ((K.d ((ComplexShape.down ℕ).prev 2) 2).hom b) = 0
    rw [← show (K.d 3 2).hom ((K.XIsoOfEq hprev).hom.hom b) =
      (K.d ((ComplexShape.down ℕ).prev 2) 2).hom b from hd]
    exact hv
  exact S.linearDual.moduleCatHomologyClass ⟨phi, hphi'⟩

theorem testCochainClass_pair {X : SSet.{u}}
    (phi : Cochain R X 2) (hphi : coboundary R 2 phi = 0)
    (c : ChainGroup R X 2) (hc : boundary R 1 c = 0) :
    let S := (X.chainComplex (ModuleCat.of R R)).sc 2
    S.linearDualHomologyEquiv (testCochainClass R phi hphi)
      (homologyClassOfTwoCycle R c hc) = phi c := by
  dsimp only
  let K := X.chainComplex (ModuleCat.of R R)
  let S := K.sc 2
  have hc' : c ∈ LinearMap.ker S.g.hom := by
    change (K.d 2 ((ComplexShape.down ℕ).next 2)).hom c = 0
    rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1]
    exact hc
  have hphi' : phi ∈ LinearMap.ker
      (((X.chainComplex (ModuleCat.of R R)).sc 2).f.hom.dualMap) := by
    change (((X.chainComplex (ModuleCat.of R R)).sc 2).f.hom.dualMap) phi = 0
    apply LinearMap.ext
    intro b
    rw [LinearMap.zero_apply]
    let hprev : (ComplexShape.down ℕ).prev 2 = 3 := ChainComplex.prev ℕ 2
    let b' : ChainGroup R X 3 := (K.XIsoOfEq hprev).hom.hom b
    have hd := ConcreteCategory.congr_hom
      (K.XIsoOfEq_hom_comp_d hprev 2) b
    have hv := LinearMap.congr_fun hphi b'
    rw [coboundary_apply] at hv
    change phi (S.f.hom b) = 0
    change phi ((K.d ((ComplexShape.down ℕ).prev 2) 2).hom b) = 0
    rw [← show (K.d 3 2).hom ((K.XIsoOfEq hprev).hom.hom b) =
      (K.d ((ComplexShape.down ℕ).prev 2) 2).hom b from hd]
    exact hv
  let z : LinearMap.ker S.g.hom := ⟨c, hc'⟩
  let eta : LinearMap.ker S.f.hom.dualMap := ⟨phi, hphi'⟩
  change S.linearDualHomologyEquiv (S.linearDual.moduleCatHomologyClass eta)
      (S.moduleCatHomologyClass z) = phi c
  exact S.linearDualHomologyEquiv_class_apply_class eta z

end AlgebraicTopology.Simplicial
