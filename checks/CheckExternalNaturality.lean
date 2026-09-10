import Other.AlgebraicTopology.SingularProductDegreeOne

noncomputable section

open CategoryTheory Limits Simplicial MonoidalCategory
open scoped Simplicial

universe u

namespace AlgebraicTopology.Simplicial

variable (R : Type u) [Field R]

theorem test_degreeOneExternalCochain_naturality
    {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    (phi : Cochain R X' 1) (psi : Cochain R Y' 1) :
    cochainMap R (f ⊗ₘ g) 2 (degreeOneExternalCochain R phi psi) =
      degreeOneExternalCochain R (cochainMap R f 1 phi) (cochainMap R g 1 psi) := by
  apply linearMap_ext_chainOfSimplex R
  intro z
  rw [cochainMap_apply, chainOfSimplex_map,
    degreeOneExternalCochain_chainOfSimplex,
    degreeOneExternalCochain_chainOfSimplex]
  change
    phi (chainOfSimplex R (frontFace (p := 1) (q := 1) X' (f.app _ z.1))) *
        psi (chainOfSimplex R (backFace (p := 1) (q := 1) Y' (g.app _ z.2))) = _
  rw [frontFace_naturality, backFace_naturality]
  simp only [cochainMap_apply]
  rw [chainOfSimplex_map, chainOfSimplex_map]

set_option backward.isDefEq.respectTransparency false in
theorem test_cochainClassOfOneCocycle_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (phi : Cochain R Y 1) (hphi : coboundary R 1 phi = 0) :
    cochainCohomologyMap R f 1
        (cochainClassOfOneCocycle R phi hphi) =
      cochainClassOfOneCocycle R (cochainMap R f 1 phi)
        (by rw [coboundary_cochainMap, hphi, map_zero]) := by
  unfold cochainCohomologyMap cochainClassOfOneCocycle
  rw [ShortComplex.moduleCatHomologyClass_naturality]
  rfl

end AlgebraicTopology.Simplicial

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

#check standardCapCohomologyLinear
#check SemiCartesianMonoidalCategory.fst
#check SemiCartesianMonoidalCategory.snd
#check LinearMap.compr₂
#check LinearMap.compl₂

set_option backward.isDefEq.respectTransparency false in
theorem test_cohomologyMap_represented_one {X Y : TopCat.{u}} (f : X ⟶ Y)
    (phi : Simplicial.Cochain R (TopCat.toSSet.obj Y) 1)
    (hphi : Simplicial.coboundary R 1 phi = 0) :
    cohomologyMap R 1 f
        (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).sc 1
          |>.linearDualHomologyEquiv
            (Simplicial.cochainClassOfOneCocycle R phi hphi)) =
      (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).sc 1
        |>.linearDualHomologyEquiv
          (Simplicial.cochainClassOfOneCocycle R
            (Simplicial.cochainMap R (TopCat.toSSet.map f) 1 phi)
            (by rw [Simplicial.coboundary_cochainMap, hphi, map_zero]))) := by
  change cohomologyMap R 1 f
      (cochainCohomologyEquiv R Y 1
        (Simplicial.cochainClassOfOneCocycle R phi hphi)) =
    cochainCohomologyEquiv R X 1
      (Simplicial.cochainClassOfOneCocycle R
        (Simplicial.cochainMap R (TopCat.toSSet.map f) 1 phi) _)
  rw [← cochainCohomologyEquiv_naturality]
  change cochainCohomologyEquiv R X 1
      (Simplicial.cochainCohomologyMap R (TopCat.toSSet.map f) 1
        (Simplicial.cochainClassOfOneCocycle R phi hphi)) = _
  rw [Simplicial.test_cochainClassOfOneCocycle_naturality]

def test_degreeOneExternalCohomologyBilinear (X Y : TopCat.{u}) :
    Cohomology R X 1 →ₗ[R] Cohomology R Y 1 →ₗ[R] Cohomology R (X ⊗ Y) 2 where
  toFun alpha :=
    { toFun := fun beta =>
        { toFun := fun z =>
            cohomologyMap R 1 (SemiCartesianMonoidalCategory.snd X Y) beta
              (standardCapCohomologyLinear R (X ⊗ Y) 1 1
                (cohomologyMap R 1 (SemiCartesianMonoidalCategory.fst X Y) alpha) z)
          map_add' := by intro z z'; simp
          map_smul' := by intro c z; simp }
      map_add' := by intro beta beta'; ext z; simp
      map_smul' := by intro c beta; ext z; simp }
  map_add' := by intro alpha alpha'; ext beta z; simp
  map_smul' := by intro c alpha; ext beta z; simp

set_option backward.isDefEq.respectTransparency false in
lemma test_capCohomologyLinear_moduleCatHomologyClass
    {X : SSet.{u}} (p q : ℕ)
    (phi : LinearMap.ker
      (((X.chainComplex (ModuleCat.of R R)).sc p).linearDual.g.hom)) :
    let T := ((X.chainComplex (ModuleCat.of R R)).sc p).linearDual
    Simplicial.capCohomologyLinear R p q (T.moduleCatHomologyClass phi) =
      Simplicial.cohomologyCycleCapLinear R p q phi := by
  dsimp only
  let T := ((X.chainComplex (ModuleCat.of R R)).sc p).linearDual
  change Simplicial.capCohomologyLinear R p q
      (T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi)) = _
  exact Simplicial.capCohomologyLinear_on_cycle R p q phi

set_option backward.isDefEq.respectTransparency false in
lemma test_capCohomologyLinear_cochainClassOfOneCocycle
    {X : SSet.{u}} (q : ℕ)
    (phi : Simplicial.Cochain R X 1)
    (hphi : Simplicial.coboundary R 1 phi = 0) :
    Simplicial.capCohomologyLinear R 1 q
        (Simplicial.cochainClassOfOneCocycle R phi hphi) =
      Simplicial.capCocycleHomologyLinear R 1 q ⟨phi, hphi⟩ := by
  unfold Simplicial.cochainClassOfOneCocycle
  rw [test_capCohomologyLinear_moduleCatHomologyClass]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma test_capHomologyMap_homologyClassOfTwoCycle
    {X : SSet.{u}}
    (phi : Simplicial.Cochain R X 1)
    (hphi : Simplicial.coboundary R 1 phi = 0)
    (c : Simplicial.ChainGroup R X 2)
    (hc : Simplicial.boundary R 1 c = 0) :
    let S := (X.chainComplex (ModuleCat.of R R)).sc 1
    Simplicial.capHomologyMap R 1 1 phi hphi
        (Simplicial.homologyClassOfTwoCycle R c hc) =
      S.moduleCatHomologyClass
        ⟨Simplicial.cap R 1 1 phi c, by
          have hcapzero : Simplicial.boundary R 0
              (Simplicial.cap R 1 1 phi c) = 0 := by
            rw [Simplicial.boundary_cap_eq_of_cocycle R 1 0 phi hphi c, hc,
              map_zero, smul_zero]
          change (((X.chainComplex (ModuleCat.of R R)).d 1
            ((ComplexShape.down ℕ).next 1)).hom
              (Simplicial.cap R 1 1 phi c)) = 0
          rw [show (ComplexShape.down ℕ).next 1 = 0 from
            ChainComplex.next_nat_succ 0]
          exact hcapzero⟩ := by
  dsimp only
  let K := X.chainComplex (ModuleCat.of R R)
  let S₂ := K.sc 2
  let S₁ := K.sc 1
  let z₂ : LinearMap.ker S₂.g.hom := ⟨c, by
    change (K.d 2 ((ComplexShape.down ℕ).next 2)).hom c = 0
    rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1]
    exact hc⟩
  change (ShortComplex.homologyMap
      (Simplicial.capShortComplexHom R 1 1 phi hphi)).hom
        (S₂.moduleCatHomologyClass z₂) = _
  rw [ShortComplex.moduleCatHomologyClass_naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma test_degreeOneExternalCochain_eq_projectionCap
    (X Y : TopCat.{u})
    (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1)
    (psi : Simplicial.Cochain R (TopCat.toSSet.obj Y) 1) :
    let phi' := Simplicial.cochainMap R
      (TopCat.toSSet.map (SemiCartesianMonoidalCategory.fst X Y)) 1 phi
    let psi' := Simplicial.cochainMap R
      (TopCat.toSSet.map (SemiCartesianMonoidalCategory.snd X Y)) 1 psi
    psi'.comp (Simplicial.cap R 1 1 phi') =
      degreeOneExternalCochain R phi psi := by
  dsimp only
  apply Simplicial.linearMap_ext_chainOfSimplex R
  intro z
  unfold degreeOneExternalCochain
  rw [Simplicial.cochainMap_apply, Simplicial.chainOfSimplex_map,
    Simplicial.degreeOneExternalCochain_chainOfSimplex]
  simp only [LinearMap.comp_apply]
  rw [Simplicial.cap_chainOfSimplex, map_smul]
  simp only [Simplicial.cochainMap_apply, Simplicial.chainOfSimplex_map]
  have hfst₂ :
      (TopCat.toSSet.map (SemiCartesianMonoidalCategory.fst X Y)).app _ z =
        ((singularProductComparison X Y).hom.app _ z).1 := by
    have happ := congrArg (fun k => k.app (Opposite.op (SimplexCategory.mk (1 + 1))))
      (CartesianMonoidalCategory.prodComparison_fst TopCat.toSSet X Y)
    have h := ConcreteCategory.congr_hom happ z
    change _ = ((CartesianMonoidalCategory.prodComparison TopCat.toSSet X Y).app _ z).1
    calc
      _ = (((CartesianMonoidalCategory.prodComparison TopCat.toSSet X Y ≫
          SemiCartesianMonoidalCategory.fst _ _).app _) z) := h.symm
      _ = _ := rfl
  have hsnd₂ :
      (TopCat.toSSet.map (SemiCartesianMonoidalCategory.snd X Y)).app _ z =
        ((singularProductComparison X Y).hom.app _ z).2 := by
    have happ := congrArg (fun k => k.app (Opposite.op (SimplexCategory.mk (1 + 1))))
      (CartesianMonoidalCategory.prodComparison_snd TopCat.toSSet X Y)
    have h := ConcreteCategory.congr_hom happ z
    change _ = ((CartesianMonoidalCategory.prodComparison TopCat.toSSet X Y).app _ z).2
    calc
      _ = (((CartesianMonoidalCategory.prodComparison TopCat.toSSet X Y ≫
          SemiCartesianMonoidalCategory.snd _ _).app _) z) := h.symm
      _ = _ := rfl
  have hfront :
      (TopCat.toSSet.map (SemiCartesianMonoidalCategory.fst X Y)).app _
          (Simplicial.frontFace (TopCat.toSSet.obj (X ⊗ Y)) z) =
        Simplicial.frontFace (TopCat.toSSet.obj X)
          ((singularProductComparison X Y).hom.app _ z).1 := by
    rw [← Simplicial.frontFace_naturality]
    exact congrArg (Simplicial.frontFace (p := 1) (q := 1)
      (TopCat.toSSet.obj X)) hfst₂
  have hback :
      (TopCat.toSSet.map (SemiCartesianMonoidalCategory.snd X Y)).app _
          (Simplicial.backFace (TopCat.toSSet.obj (X ⊗ Y)) z) =
        Simplicial.backFace (TopCat.toSSet.obj Y)
          ((singularProductComparison X Y).hom.app _ z).2 := by
    rw [← Simplicial.backFace_naturality]
    exact congrArg (Simplicial.backFace (p := 1) (q := 1)
      (TopCat.toSSet.obj Y)) hsnd₂
  rw [hfront, hback]
  exact smul_eq_mul _ _

set_option backward.isDefEq.respectTransparency false in
theorem test_degreeOneExternalCohomologyBilinear_shuffle
    (X Y : TopCat.{u})
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 1)
    (d : Simplicial.ChainGroup R (TopCat.toSSet.obj Y) 1)
    (hc : Simplicial.boundary R 0 c = 0)
    (hd : Simplicial.boundary R 0 d = 0)
    (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1)
    (psi : Simplicial.Cochain R (TopCat.toSSet.obj Y) 1)
    (hphi : Simplicial.coboundary R 1 phi = 0)
    (hpsi : Simplicial.coboundary R 1 psi = 0) :
    let SX := ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).sc 1
    let SY := ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).sc 1
    test_degreeOneExternalCohomologyBilinear R X Y
        (SX.linearDualHomologyEquiv
          (Simplicial.cochainClassOfOneCocycle R phi hphi))
        (SY.linearDualHomologyEquiv
          (Simplicial.cochainClassOfOneCocycle R psi hpsi))
        (degreeOneShuffleHomologyClass R c d hc hd) =
      phi c * psi d := by
  dsimp only
  unfold test_degreeOneExternalCohomologyBilinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  change
    (cohomologyMap R 1 (SemiCartesianMonoidalCategory.snd X Y)
      (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).sc 1
        |>.linearDualHomologyEquiv
          (Simplicial.cochainClassOfOneCocycle R psi hpsi)))
      (standardCapCohomologyLinear R (X ⊗ Y) 1 1
        (cohomologyMap R 1 (SemiCartesianMonoidalCategory.fst X Y)
          (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).sc 1
            |>.linearDualHomologyEquiv
              (Simplicial.cochainClassOfOneCocycle R phi hphi)))
        (degreeOneShuffleHomologyClass R c d hc hd)) = _
  rw [test_cohomologyMap_represented_one, test_cohomologyMap_represented_one]
  let phi' := Simplicial.cochainMap R
    (TopCat.toSSet.map (SemiCartesianMonoidalCategory.fst X Y)) 1 phi
  let psi' := Simplicial.cochainMap R
    (TopCat.toSSet.map (SemiCartesianMonoidalCategory.snd X Y)) 1 psi
  have hphi' : Simplicial.coboundary R 1 phi' = 0 := by
    dsimp only [phi']
    rw [Simplicial.coboundary_cochainMap, hphi, map_zero]
  have hpsi' : Simplicial.coboundary R 1 psi' = 0 := by
    dsimp only [psi']
    rw [Simplicial.coboundary_cochainMap, hpsi, map_zero]
  let aclass := Simplicial.cochainClassOfOneCocycle R phi' hphi'
  let bclass := Simplicial.cochainClassOfOneCocycle R psi' hpsi'
  change (cochainCohomologyEquiv R (X ⊗ Y) 1 bclass)
      (standardCapCohomologyLinear R (X ⊗ Y) 1 1
        (cochainCohomologyEquiv R (X ⊗ Y) 1 aclass)
        (degreeOneShuffleHomologyClass R c d hc hd)) = _
  have hinv : (cochainCohomologyEquiv R (X ⊗ Y) 1).symm
      (cochainCohomologyEquiv R (X ⊗ Y) 1 aclass) = aclass :=
    (cochainCohomologyEquiv R (X ⊗ Y) 1).symm_apply_apply aclass
  unfold standardCapCohomologyLinear
  simp only [LinearMap.comp_apply]
  change (cochainCohomologyEquiv R (X ⊗ Y) 1 bclass)
      (capCohomologyLinear R (X ⊗ Y) 1 1
        ((cochainCohomologyEquiv R (X ⊗ Y) 1).symm
          (cochainCohomologyEquiv R (X ⊗ Y) 1 aclass))
        (degreeOneShuffleHomologyClass R c d hc hd)) = _
  rw [hinv]
  have ha : capCohomologyLinear R (X ⊗ Y) 1 1 aclass =
      Simplicial.capCocycleHomologyLinear R 1 1 ⟨phi', hphi'⟩ := by
    dsimp only [aclass]
    exact test_capCohomologyLinear_cochainClassOfOneCocycle R 1 phi' hphi'
  rw [ha]
  let c₂ := degreeOneShuffleChain R c d
  have hc₂ : Simplicial.boundary R 1 c₂ = 0 :=
    boundary_degreeOneShuffleChain_eq_zero R c d hc hd
  let S₁ := ((TopCat.toSSet.obj (X ⊗ Y)).chainComplex
    (ModuleCat.of R R)).sc 1
  let z₁ : LinearMap.ker S₁.g.hom := ⟨Simplicial.cap R 1 1 phi' c₂, by
    have hz : Simplicial.boundary R 0 (Simplicial.cap R 1 1 phi' c₂) = 0 := by
      rw [Simplicial.boundary_cap_eq_of_cocycle R 1 0 phi' hphi' c₂,
        hc₂, map_zero, smul_zero]
    change ((((TopCat.toSSet.obj (X ⊗ Y)).chainComplex
      (ModuleCat.of R R)).d 1 ((ComplexShape.down ℕ).next 1)).hom
        (Simplicial.cap R 1 1 phi' c₂)) = 0
    rw [show (ComplexShape.down ℕ).next 1 = 0 from ChainComplex.next_nat_succ 0]
    exact hz⟩
  have hcapclass :
      (Simplicial.capCocycleHomologyLinear R 1 1 ⟨phi', hphi'⟩)
          (degreeOneShuffleHomologyClass R c d hc hd) =
        S₁.moduleCatHomologyClass z₁ := by
    change Simplicial.capHomologyMap R 1 1 phi' hphi'
      (Simplicial.homologyClassOfTwoCycle R c₂ hc₂) = _
    exact test_capHomologyMap_homologyClassOfTwoCycle R phi' hphi' c₂ hc₂
  change S₁.linearDualHomologyEquiv bclass
      ((Simplicial.capCocycleHomologyLinear R 1 1 ⟨phi', hphi'⟩)
        (degreeOneShuffleHomologyClass R c d hc hd)) = _
  calc
    _ = S₁.linearDualHomologyEquiv bclass (S₁.moduleCatHomologyClass z₁) :=
      congrArg (S₁.linearDualHomologyEquiv bclass) hcapclass
    _ = _ := by
      dsimp only [bclass]
      unfold Simplicial.cochainClassOfOneCocycle
      rw [S₁.linearDualHomologyEquiv_class_apply_class]
      change psi' (Simplicial.cap R 1 1 phi' c₂) = phi c * psi d
      calc
        _ = degreeOneExternalCochain R phi psi c₂ :=
          LinearMap.congr_fun
            (test_degreeOneExternalCochain_eq_projectionCap R X Y phi psi) c₂
        _ = _ := degreeOneExternalCochain_shuffleChain R phi psi hphi hpsi c d

end AlgebraicTopology.Singular
