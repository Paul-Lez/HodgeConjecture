import Other.AlgebraicTopology.SingularDegreeOneExternalFunctoriality

noncomputable section

open CategoryTheory Limits Simplicial MonoidalCategory
open scoped Simplicial

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

set_option backward.isDefEq.respectTransparency false in
theorem test_external_represented
    (X Y : TopCat.{u})
    (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1)
    (psi : Simplicial.Cochain R (TopCat.toSSet.obj Y) 1)
    (hphi : Simplicial.coboundary R 1 phi = 0)
    (hpsi : Simplicial.coboundary R 1 psi = 0) :
    let SX := ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).sc 1
    let SY := ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).sc 1
    degreeOneExternalCohomologyBilinear R X Y
        (SX.linearDualHomologyEquiv
          (Simplicial.cochainClassOfOneCocycle R phi hphi))
        (SY.linearDualHomologyEquiv
          (Simplicial.cochainClassOfOneCocycle R psi hpsi)) =
      degreeOneExternalCohomologyClass R phi psi hphi hpsi := by
  dsimp only
  apply LinearMap.ext
  intro z
  let T := ((TopCat.toSSet.obj (X ⊗ Y)).chainComplex
    (ModuleCat.of R R)).sc 2
  obtain ⟨z₂, hz₂⟩ := T.moduleCatHomologyClass_surjective z
  rw [← hz₂]
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
  let S := ((TopCat.toSSet.obj (X ⊗ Y)).chainComplex
    (ModuleCat.of R R)).sc 1
  let aclass := Simplicial.cochainClassOfOneCocycle R phi' hphi'
  let bclass := Simplicial.cochainClassOfOneCocycle R psi' hpsi'
  have ha : cohomologyMap R 1 (SemiCartesianMonoidalCategory.fst X Y)
      (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).sc 1
        |>.linearDualHomologyEquiv
          (Simplicial.cochainClassOfOneCocycle R phi hphi)) =
      S.linearDualHomologyEquiv aclass :=
    cohomologyMap_represented_one R _ phi hphi
  have hb : cohomologyMap R 1 (SemiCartesianMonoidalCategory.snd X Y)
      (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).sc 1
        |>.linearDualHomologyEquiv
          (Simplicial.cochainClassOfOneCocycle R psi hpsi)) =
      S.linearDualHomologyEquiv bclass :=
    cohomologyMap_represented_one R _ psi hpsi
  unfold degreeOneExternalCohomologyBilinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [ha, hb]
  change (cochainCohomologyEquiv R (X ⊗ Y) 1 bclass)
      (standardCapCohomologyLinear R (X ⊗ Y) 1 1
        (cochainCohomologyEquiv R (X ⊗ Y) 1 aclass)
        (T.moduleCatHomologyClass z₂)) = _
  have hinv : (cochainCohomologyEquiv R (X ⊗ Y) 1).symm
      (cochainCohomologyEquiv R (X ⊗ Y) 1 aclass) = aclass :=
    (cochainCohomologyEquiv R (X ⊗ Y) 1).symm_apply_apply aclass
  unfold standardCapCohomologyLinear
  simp only [LinearMap.comp_apply]
  change (cochainCohomologyEquiv R (X ⊗ Y) 1 bclass)
      (capCohomologyLinear R (X ⊗ Y) 1 1
        ((cochainCohomologyEquiv R (X ⊗ Y) 1).symm
          (cochainCohomologyEquiv R (X ⊗ Y) 1 aclass))
        (T.moduleCatHomologyClass z₂)) = _
  rw [hinv]
  have hacap : capCohomologyLinear R (X ⊗ Y) 1 1 aclass =
      Simplicial.capCocycleHomologyLinear R 1 1 ⟨phi', hphi'⟩ :=
    capCohomologyLinear_cochainClassOfOneCocycle R 1 phi' hphi'
  rw [hacap]
  let F := Simplicial.capShortComplexHom R 1 1 phi' hphi'
  let z₁ := ShortComplex.moduleCatCycleMap F z₂
  have hcapclass :
      (Simplicial.capCocycleHomologyLinear R 1 1 ⟨phi', hphi'⟩)
          (T.moduleCatHomologyClass z₂) = S.moduleCatHomologyClass z₁ := by
    change (ShortComplex.homologyMap F).hom (T.moduleCatHomologyClass z₂) = _
    exact ShortComplex.moduleCatHomologyClass_naturality F z₂
  change S.linearDualHomologyEquiv bclass
      ((Simplicial.capCocycleHomologyLinear R 1 1 ⟨phi', hphi'⟩)
        (T.moduleCatHomologyClass z₂)) = _
  calc
    _ = S.linearDualHomologyEquiv bclass (S.moduleCatHomologyClass z₁) :=
      congrArg (S.linearDualHomologyEquiv bclass) hcapclass
    _ = _ := by
      dsimp only [bclass]
      unfold Simplicial.cochainClassOfOneCocycle
      rw [S.linearDualHomologyEquiv_class_apply_class]
      change psi' (Simplicial.cap R 1 1 phi' z₂.1) = _
      have hcup := LinearMap.congr_fun
        (degreeOneExternalCochain_eq_projectionCap R X Y phi psi) z₂.1
      calc
        _ = degreeOneExternalCochain R phi psi z₂.1 := by
          change (psi'.comp (Simplicial.cap R 1 1 phi')) z₂.1 = _
          exact hcup
        _ = _ := by
          have hzboundary : Simplicial.boundary R 1 z₂.1 = 0 := by
            have hz := z₂.2
            change ((((TopCat.toSSet.obj (X ⊗ Y)).chainComplex
              (ModuleCat.of R R)).d 2
                ((ComplexShape.down ℕ).next 2)).hom z₂.1) = 0 at hz
            rw [show (ComplexShape.down ℕ).next 2 = 1 from
              ChainComplex.next_nat_succ 1] at hz
            exact hz
          have hzclass : T.moduleCatHomologyClass z₂ =
              Simplicial.homologyClassOfTwoCycle R z₂.1 hzboundary := by
            rfl
          rw [hzclass]
          exact (Simplicial.cochainClassOfTwoCocycle_pair R
            (degreeOneExternalCochain R phi psi)
            (coboundary_degreeOneExternalCochain R phi psi hphi hpsi)
            z₂.1 hzboundary).symm

end AlgebraicTopology.Singular
