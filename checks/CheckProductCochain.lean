import Other.AlgebraicTopology.SingularProductDegreeOne

open CategoryTheory Limits Simplicial MonoidalCategory
open scoped Simplicial

universe u

namespace AlgebraicTopology.Simplicial

variable (R : Type u) [Field R]

noncomputable def testExternal {X Y : SSet.{u}}
    (phi : Cochain R X 1) (psi : Cochain R Y 1) :
    Cochain R (X ⊗ Y) 2 :=
  linearOfChainGenerators R fun z =>
    phi (chainOfSimplex R (frontFace (p := 1) (q := 1) X z.1)) *
      psi (chainOfSimplex R (backFace (p := 1) (q := 1) Y z.2))

@[simp]
lemma testExternal_apply {X Y : SSet.{u}}
    (phi : Cochain R X 1) (psi : Cochain R Y 1)
    (z : (X ⊗ Y : SSet.{u}).obj (Opposite.op (SimplexCategory.mk 2))) :
    testExternal R phi psi (chainOfSimplex R z) =
      phi (chainOfSimplex R (frontFace (p := 1) (q := 1) X z.1)) *
        psi (chainOfSimplex R (backFace (p := 1) (q := 1) Y z.2)) := by
  apply linearOfChainGenerators_chainOfSimplex

lemma cocycle_degenerate_one {X : SSet.{u}} (phi : Cochain R X 1)
    (hphi : coboundary R 1 phi = 0)
    (v : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    phi (chainOfSimplex R (X.σ 0 v)) = 0 := by
  -- Expose all three faces of the double degeneracy.
  have h0 : X.δ 0 (X.σ 0 (X.σ 0 v)) = X.σ 0 v := by
    simpa using SSet.δ_comp_σ_self_apply (S := X) (0 : Fin 2) (X.σ 0 v)
  have h1 : X.δ 1 (X.σ 0 (X.σ 0 v)) = X.σ 0 v := by
    simpa using SSet.δ_comp_σ_succ_apply (S := X) (0 : Fin 2) (X.σ 0 v)
  have h2 : X.δ 2 (X.σ 0 (X.σ 0 v)) = X.σ 0 v := by
    calc
      X.δ 2 (X.σ 0 (X.σ 0 v)) = X.σ 0 (X.δ 1 (X.σ 0 v)) := by
        simpa using SSet.δ_comp_σ_of_gt_apply (S := X)
          (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide) (X.σ 0 v)
      _ = X.σ 0 v := by
        rw [show X.δ 1 (X.σ 0 v) = v by
          simpa using SSet.δ_comp_σ_succ_apply (S := X) (0 : Fin 1) v]
  have hboundary :
      boundary R 1 (chainOfSimplex R (X.σ 0 (X.σ 0 v))) =
        chainOfSimplex R (X.σ 0 v) := by
    rw [boundary_chainOfSimplex]
    simp only [Fin.sum_univ_succ]
    erw [h0, h1, h2]
    norm_num
  have h := LinearMap.congr_fun hphi
    (chainOfSimplex R (X.σ 0 (X.σ 0 v)))
  rw [coboundary_apply, hboundary] at h
  simpa using h

lemma frontFace_one_one_eq_delta_two {X : SSet.{u}}
    (z : X.obj (Opposite.op (SimplexCategory.mk 2))) :
    frontFace (p := 1) (q := 1) X z = X.δ 2 z := by
  unfold frontFace
  rw [show frontInclusion 1 1 = SimplexCategory.δ 2 by
    ext i
    fin_cases i <;> rfl]
  rfl

lemma backFace_one_one_eq_delta_zero {X : SSet.{u}}
    (z : X.obj (Opposite.op (SimplexCategory.mk 2))) :
    backFace (p := 1) (q := 1) X z = X.δ 0 z := by
  unfold backFace
  rw [show backInclusion 1 1 = SimplexCategory.δ 0 by
    ext i
    fin_cases i <;> rfl]
  rfl

lemma testExternal_shuffleSimplex {X Y : SSet.{u}}
    (phi : Cochain R X 1) (psi : Cochain R Y 1)
    (hphi : coboundary R 1 phi = 0) (hpsi : coboundary R 1 psi = 0)
    (x : X.obj (Opposite.op (SimplexCategory.mk 1)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 1))) :
    testExternal R phi psi (degreeOneShuffleSimplex R x y) = phi (chainOfSimplex R x) *
      psi (chainOfSimplex R y) := by
  rw [degreeOneShuffleSimplex, map_sub, testExternal_apply, testExternal_apply]
  rw [frontFace_one_one_eq_delta_two, backFace_one_one_eq_delta_zero,
    frontFace_one_one_eq_delta_two, backFace_one_one_eq_delta_zero]
  change
    phi (chainOfSimplex R (X.δ 2 (X.σ 1 x))) *
        psi (chainOfSimplex R (Y.δ 0 (Y.σ 0 y))) -
      phi (chainOfSimplex R (X.δ 2 (X.σ 0 x))) *
        psi (chainOfSimplex R (Y.δ 0 (Y.σ 1 y))) = _
  have hxfirst : X.δ 2 (X.σ 1 x) = x := by
    simpa using SSet.δ_comp_σ_succ_apply (S := X) (1 : Fin 2) x
  have hyfirst : Y.δ 0 (Y.σ 0 y) = y := by
    simpa using SSet.δ_comp_σ_self_apply (S := Y) (0 : Fin 2) y
  have hxsecond : X.δ 2 (X.σ 0 x) = X.σ 0 (X.δ 1 x) := by
    simpa using SSet.δ_comp_σ_of_gt_apply (S := X)
      (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide) x
  have hysecond : Y.δ 0 (Y.σ 1 y) = Y.σ 0 (Y.δ 0 y) := by
    simpa using SSet.δ_comp_σ_of_le_apply (S := Y)
      (i := (0 : Fin 2)) (j := (0 : Fin 1)) (by decide) y
  rw [hxfirst, hyfirst, hxsecond, hysecond]
  have hx : phi (chainOfSimplex R (X.σ 0 (X.δ 1 x))) = 0 :=
    cocycle_degenerate_one R phi hphi (X.δ 1 x)
  have hy : psi (chainOfSimplex R (Y.σ 0 (Y.δ 0 y))) = 0 :=
    cocycle_degenerate_one R psi hpsi (Y.δ 0 y)
  rw [hx, hy]
  ring

lemma testExternal_shuffle {X Y : SSet.{u}}
    (phi : Cochain R X 1) (psi : Cochain R Y 1)
    (hphi : coboundary R 1 phi = 0) (hpsi : coboundary R 1 psi = 0)
    (c : ChainGroup R X 1) (d : ChainGroup R Y 1) :
    testExternal R phi psi (degreeOneShuffle R c d) = phi c * psi d := by
  let lhs := LinearMap.compr₂
    (degreeOneShuffle R :
      ChainGroup R X 1 →ₗ[R] ChainGroup R Y 1 →ₗ[R] ChainGroup R (X ⊗ Y) 2)
    (testExternal R phi psi)
  let rhs := LinearMap.compl₂ ((LinearMap.mul R R).comp phi) psi
  have hmaps : lhs = rhs := by
    apply linearMap_ext_chainOfSimplex R
    intro x
    apply linearMap_ext_chainOfSimplex R
    intro y
    simp only [lhs, rhs, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
      LinearMap.comp_apply]
    rw [degreeOneShuffle_chainOfSimplex]
    exact testExternal_shuffleSimplex R phi psi hphi hpsi x y
  exact LinearMap.congr_fun (LinearMap.congr_fun hmaps c) d

lemma test_coboundary_cochainMap {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    (phi : Cochain R Y n) :
    coboundary R n (cochainMap R f n phi) =
      cochainMap R f (n + 1) (coboundary R n phi) := by
  apply LinearMap.ext
  intro c
  rw [coboundary_apply, cochainMap_apply, cochainMap_apply, coboundary_apply]
  have h := ConcreteCategory.congr_hom
    ((SSet.chainComplexMap f (ModuleCat.of R R)).comm (n + 1) n) c
  exact congrArg phi h.symm

noncomputable def testExternalCap {X Y : SSet.{u}}
    (phi : Cochain R X 1) (psi : Cochain R Y 1) :
    Cochain R (X ⊗ Y) 2 :=
  let phi' := cochainMap R (SemiCartesianMonoidalCategory.fst X Y) 1 phi
  let psi' := cochainMap R (SemiCartesianMonoidalCategory.snd X Y) 1 psi
  psi'.comp (cap R 1 1 phi')

lemma testExternalCap_eq {X Y : SSet.{u}}
    (phi : Cochain R X 1) (psi : Cochain R Y 1) :
    testExternalCap R phi psi = testExternal R phi psi := by
  apply linearMap_ext_chainOfSimplex R
  intro z
  rw [testExternal_apply]
  dsimp only [testExternalCap, LinearMap.comp_apply]
  rw [cap_chainOfSimplex, map_smul]
  simp only [cochainMap_apply, chainOfSimplex_map]
  have hf :
      (SemiCartesianMonoidalCategory.fst X Y).app _
          (frontFace (p := 1) (q := 1) (X ⊗ Y) z) =
        frontFace (p := 1) (q := 1) X z.1 := by
    rw [← frontFace_naturality]
    rfl
  have hb :
      (SemiCartesianMonoidalCategory.snd X Y).app _
          (backFace (p := 1) (q := 1) (X ⊗ Y) z) =
        backFace (p := 1) (q := 1) Y z.2 := by
    rw [← backFace_naturality]
    rfl
  rw [hf, hb]
  rfl

lemma testExternal_cocycle {X Y : SSet.{u}}
    (phi : Cochain R X 1) (psi : Cochain R Y 1)
    (hphi : coboundary R 1 phi = 0) (hpsi : coboundary R 1 psi = 0) :
    coboundary R 2 (testExternal R phi psi) = 0 := by
  rw [← testExternalCap_eq]
  let phi' := cochainMap R (SemiCartesianMonoidalCategory.fst X Y) 1 phi
  let psi' := cochainMap R (SemiCartesianMonoidalCategory.snd X Y) 1 psi
  have hphi' : coboundary R 1 phi' = 0 := by
    dsimp only [phi']
    rw [test_coboundary_cochainMap, hphi]
    exact map_zero _
  have hpsi' : coboundary R 1 psi' = 0 := by
    dsimp only [psi']
    rw [test_coboundary_cochainMap, hpsi]
    exact map_zero _
  apply LinearMap.ext
  intro c
  rw [LinearMap.zero_apply, coboundary_apply]
  change psi' (cap R 1 1 phi' (boundary R 2 c)) = 0
  have hvanish : psi' (boundary R 1 (cap R 1 2 phi' c)) = 0 := by
    have h := LinearMap.congr_fun hpsi' (cap R 1 2 phi' c)
    rw [coboundary_apply] at h
    simpa using h
  rw [boundary_cap_eq_of_cocycle R 1 1 phi' hphi' c] at hvanish
  simpa using hvanish

noncomputable def testHomologyClassOfTwoCycle {X : SSet.{u}}
    (c : ChainGroup R X 2) (hc : boundary R 1 c = 0) :
    (X.chainComplex (ModuleCat.of R R)).homology 2 := by
  let K := X.chainComplex (ModuleCat.of R R)
  let S := K.sc 2
  have hc' : c ∈ LinearMap.ker
      (((X.chainComplex (ModuleCat.of R R)).sc 2).g.hom) := by
    change ((X.chainComplex (ModuleCat.of R R)).d 2
      ((ComplexShape.down ℕ).next 2)).hom c = 0
    rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1]
    exact hc
  exact S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk ⟨c, hc'⟩)

lemma testHomologyClassOfTwoCycle_ne_zero {X : SSet.{u}}
    (c : ChainGroup R X 2) (hc : boundary R 1 c = 0)
    (phi : Cochain R X 2) (hphi : coboundary R 2 phi = 0)
    (heval : phi c ≠ 0) :
    testHomologyClassOfTwoCycle R c hc ≠ 0 := by
  intro hzero
  let K := X.chainComplex (ModuleCat.of R R)
  let S := K.sc 2
  have hc' : c ∈ LinearMap.ker
      (((X.chainComplex (ModuleCat.of R R)).sc 2).g.hom) := by
    change ((X.chainComplex (ModuleCat.of R R)).d 2
      ((ComplexShape.down ℕ).next 2)).hom c = 0
    rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1]
    exact hc
  let z : LinearMap.ker S.g.hom := ⟨c, hc'⟩
  have hmk : (Submodule.Quotient.mk z : S.moduleCatLeftHomologyData.H) = 0 := by
    have h := congrArg S.moduleCatHomologyIso.hom.hom hzero
    change S.moduleCatHomologyIso.hom.hom
        (S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z)) =
      S.moduleCatHomologyIso.hom.hom 0 at h
    rw [map_zero] at h
    have hi := S.moduleCatHomologyIso.toLinearEquiv.apply_symm_apply
      (show S.moduleCatLeftHomologyData.H from Submodule.Quotient.mk z)
    exact hi.symm.trans h
  have hzrange : z ∈ LinearMap.range S.moduleCatToCycles :=
    (Submodule.Quotient.mk_eq_zero _).mp hmk
  obtain ⟨b, hb⟩ := hzrange
  let hprev : (ComplexShape.down ℕ).prev 2 = 3 := ChainComplex.prev ℕ 2
  let b' : ChainGroup R X 3 := (K.XIsoOfEq hprev).hom.hom b
  have hb_under : S.f.hom b = c := congrArg Subtype.val hb
  have hd := ConcreteCategory.congr_hom
    (K.XIsoOfEq_hom_comp_d hprev 2) b
  have hb' : boundary R 2 b' = c := by
    change (K.d 3 2).hom b' = c
    change (K.d 3 2).hom ((K.XIsoOfEq hprev).hom.hom b) = c
    rw [show (K.d 3 2).hom ((K.XIsoOfEq hprev).hom.hom b) =
      (K.d ((ComplexShape.down ℕ).prev 2) 2).hom b from hd]
    change (K.d ((ComplexShape.down ℕ).prev 2) 2).hom b = c at hb_under
    exact hb_under
  have hv := LinearMap.congr_fun hphi b'
  rw [coboundary_apply, hb'] at hv
  exact heval (by simpa using hv)

end AlgebraicTopology.Simplicial
