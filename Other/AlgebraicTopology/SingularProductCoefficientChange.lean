/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularCochainCoefficientBaseChange
public import Other.AlgebraicTopology.SingularProductDegreeOne

/-!
# Coefficient change for the degree-one singular external product

Rational singular cochains extend uniquely to complex-linear cochains.  This
file proves that the extension commutes with the singular coboundary and with
the explicit degree-`(1,1)` external cochain used for the elliptic-surface
candidate.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open AlgebraicTopology
open scoped Simplicial

namespace AlgebraicTopology.Singular

local instance qToCProductModuleChains (X : TopCat) (n : ℕ) :
    Module ℚ ((CChains X).X n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance qToCProductScalarTowerChains (X : TopCat) (n : ℕ) :
    IsScalarTower ℚ ℂ ((CChains X).X n) :=
  IsScalarTower.of_compHom ℚ ℂ _

local instance qToCProductModuleCycles (X : TopCat) (n : ℕ) :
    Module ℚ (CCyclesModel X n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance qToCProductScalarTowerCycles (X : TopCat) (n : ℕ) :
    IsScalarTower ℚ ℂ (CCyclesModel X n) :=
  IsScalarTower.of_compHom ℚ ℂ _

local instance qToCProductModuleHomology (X : TopCat) (n : ℕ) :
    Module ℚ ((CChains X).homology n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance qToCProductScalarTowerHomology (X : TopCat) (n : ℕ) :
    IsScalarTower ℚ ℂ ((CChains X).homology n) :=
  IsScalarTower.of_compHom ℚ ℂ _

/-- Extend a rational singular cochain to the unique complex-linear cochain
with the prescribed values on rational chains. -/
def qToCSingularCochain (X : TopCat) (n : ℕ) :
    Simplicial.Cochain ℚ (TopCat.toSSet.obj X) n →ₗ[ℚ]
      Simplicial.Cochain ℂ (TopCat.toSSet.obj X) n :=
  (qToCChainGroup_isBaseChange X n).toDual

/-- The extended cochain takes the coefficient-extended value on a rational
chain. -/
@[simp]
lemma qToCSingularCochain_apply_qToCChain (X : TopCat) (n : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) n)
    (c : Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) n) :
    qToCSingularCochain X n φ (qToCChainGroup X n c) =
      algebraMap ℚ ℂ (φ c) :=
  (qToCChainGroup_isBaseChange X n).toDual_comp_apply φ c

/-- Coefficient extension commutes with the singular boundary. -/
lemma boundary_qToCChainGroup (X : TopCat) (n : ℕ)
    (c : Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) (n + 1)) :
    Simplicial.boundary ℂ n (qToCChainGroup X (n + 1) c) =
      qToCChainGroup X n (Simplicial.boundary ℚ n c) := by
  have h := ConcreteCategory.congr_hom ((qToCChainMap X).comm (n + 1) n) c
  change ((CChains X).d (n + 1) n).hom (qToCChainGroup X (n + 1) c) =
    qToCChainGroup X n (((QChains X).d (n + 1) n).hom c)
  change ((CChains X).d (n + 1) n).hom (qToCChainGroup X (n + 1) c) =
    qToCChainGroup X n (((QChains X).d (n + 1) n).hom c) at h
  exact h

/-- Rational-to-complex extension is a cochain map on whole-space singular
cochains. -/
lemma qToCSingularCochain_coboundary (X : TopCat) (n : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) n) :
    qToCSingularCochain X (n + 1) (Simplicial.coboundary ℚ n φ) =
      Simplicial.coboundary ℂ n (qToCSingularCochain X n φ) := by
  apply Simplicial.linearMap_ext_chainOfSimplex ℂ
  intro x
  have hi : qToCChainGroup X (n + 1)
      (Simplicial.chainOfSimplex ℚ x) =
      Simplicial.chainOfSimplex ℂ x := by
    simpa only [Simplicial.chainOfSimplex, map_one] using
      qToCChainGroup_iota X (n + 1) x (1 : ℚ)
  rw [← hi, qToCSingularCochain_apply_qToCChain]
  simp only [Simplicial.coboundary_apply]
  rw [boundary_qToCChainGroup, qToCSingularCochain_apply_qToCChain]

/-- Coefficient extension commutes exactly with the explicit degree-`(1,1)`
external cochain on a topological product. -/
theorem qToCSingularCochain_degreeOneExternalCochain {X Y : TopCat}
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) 1)
    (ψ : Simplicial.Cochain ℚ (TopCat.toSSet.obj Y) 1) :
    qToCSingularCochain (X ⊗ Y) 2 (degreeOneExternalCochain ℚ φ ψ) =
      degreeOneExternalCochain ℂ
        (qToCSingularCochain X 1 φ) (qToCSingularCochain Y 1 ψ) := by
  apply Simplicial.linearMap_ext_chainOfSimplex ℂ
  intro z
  have hi : qToCChainGroup (X ⊗ Y) 2
      (Simplicial.chainOfSimplex ℚ z) =
      Simplicial.chainOfSimplex ℂ z := by
    simpa only [Simplicial.chainOfSimplex, map_one] using
      qToCChainGroup_iota (X ⊗ Y) 2 z (1 : ℚ)
  rw [← hi, qToCSingularCochain_apply_qToCChain]
  rw [hi]
  unfold degreeOneExternalCochain
  rw [Simplicial.cochainMap_apply, Simplicial.cochainMap_apply]
  have hQ := SSet.ι_chainComplexMap_f
    (X := TopCat.toSSet.obj (X ⊗ Y))
    (Y := TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y)
    (f := (singularProductComparison X Y).hom)
    (R := ModuleCat.of ℚ ℚ) z
  have hC := SSet.ι_chainComplexMap_f
    (X := TopCat.toSSet.obj (X ⊗ Y))
    (Y := TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y)
    (f := (singularProductComparison X Y).hom)
    (R := ModuleCat.of ℂ ℂ) z
  have hQ1 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hQ) (1 : ℚ)
  have hC1 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hC) (1 : ℂ)
  simp only [ConcreteCategory.comp_apply] at hQ1 hC1
  change algebraMap ℚ ℂ
      (Simplicial.degreeOneExternalCochain ℚ φ ψ
        (((SSet.chainComplexMap (singularProductComparison X Y).hom
          (ModuleCat.of ℚ ℚ)).f 2).hom (Simplicial.chainOfSimplex ℚ z))) =
    Simplicial.degreeOneExternalCochain ℂ
      (qToCSingularCochain X 1 φ) (qToCSingularCochain Y 1 ψ)
      (((SSet.chainComplexMap (singularProductComparison X Y).hom
        (ModuleCat.of ℂ ℂ)).f 2).hom (Simplicial.chainOfSimplex ℂ z))
  rw [show ((SSet.chainComplexMap (singularProductComparison X Y).hom
      (ModuleCat.of ℚ ℚ)).f 2).hom (Simplicial.chainOfSimplex ℚ z) =
      Simplicial.chainOfSimplex ℚ
        ((singularProductComparison X Y).hom.app _ z) by
        simpa only [Simplicial.chainOfSimplex] using hQ1,
    show ((SSet.chainComplexMap (singularProductComparison X Y).hom
      (ModuleCat.of ℂ ℂ)).f 2).hom (Simplicial.chainOfSimplex ℂ z) =
      Simplicial.chainOfSimplex ℂ
        ((singularProductComparison X Y).hom.app _ z) by
        simpa only [Simplicial.chainOfSimplex] using hC1,
    Simplicial.degreeOneExternalCochain_chainOfSimplex,
    Simplicial.degreeOneExternalCochain_chainOfSimplex]
  have hx : qToCChainGroup X 1
      (Simplicial.chainOfSimplex ℚ
        (Simplicial.frontFace (p := 1) (q := 1) (TopCat.toSSet.obj X)
          ((singularProductComparison X Y).hom.app _ z).1)) =
      Simplicial.chainOfSimplex ℂ
        (Simplicial.frontFace (p := 1) (q := 1) (TopCat.toSSet.obj X)
          ((singularProductComparison X Y).hom.app _ z).1) := by
    simpa only [Simplicial.chainOfSimplex, map_one] using
      qToCChainGroup_iota X 1
        (Simplicial.frontFace (p := 1) (q := 1) (TopCat.toSSet.obj X)
          ((singularProductComparison X Y).hom.app _ z).1) (1 : ℚ)
  have hy : qToCChainGroup Y 1
      (Simplicial.chainOfSimplex ℚ
        (Simplicial.backFace (p := 1) (q := 1) (TopCat.toSSet.obj Y)
          ((singularProductComparison X Y).hom.app _ z).2)) =
      Simplicial.chainOfSimplex ℂ
        (Simplicial.backFace (p := 1) (q := 1) (TopCat.toSSet.obj Y)
          ((singularProductComparison X Y).hom.app _ z).2) := by
    simpa only [Simplicial.chainOfSimplex, map_one] using
      qToCChainGroup_iota Y 1
        (Simplicial.backFace (p := 1) (q := 1) (TopCat.toSSet.obj Y)
          ((singularProductComparison X Y).hom.app _ z).2) (1 : ℚ)
  rw [← hx, ← hy, qToCSingularCochain_apply_qToCChain,
    qToCSingularCochain_apply_qToCChain, map_mul]

/-- Extending coefficients sends the class of an explicit rational two-cycle to the class of
the coefficient-extended complex two-cycle. -/
theorem qToCHomology_homologyClassOfTwoCycle (X : TopCat)
    (c : Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) 2)
    (hc : Simplicial.boundary ℚ 1 c = 0) :
    qToCHomology X 2 (Simplicial.homologyClassOfTwoCycle ℚ c hc) =
      Simplicial.homologyClassOfTwoCycle ℂ (qToCChainGroup X 2 c)
        (by rw [boundary_qToCChainGroup X 1 c, hc, map_zero]) := by
  let KQ := QChains X
  let KC := CChains X
  let SQ := KQ.sc 2
  let SC := KC.sc 2
  have hcQ : c ∈ LinearMap.ker SQ.g.hom := by
    change (KQ.d 2 ((ComplexShape.down ℕ).next 2)).hom c = 0
    rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1]
    exact hc
  let zQ : LinearMap.ker SQ.g.hom := ⟨c, hcQ⟩
  have hcC : qToCChainGroup X 2 c ∈ LinearMap.ker SC.g.hom := by
    change (KC.d 2 ((ComplexShape.down ℕ).next 2)).hom (qToCChainGroup X 2 c) = 0
    rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1]
    exact boundary_qToCChainGroup X 1 c |>.trans (by rw [hc, map_zero])
  let zC : LinearMap.ker SC.g.hom := ⟨qToCChainGroup X 2 c, hcC⟩
  change qToCHomology X 2 (SQ.moduleCatHomologyClass zQ) =
    SC.moduleCatHomologyClass zC
  have hQclass := ConcreteCategory.congr_hom SQ.moduleCatCyclesIso_inv_π zQ
  have hCclass := ConcreteCategory.congr_hom SC.moduleCatCyclesIso_inv_π zC
  have hQclass' : SQ.moduleCatHomologyClass zQ =
      SQ.homologyπ.hom (SQ.moduleCatCyclesIso.inv.hom zQ) := by
    change SQ.moduleCatHomologyIso.inv.hom
      ((LinearMap.range SQ.moduleCatToCycles).mkQ zQ) = _
    change SQ.homologyπ.hom (SQ.moduleCatCyclesIso.inv.hom zQ) =
      SQ.moduleCatHomologyIso.inv.hom
        ((LinearMap.range SQ.moduleCatToCycles).mkQ zQ) at hQclass
    exact hQclass.symm
  have hCclass' : SC.moduleCatHomologyClass zC =
      SC.homologyπ.hom (SC.moduleCatCyclesIso.inv.hom zC) := by
    change SC.moduleCatHomologyIso.inv.hom
      ((LinearMap.range SC.moduleCatToCycles).mkQ zC) = _
    change SC.homologyπ.hom (SC.moduleCatCyclesIso.inv.hom zC) =
      SC.moduleCatHomologyIso.inv.hom
        ((LinearMap.range SC.moduleCatToCycles).mkQ zC) at hCclass
    exact hCclass.symm
  change qToCHomology X 2 (SQ.moduleCatHomologyClass zQ) =
    SC.moduleCatHomologyClass zC
  rw [hQclass', hCclass']
  have hchosen : (SC.homologyData.left.homologyIso).hom = 𝟙 SC.homology := by
    let e := ShortComplex.leftHomologyMapIso' (Iso.refl SC)
      SC.leftHomologyData SC.homologyData.left
    change e.inv ≫ e.hom = 𝟙 _
    exact e.inv_hom_id
  have hπ := ConcreteCategory.congr_hom
    (homologyπ_comp_qToCHomology X 2)
    (SQ.moduleCatCyclesIso.inv.hom zQ)
  have hπ' : qToCHomology X 2
      (SQ.homologyπ.hom (SQ.moduleCatCyclesIso.inv.hom zQ)) =
      ((SC.homologyData.left.map
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).π).hom
        (qToCCycles X 2 (SQ.moduleCatCyclesIso.inv.hom zQ)) := by
    change qToCHomology X 2
      (SQ.homologyπ.hom (SQ.moduleCatCyclesIso.inv.hom zQ)) = _ at hπ
    exact hπ
  have hcycles : qToCCycles X 2 (SQ.moduleCatCyclesIso.inv.hom zQ) =
      SC.homologyData.left.cyclesIso.hom
        (SC.moduleCatCyclesIso.inv.hom zC) := by
    apply (ModuleCat.mono_iff_injective SC.homologyData.left.i).mp
      (Limits.mono_of_isLimit_fork SC.homologyData.left.hi)
    have hleft := DFunLike.congr_fun (iCycles_comp_qToCChainGroup X 2)
      (SQ.moduleCatCyclesIso.inv.hom zQ)
    change SC.homologyData.left.i.hom
        (qToCCycles X 2 (SQ.moduleCatCyclesIso.inv.hom zQ)) =
      SC.homologyData.left.i.hom
        (SC.homologyData.left.cyclesIso.hom
          (SC.moduleCatCyclesIso.inv.hom zC))
    change qToCChainGroup X 2
        (SQ.iCycles.hom (SQ.moduleCatCyclesIso.inv.hom zQ)) =
      SC.homologyData.left.i.hom
        (qToCCycles X 2 (SQ.moduleCatCyclesIso.inv.hom zQ)) at hleft
    have hQinc := ConcreteCategory.congr_hom
      SQ.moduleCatCyclesIso_inv_iCycles zQ
    have hCinc := ConcreteCategory.congr_hom
      SC.moduleCatCyclesIso_inv_iCycles zC
    have hDinc := ConcreteCategory.congr_hom
      SC.homologyData.left.cyclesIso_hom_comp_i
      (SC.moduleCatCyclesIso.inv.hom zC)
    have hQinc' : SQ.iCycles.hom (SQ.moduleCatCyclesIso.inv.hom zQ) = c := by
      change SQ.iCycles.hom (SQ.moduleCatCyclesIso.inv.hom zQ) = c at hQinc
      exact hQinc
    have hCinc' : SC.iCycles.hom (SC.moduleCatCyclesIso.inv.hom zC) =
        qToCChainGroup X 2 c := by
      change SC.iCycles.hom (SC.moduleCatCyclesIso.inv.hom zC) =
        qToCChainGroup X 2 c at hCinc
      exact hCinc
    have hDinc' : SC.homologyData.left.i.hom
          (SC.homologyData.left.cyclesIso.hom
            (SC.moduleCatCyclesIso.inv.hom zC)) =
        SC.iCycles.hom (SC.moduleCatCyclesIso.inv.hom zC) := by
      change SC.homologyData.left.i.hom
          (SC.homologyData.left.cyclesIso.hom
            (SC.moduleCatCyclesIso.inv.hom zC)) =
        SC.iCycles.hom (SC.moduleCatCyclesIso.inv.hom zC) at hDinc
      exact hDinc
    rw [← hleft, hQinc', hDinc', hCinc']
  rw [hπ', hcycles]
  have hrel := ConcreteCategory.congr_hom
    SC.homologyData.left.homologyπ_comp_homologyIso_hom
    (SC.moduleCatCyclesIso.inv.hom zC)
  change SC.homologyData.left.π.hom
      (SC.homologyData.left.cyclesIso.hom
        (SC.moduleCatCyclesIso.inv.hom zC)) =
    SC.homologyπ.hom (SC.moduleCatCyclesIso.inv.hom zC)
  change SC.homologyData.left.homologyIso.hom
      (SC.homologyπ.hom (SC.moduleCatCyclesIso.inv.hom zC)) =
    SC.homologyData.left.π.hom
      (SC.homologyData.left.cyclesIso.hom
        (SC.moduleCatCyclesIso.inv.hom zC)) at hrel
  rw [hchosen] at hrel
  exact hrel.symm

/-- A continuous map sends the class of an explicit two-cycle to the class of its image
two-cycle. -/
lemma homologyMap_homologyClassOfTwoCycle
    (R : Type) [Field R] {X Y : TopCat} (f : X ⟶ Y)
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 2)
    (hc : Simplicial.boundary R 1 c = 0) :
    homologyMap R 2 f (Simplicial.homologyClassOfTwoCycle R c hc) =
      Simplicial.homologyClassOfTwoCycle R
        (((SSet.chainComplexMap (TopCat.toSSet.map f)
          (ModuleCat.of R R)).f 2).hom c)
        (by
          have h := ConcreteCategory.congr_hom
            ((SSet.chainComplexMap (TopCat.toSSet.map f)
              (ModuleCat.of R R)).comm 2 1) c
          change _ = 0
          rw [show Simplicial.boundary R 1
              (((SSet.chainComplexMap (TopCat.toSSet.map f)
                (ModuleCat.of R R)).f 2).hom c) =
              (((SSet.chainComplexMap (TopCat.toSSet.map f)
                (ModuleCat.of R R)).f 1).hom
                (Simplicial.boundary R 1 c)) by
              simpa only [Simplicial.boundary, ConcreteCategory.comp_apply] using h,
            hc, map_zero]) := by
  let KX := (TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)
  let KY := (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)
  let F := SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)
  let SX := KX.sc 2
  let SY := KY.sc 2
  have hcX : c ∈ LinearMap.ker SX.g.hom := by
    change (KX.d 2 ((ComplexShape.down ℕ).next 2)).hom c = 0
    rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1]
    exact hc
  let zX : LinearMap.ker SX.g.hom := ⟨c, hcX⟩
  let cY : Simplicial.ChainGroup R (TopCat.toSSet.obj Y) 2 := (F.f 2).hom c
  have hcY : cY ∈ LinearMap.ker SY.g.hom := by
    change (KY.d 2 ((ComplexShape.down ℕ).next 2)).hom cY = 0
    rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1]
    have h := ConcreteCategory.congr_hom (F.comm 2 1) c
    have hc' : (KX.d 2 1).hom c = 0 := hc
    change (KY.d 2 1).hom ((F.f 2).hom c) = 0
    rw [show (KY.d 2 1).hom ((F.f 2).hom c) =
        (F.f 1).hom ((KX.d 2 1).hom c) by
      simpa only [ConcreteCategory.comp_apply] using h,
      hc', map_zero]
  let zY : LinearMap.ker SY.g.hom := ⟨cY, hcY⟩
  let SF := (HomologicalComplex.shortComplexFunctor
    (ModuleCat R) (ComplexShape.down ℕ) 2).map F
  have hnat := ShortComplex.moduleCatHomologyClass_naturality SF zX
  change (HomologicalComplex.homologyMap F 2).hom
      (SX.moduleCatHomologyClass zX) = SY.moduleCatHomologyClass zY
  rw [show (HomologicalComplex.homologyMap F 2).hom
      (SX.moduleCatHomologyClass zX) =
        SY.moduleCatHomologyClass (ShortComplex.moduleCatCycleMap SF zX) by
      exact hnat]
  congr 1

/-- Every rational degree-two homology class has an explicit cycle representative. -/
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

/-- Rational-to-complex extension of degree-two homology commutes with every continuous map. -/
theorem qToCHomology_naturality_degreeTwo {X Y : TopCat} (f : X ⟶ Y)
    (z : Homology ℚ X 2) :
    homologyMap ℂ 2 f (qToCHomology X 2 z) =
      qToCHomology Y 2 (homologyMap ℚ 2 f z) := by
  obtain ⟨c, hc, rfl⟩ := exists_rationalTwoCycleRepresenting X z
  rw [qToCHomology_homologyClassOfTwoCycle]
  rw [homologyMap_homologyClassOfTwoCycle]
  rw [homologyMap_homologyClassOfTwoCycle]
  rw [qToCHomology_homologyClassOfTwoCycle]
  congr 1
  exact DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom (qToCChainGroup_naturality f 2)) c

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rational-to-complex extension of degree-two cohomology commutes with pullback along every
continuous map. -/
theorem rationalToComplexCohomologyMap_naturality_degreeTwo
    {X Y : TopCat} (f : X ⟶ Y) (beta : Cohomology ℚ Y 2) :
    rationalToComplexCohomologyMap X 2 (cohomologyMap ℚ 2 f beta) =
      cohomologyMap ℂ 2 f (rationalToComplexCohomologyMap Y 2 beta) := by
  apply LinearMap.ext
  intro w
  apply (qToCHomology_isBaseChange X 2).inductionOn w
    (fun w =>
      rationalToComplexCohomologyMap X 2 (cohomologyMap ℚ 2 f beta) w =
        cohomologyMap ℂ 2 f (rationalToComplexCohomologyMap Y 2 beta) w)
  · simp
  · intro z
    rw [cohomologyMap_apply, qToCHomology_naturality_degreeTwo]
    exact ((qToCHomology_isBaseChange X 2).toDual_comp_apply
      (cohomologyMap ℚ 2 f beta) z).trans
        ((qToCHomology_isBaseChange Y 2).toDual_comp_apply beta
          (homologyMap ℚ 2 f z)).symm
  · intro a z hz
    simp [hz]
  · intro x y hx hy
    simp [hx, hy]

/-- The degree-one external cohomology class evaluates on an explicitly represented
two-cycle by evaluating its defining cocycle. -/
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rational-to-complex coefficient extension commutes with the explicit
degree-`(1,1)` external product on singular cohomology. -/
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

end AlgebraicTopology.Singular
