/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticCMTopology
public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceRationalSingularClass
public import Other.AlgebraicTopology.SingularOrderFourProjector

/-!
# The CM detector on the explicit elliptic surface

This file identifies the two algebraic CM endomorphisms of the explicit surface with
the corresponding factor maps under the product homeomorphism.  It then specializes
the elementary singular-cohomology CM detector to the concrete rational curve class
used to construct the candidate surface class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicTopology

universe u

namespace AlgebraicTopology.Simplicial

variable (R : Type u) [Field R]

/-- The homology class represented by an explicit singular one-cycle. -/
noncomputable def homologyClassOfOneCycle {X : SSet.{u}}
    (c : ChainGroup R X 1) (hc : boundary R 0 c = 0) :
    (X.chainComplex (ModuleCat.of R R)).homology 1 := by
  let K := X.chainComplex (ModuleCat.of R R)
  let S := K.sc 1
  have hc' : c ∈ LinearMap.ker S.g.hom := by
    change (K.d 1 ((ComplexShape.down ℕ).next 1)).hom c = 0
    rw [show (ComplexShape.down ℕ).next 1 = 0 from
      ChainComplex.next_nat_succ 0]
    exact hc
  exact S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk ⟨c, hc'⟩)

/-- Evaluation of a represented degree-one cohomology class on a represented
degree-one homology class is the original cochain-chain pairing. -/
theorem cochainClassOfOneCocycle_pair {X : SSet.{u}}
    (phi : Cochain R X 1) (hphi : coboundary R 1 phi = 0)
    (c : ChainGroup R X 1) (hc : boundary R 0 c = 0) :
    let S := (X.chainComplex (ModuleCat.of R R)).sc 1
    S.linearDualHomologyEquiv (cochainClassOfOneCocycle R phi hphi)
      (homologyClassOfOneCycle R c hc) = phi c := by
  dsimp only
  let K := X.chainComplex (ModuleCat.of R R)
  let S := K.sc 1
  have hc' : c ∈ LinearMap.ker S.g.hom := by
    change (K.d 1 ((ComplexShape.down ℕ).next 1)).hom c = 0
    rw [show (ComplexShape.down ℕ).next 1 = 0 from
      ChainComplex.next_nat_succ 0]
    exact hc
  have hphi' : phi ∈ LinearMap.ker S.f.hom.dualMap := by
    change S.f.hom.dualMap phi = 0
    apply LinearMap.ext
    intro b
    rw [LinearMap.zero_apply]
    let hprev : (ComplexShape.down ℕ).prev 1 = 2 := ChainComplex.prev ℕ 1
    let b' : ChainGroup R X 2 := (K.XIsoOfEq hprev).hom.hom b
    have hd := ConcreteCategory.congr_hom
      (K.XIsoOfEq_hom_comp_d hprev 1) b
    have hv := LinearMap.congr_fun hphi b'
    rw [coboundary_apply] at hv
    change phi (S.f.hom b) = 0
    change phi ((K.d ((ComplexShape.down ℕ).prev 1) 1).hom b) = 0
    rw [← show (K.d 2 1).hom ((K.XIsoOfEq hprev).hom.hom b) =
      (K.d ((ComplexShape.down ℕ).prev 1) 1).hom b from hd]
    exact hv
  let z : LinearMap.ker S.g.hom := ⟨c, hc'⟩
  let eta : LinearMap.ker S.f.hom.dualMap := ⟨phi, hphi'⟩
  change S.linearDualHomologyEquiv (S.linearDual.moduleCatHomologyClass eta)
      (S.moduleCatHomologyClass z) = phi c
  exact S.linearDualHomologyEquiv_class_apply_class eta z

end AlgebraicTopology.Simplicial

namespace AlgebraicTopology.Singular

local instance surfaceCMProjectorRatModule (X : TopCat) (n : ℕ) :
    Module ℚ ((CChains X).homology n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance surfaceCMProjectorRatScalarTower (X : TopCat) (n : ℕ) :
    IsScalarTower ℚ ℂ ((CChains X).homology n) :=
  IsScalarTower.of_compHom ℚ ℂ _

/-- Extending coefficients sends the class of a rational singular one-cycle to
the class of its coefficient-extended complex one-cycle. -/
theorem qToCHomology_homologyClassOfOneCycle (X : TopCat)
    (c : Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) 1)
    (hc : Simplicial.boundary ℚ 0 c = 0) :
    qToCHomology X 1 (Simplicial.homologyClassOfOneCycle ℚ c hc) =
      Simplicial.homologyClassOfOneCycle ℂ (qToCChainGroup X 1 c)
        (by rw [boundary_qToCChainGroup X 0 c, hc, map_zero]) := by
  let KQ := QChains X
  let KC := CChains X
  let SQ := KQ.sc 1
  let SC := KC.sc 1
  have hcQ : c ∈ LinearMap.ker SQ.g.hom := by
    change (KQ.d 1 ((ComplexShape.down ℕ).next 1)).hom c = 0
    rw [show (ComplexShape.down ℕ).next 1 = 0 from
      ChainComplex.next_nat_succ 0]
    exact hc
  let zQ : LinearMap.ker SQ.g.hom := ⟨c, hcQ⟩
  have hcC : qToCChainGroup X 1 c ∈ LinearMap.ker SC.g.hom := by
    change (KC.d 1 ((ComplexShape.down ℕ).next 1)).hom
      (qToCChainGroup X 1 c) = 0
    rw [show (ComplexShape.down ℕ).next 1 = 0 from
      ChainComplex.next_nat_succ 0]
    exact boundary_qToCChainGroup X 0 c |>.trans (by rw [hc, map_zero])
  let zC : LinearMap.ker SC.g.hom := ⟨qToCChainGroup X 1 c, hcC⟩
  change qToCHomology X 1 (SQ.moduleCatHomologyClass zQ) =
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
  rw [hQclass', hCclass']
  have hchosen : (SC.homologyData.left.homologyIso).hom = 𝟙 SC.homology := by
    let e := ShortComplex.leftHomologyMapIso' (Iso.refl SC)
      SC.leftHomologyData SC.homologyData.left
    change e.inv ≫ e.hom = 𝟙 _
    exact e.inv_hom_id
  have hπ := ConcreteCategory.congr_hom
    (homologyπ_comp_qToCHomology X 1)
    (SQ.moduleCatCyclesIso.inv.hom zQ)
  have hπ' : qToCHomology X 1
      (SQ.homologyπ.hom (SQ.moduleCatCyclesIso.inv.hom zQ)) =
      ((SC.homologyData.left.map
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).π).hom
        (qToCCycles X 1 (SQ.moduleCatCyclesIso.inv.hom zQ)) := by
    change qToCHomology X 1
      (SQ.homologyπ.hom (SQ.moduleCatCyclesIso.inv.hom zQ)) = _ at hπ
    exact hπ
  have hcycles : qToCCycles X 1 (SQ.moduleCatCyclesIso.inv.hom zQ) =
      SC.homologyData.left.cyclesIso.hom
        (SC.moduleCatCyclesIso.inv.hom zC) := by
    apply (ModuleCat.mono_iff_injective SC.homologyData.left.i).mp
      (Limits.mono_of_isLimit_fork SC.homologyData.left.hi)
    have hleft := DFunLike.congr_fun (iCycles_comp_qToCChainGroup X 1)
      (SQ.moduleCatCyclesIso.inv.hom zQ)
    change SC.homologyData.left.i.hom
        (qToCCycles X 1 (SQ.moduleCatCyclesIso.inv.hom zQ)) =
      SC.homologyData.left.i.hom
        (SC.homologyData.left.cyclesIso.hom
          (SC.moduleCatCyclesIso.inv.hom zC))
    change qToCChainGroup X 1
        (SQ.iCycles.hom (SQ.moduleCatCyclesIso.inv.hom zQ)) =
      SC.homologyData.left.i.hom
        (qToCCycles X 1 (SQ.moduleCatCyclesIso.inv.hom zQ)) at hleft
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
        qToCChainGroup X 1 c := by
      change SC.iCycles.hom (SC.moduleCatCyclesIso.inv.hom zC) =
        qToCChainGroup X 1 c at hCinc
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

/-- Every rational degree-one singular homology class has a one-cycle
representative in the selected chain model. -/
theorem exists_rationalOneCycleRepresenting (X : TopCat)
    (z : Homology ℚ X 1) :
    ∃ (c : Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) 1)
      (hc : Simplicial.boundary ℚ 0 c = 0),
      Simplicial.homologyClassOfOneCycle ℚ c hc = z := by
  let K := QChains X
  let S := K.sc 1
  obtain ⟨eta, heta⟩ := S.moduleCatHomologyClass_surjective z
  have hc : Simplicial.boundary ℚ 0 eta.1 = 0 := by
    change (K.d 1 0).hom eta.1 = 0
    have hetaCycle := eta.2
    change (K.d 1 ((ComplexShape.down ℕ).next 1)).hom eta.1 = 0 at hetaCycle
    rw [show (ComplexShape.down ℕ).next 1 = 0 from
      ChainComplex.next_nat_succ 0] at hetaCycle
    exact hetaCycle
  refine ⟨eta.1, hc, ?_⟩
  change S.moduleCatHomologyClass eta = z
  exact heta

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coefficient extension carries the class represented by a rational one-cocycle
to the class represented by its pointwise complexification. -/
theorem rationalToComplexCohomologyMap_cochainClassOfOneCocycle
    (X : TopCat)
    (phi : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) 1)
    (hphi : Simplicial.coboundary ℚ 1 phi = 0) :
    rationalToComplexCohomologyMap X 1
        (((QChains X).sc 1).linearDualHomologyEquiv
          (Simplicial.cochainClassOfOneCocycle ℚ phi hphi)) =
      ((CChains X).sc 1).linearDualHomologyEquiv
        (Simplicial.cochainClassOfOneCocycle ℂ
          (qToCSingularCochain X 1 phi)
          (by rw [← qToCSingularCochain_coboundary X 1 phi,
            hphi, map_zero])) := by
  let beta : Cohomology ℚ X 1 :=
    ((QChains X).sc 1).linearDualHomologyEquiv
      (Simplicial.cochainClassOfOneCocycle ℚ phi hphi)
  let hphiC : Simplicial.coboundary ℂ 1
      (qToCSingularCochain X 1 phi) = 0 := by
    rw [← qToCSingularCochain_coboundary X 1 phi, hphi, map_zero]
  let betaC : Cohomology ℂ X 1 :=
    ((CChains X).sc 1).linearDualHomologyEquiv
      (Simplicial.cochainClassOfOneCocycle ℂ
        (qToCSingularCochain X 1 phi) hphiC)
  change rationalToComplexCohomologyMap X 1 beta = betaC
  apply LinearMap.ext
  intro w
  apply (qToCHomology_isBaseChange X 1).inductionOn w
    (fun w => rationalToComplexCohomologyMap X 1 beta w = betaC w)
  · simp
  · intro z
    obtain ⟨c, hc, rfl⟩ := exists_rationalOneCycleRepresenting X z
    let zQ := Simplicial.homologyClassOfOneCycle ℚ c hc
    have hdual : rationalToComplexCohomologyMap X 1 beta
        (qToCHomology X 1 zQ) = algebraMap ℚ ℂ (beta zQ) :=
      (qToCHomology_isBaseChange X 1).toDual_comp_apply beta zQ
    change rationalToComplexCohomologyMap X 1 beta
        (qToCHomology X 1 zQ) = betaC (qToCHomology X 1 zQ)
    calc
      _ = algebraMap ℚ ℂ (beta zQ) := hdual
      _ = algebraMap ℚ ℂ (phi c) := by
        rw [show beta zQ = phi c by
          exact Simplicial.cochainClassOfOneCocycle_pair ℚ phi hphi c hc]
      _ = qToCSingularCochain X 1 phi (qToCChainGroup X 1 c) := by
        rw [qToCSingularCochain_apply_qToCChain]
      _ = betaC
          (Simplicial.homologyClassOfOneCycle ℂ (qToCChainGroup X 1 c)
            (by rw [boundary_qToCChainGroup X 0 c, hc, map_zero])) := by
        symm
        exact Simplicial.cochainClassOfOneCocycle_pair ℂ
          (qToCSingularCochain X 1 phi) hphiC
          (qToCChainGroup X 1 c)
          (by rw [boundary_qToCChainGroup X 0 c, hc, map_zero])
      _ = betaC (qToCHomology X 1 zQ) := by
        rw [qToCHomology_homologyClassOfOneCycle]
  · intro a z hz
    simp [hz]
  · intro x y hx hy
    simp [hx, hy]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rational-to-complex coefficient extension commutes with the canonical
degree-`(1,1)` external product of two specified nonzero classes. -/
theorem rationalToComplexCohomologyMap_degreeOneExternalCohomologyClassOfNonzero
    {X Y : TopCat}
    (alpha : Cohomology ℚ X 1) (beta : Cohomology ℚ Y 1)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) :
    rationalToComplexCohomologyMap (X ⊗ Y) 2
        (degreeOneExternalCohomologyClassOfNonzero ℚ
          alpha beta halpha hbeta) =
      degreeOneExternalCohomologyBilinear ℂ X Y
        (rationalToComplexCohomologyMap X 1 alpha)
        (rationalToComplexCohomologyMap Y 1 beta) := by
  let a := oneCycleCocycleRepresentativePairingOfNonzero ℚ alpha halpha
  let b := oneCycleCocycleRepresentativePairingOfNonzero ℚ beta hbeta
  change rationalToComplexCohomologyMap (X ⊗ Y) 2
      (degreeOneExternalCohomologyClass ℚ a.cochain b.cochain
        a.coboundary_eq_zero b.coboundary_eq_zero) = _
  rw [rationalToComplexCohomologyMap_degreeOneExternalCohomologyClass]
  rw [← degreeOneExternalCohomologyBilinear_represented]
  rw [← rationalToComplexCohomologyMap_cochainClassOfOneCocycle
      X a.cochain a.coboundary_eq_zero,
    ← rationalToComplexCohomologyMap_cochainClassOfOneCocycle
      Y b.cochain b.coboundary_eq_zero]
  rw [a.represents, b.represents]

/-- The double-minus detector applied to an unprojected complexified rational
external product is `-4` times the simple doubly projected class.  This identity
does not use a square or fourth-power relation for either self-map. -/
theorem productCMDoubleMinusEnd_externalRationalClass
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology ℚ X 1) (beta : Cohomology ℚ Y 1) :
    productCMDoubleMinusEnd X Y f g
        (degreeOneExternalCohomologyBilinear ℂ X Y
          (rationalToComplexCohomologyMap X 1 alpha)
          (rationalToComplexCohomologyMap Y 1 beta)) =
      (-4 : ℂ) • continuousCMMinusExternalClass X Y f g alpha beta := by
  rw [productCMDoubleMinusEnd, LinearMap.comp_apply]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    firstFactorCohomologyEnd, secondFactorCohomologyEnd,
    degreeOneExternalCohomologyBilinear_naturality,
    cohomologyMap_id, LinearMap.id_apply]
  simp only [continuousCMMinusExternalClass, continuousCMMinusPart,
    LinearAlgebra.cmMinusPart]
  simp only [map_add, map_sub, map_smul, smul_add, smul_sub, smul_smul]
  simp only [firstFactorCohomologyEnd,
    degreeOneExternalCohomologyBilinear_naturality,
    cohomologyMap_id, LinearMap.id_apply, continuousCohomologyEnd]
  simp only [LinearMap.add_apply, LinearMap.smul_apply,
    map_add, map_sub, map_smul, smul_add, smul_sub, smul_smul]
  simp only [Complex.I_mul_I]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq]

theorem productCMDoubleMinusEnd_externalRationalClass_ne_zero
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology ℚ X 1) (beta : Cohomology ℚ Y 1)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) :
    productCMDoubleMinusEnd X Y f g
        (degreeOneExternalCohomologyBilinear ℂ X Y
          (rationalToComplexCohomologyMap X 1 alpha)
          (rationalToComplexCohomologyMap Y 1 beta)) ≠ 0 := by
  rw [productCMDoubleMinusEnd_externalRationalClass]
  exact smul_ne_zero (by norm_num)
    (continuousCMMinusExternalClass_ne_zero X Y f g alpha beta halpha hbeta)

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ExplicitEllipticCandidate

/-- The curve CM map with its source and target expressed in the singular-cohomology
topological-space abbreviation. -/
def curveCMTopologicalMap : curveAnalyticSpace ⟶ curveAnalyticSpace :=
  @TopCat.ofHom (ComplexPoint curveVariety) (ComplexPoint curveVariety)
    Point.analyticTopology Point.analyticTopology
    (Point.continuousMap curveVarietyCMEnd)

/-- First-factor surface CM with its source and target expressed in the
singular-cohomology topological-space abbreviation. -/
def surfaceFirstCMTopologicalMap : surfaceAnalyticSpace ⟶ surfaceAnalyticSpace :=
  @TopCat.ofHom (ComplexPoint surfaceVariety) (ComplexPoint surfaceVariety)
    Point.analyticTopology Point.analyticTopology
    (Point.continuousMap surfaceVarietyFirstCMEnd)

/-- Second-factor surface CM with its source and target expressed in the
singular-cohomology topological-space abbreviation. -/
def surfaceSecondCMTopologicalMap : surfaceAnalyticSpace ⟶ surfaceAnalyticSpace :=
  @TopCat.ofHom (ComplexPoint surfaceVariety) (ComplexPoint surfaceVariety)
    Point.analyticTopology Point.analyticTopology
    (Point.continuousMap surfaceVarietySecondCMEnd)

theorem curveCMTopologicalMap_eq : curveCMTopologicalMap = curveCMAnalyticMap := by
  rfl

theorem surfaceFirstCMTopologicalMap_eq :
    surfaceFirstCMTopologicalMap = surfaceFirstCMAnalyticMap := by
  rfl

theorem surfaceSecondCMTopologicalMap_eq :
    surfaceSecondCMTopologicalMap = surfaceSecondCMAnalyticMap := by
  rfl

/-- Under the point-product homeomorphism, first-factor CM on the surface is CM on
the first curve coordinate and the identity on the second. -/
theorem surfaceAnalyticProductIso_intertwines_firstCM :
    surfaceFirstCMAnalyticMap ≫ surfaceAnalyticProductIso.hom =
      surfaceAnalyticProductIso.hom ≫
        (curveCMAnalyticMap ⊗ₘ 𝟙 curveAnalyticSpace) := by
  ext : 1
  · ext z : 1
    change ComplexPoint surfaceVariety at z
    simp only [Category.comp_apply]
    change Point.map surfaceVarietyFst
        (Point.map surfaceVarietyFirstCMEnd z) =
      Point.map curveVarietyCMEnd (Point.map surfaceVarietyFst z)
    rw [← Point.map_comp_apply, surfaceVarietyFirstCMEnd_fst,
      Point.map_comp_apply]
  · ext z : 1
    change ComplexPoint surfaceVariety at z
    simp only [Category.comp_apply]
    change Point.map surfaceVarietySnd
        (Point.map surfaceVarietyFirstCMEnd z) =
      Point.map surfaceVarietySnd z
    rw [← Point.map_comp_apply, surfaceVarietyFirstCMEnd_snd]

/-- Under the point-product homeomorphism, second-factor CM on the surface is the
identity on the first curve coordinate and CM on the second. -/
theorem surfaceAnalyticProductIso_intertwines_secondCM :
    surfaceSecondCMAnalyticMap ≫ surfaceAnalyticProductIso.hom =
      surfaceAnalyticProductIso.hom ≫
        (𝟙 curveAnalyticSpace ⊗ₘ curveCMAnalyticMap) := by
  ext : 1
  · ext z : 1
    change ComplexPoint surfaceVariety at z
    simp only [Category.comp_apply]
    change Point.map surfaceVarietyFst
        (Point.map surfaceVarietySecondCMEnd z) =
      Point.map surfaceVarietyFst z
    rw [← Point.map_comp_apply, surfaceVarietySecondCMEnd_fst]
  · ext z : 1
    change ComplexPoint surfaceVariety at z
    simp only [Category.comp_apply]
    change Point.map surfaceVarietySnd
        (Point.map surfaceVarietySecondCMEnd z) =
      Point.map curveVarietyCMEnd (Point.map surfaceVarietySnd z)
    rw [← Point.map_comp_apply, surfaceVarietySecondCMEnd_snd,
      Point.map_comp_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem surfaceAnalyticProductIso_inv_intertwines_firstCM :
    surfaceAnalyticProductIso.inv ≫ surfaceFirstCMAnalyticMap =
      (curveCMAnalyticMap ⊗ₘ 𝟙 curveAnalyticSpace) ≫
        surfaceAnalyticProductIso.inv := by
  rw [← cancel_mono surfaceAnalyticProductIso.hom]
  rw [Category.assoc, surfaceAnalyticProductIso_intertwines_firstCM]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem surfaceAnalyticProductIso_inv_intertwines_secondCM :
    surfaceAnalyticProductIso.inv ≫ surfaceSecondCMAnalyticMap =
      (𝟙 curveAnalyticSpace ⊗ₘ curveCMAnalyticMap) ≫
        surfaceAnalyticProductIso.inv := by
  rw [← cancel_mono surfaceAnalyticProductIso.hom]
  rw [Category.assoc, surfaceAnalyticProductIso_intertwines_secondCM]
  simp

theorem surfaceAnalyticProductIso_intertwines_firstCM_topological :
    surfaceFirstCMTopologicalMap ≫ surfaceAnalyticProductIso.hom =
      surfaceAnalyticProductIso.hom ≫
        (curveCMTopologicalMap ⊗ₘ 𝟙 curveAnalyticSpace) := by
  ext : 1
  · ext z : 1
    change ComplexPoint surfaceVariety at z
    change Point.map surfaceVarietyFst
        (Point.map surfaceVarietyFirstCMEnd z) =
      Point.map curveVarietyCMEnd (Point.map surfaceVarietyFst z)
    rw [← Point.map_comp_apply, surfaceVarietyFirstCMEnd_fst,
      Point.map_comp_apply]
  · ext z : 1
    change ComplexPoint surfaceVariety at z
    change Point.map surfaceVarietySnd
        (Point.map surfaceVarietyFirstCMEnd z) =
      Point.map surfaceVarietySnd z
    rw [← Point.map_comp_apply, surfaceVarietyFirstCMEnd_snd]

theorem surfaceAnalyticProductIso_intertwines_secondCM_topological :
    surfaceSecondCMTopologicalMap ≫ surfaceAnalyticProductIso.hom =
      surfaceAnalyticProductIso.hom ≫
        (𝟙 curveAnalyticSpace ⊗ₘ curveCMTopologicalMap) := by
  ext : 1
  · ext z : 1
    change ComplexPoint surfaceVariety at z
    change Point.map surfaceVarietyFst
        (Point.map surfaceVarietySecondCMEnd z) =
      Point.map surfaceVarietyFst z
    rw [← Point.map_comp_apply, surfaceVarietySecondCMEnd_fst]
  · ext z : 1
    change ComplexPoint surfaceVariety at z
    change Point.map surfaceVarietySnd
        (Point.map surfaceVarietySecondCMEnd z) =
      Point.map curveVarietyCMEnd (Point.map surfaceVarietySnd z)
    rw [← Point.map_comp_apply, surfaceVarietySecondCMEnd_snd,
      Point.map_comp_apply]

theorem surfaceAnalyticProductIso_inv_intertwines_firstCM_topological :
    surfaceAnalyticProductIso.inv ≫ surfaceFirstCMTopologicalMap =
      (curveCMTopologicalMap ⊗ₘ 𝟙 curveAnalyticSpace) ≫
        surfaceAnalyticProductIso.inv := by
  rw [← cancel_mono surfaceAnalyticProductIso.hom]
  rw [Category.assoc, surfaceAnalyticProductIso_intertwines_firstCM_topological]
  simp

theorem surfaceAnalyticProductIso_inv_intertwines_secondCM_topological :
    surfaceAnalyticProductIso.inv ≫ surfaceSecondCMTopologicalMap =
      (𝟙 curveAnalyticSpace ⊗ₘ curveCMTopologicalMap) ≫
        surfaceAnalyticProductIso.inv := by
  rw [← cancel_mono surfaceAnalyticProductIso.hom]
  rw [Category.assoc, surfaceAnalyticProductIso_intertwines_secondCM_topological]
  simp

/-! ## The detector on the named candidate -/

/-- The particular nonzero rational degree-one class selected from the invariant
elliptic differential. -/
def explicitCurveRationalOneClass :
    Singular.Cohomology ℚ curveAnalyticSpace 1 :=
  curveRationalOneClassOfComplexNonzero curveComplexSingularClass
    curveComplexSingularClass_ne_zero

theorem explicitCurveRationalOneClass_ne_zero :
    explicitCurveRationalOneClass ≠ 0 :=
  curveRationalOneClassOfComplexNonzero_ne_zero curveComplexSingularClass
    curveComplexSingularClass_ne_zero

/-- After transport to the topological product, the complexification of the named
rational surface class is the canonical external product of the complexified
rational curve class with itself. -/
theorem explicitSurfaceComplexifiedExternalTwoClass_product :
    Singular.cohomologyLinearEquivOfIso ℂ surfaceAnalyticProductIso 2
        explicitSurfaceComplexifiedExternalTwoClass =
      Singular.degreeOneExternalCohomologyBilinear ℂ
        curveAnalyticSpace curveAnalyticSpace
        (Singular.rationalToComplexCohomologyMap curveAnalyticSpace 1
          explicitCurveRationalOneClass)
        (Singular.rationalToComplexCohomologyMap curveAnalyticSpace 1
          explicitCurveRationalOneClass) := by
  rw [explicitSurfaceComplexifiedExternalTwoClass,
    explicitSurfaceRationalExternalTwoClass,
    surfaceRationalExternalTwoClass_toComplex]
  rw [LinearEquiv.apply_symm_apply]
  rw [← curveProductRationalExternalTwoClass_toComplex]
  exact Singular.rationalToComplexCohomologyMap_degreeOneExternalCohomologyClassOfNonzero
    explicitCurveRationalOneClass explicitCurveRationalOneClass
    explicitCurveRationalOneClass_ne_zero explicitCurveRationalOneClass_ne_zero

/-- The double-minus CM detector is nonzero on the product-coordinate form of the
named candidate.  This needs no assumption on the square of the CM action. -/
theorem productCMDoubleMinusEnd_explicitSurfaceClass_ne_zero :
    Singular.productCMDoubleMinusEnd curveAnalyticSpace curveAnalyticSpace
        curveCMTopologicalMap curveCMTopologicalMap
        (Singular.cohomologyLinearEquivOfIso ℂ surfaceAnalyticProductIso 2
          explicitSurfaceComplexifiedExternalTwoClass) ≠ 0 := by
  rw [explicitSurfaceComplexifiedExternalTwoClass_product]
  exact Singular.productCMDoubleMinusEnd_externalRationalClass_ne_zero
    curveAnalyticSpace curveAnalyticSpace curveCMTopologicalMap curveCMTopologicalMap
    explicitCurveRationalOneClass explicitCurveRationalOneClass
    explicitCurveRationalOneClass_ne_zero explicitCurveRationalOneClass_ne_zero

/-- The double-minus detector formed directly from the two algebraic CM maps of
the actual surface. -/
def surfaceCMDoubleMinusEnd :
    Module.End ℂ (Singular.Cohomology ℂ surfaceAnalyticSpace 2) :=
  (Singular.cohomologyMap ℂ 2 surfaceFirstCMTopologicalMap -
      Complex.I • LinearMap.id).comp
    (Singular.cohomologyMap ℂ 2 surfaceSecondCMTopologicalMap -
      Complex.I • LinearMap.id)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem surfaceProductCohomologyEquiv_firstCM
    (x : Singular.Cohomology ℂ surfaceAnalyticSpace 2) :
    Singular.cohomologyLinearEquivOfIso ℂ surfaceAnalyticProductIso 2
        (Singular.cohomologyMap ℂ 2 surfaceFirstCMTopologicalMap x) =
      Singular.firstFactorCohomologyEnd curveAnalyticSpace curveAnalyticSpace
        curveCMTopologicalMap
        (Singular.cohomologyLinearEquivOfIso ℂ surfaceAnalyticProductIso 2 x) := by
  change ((Singular.cohomologyMap ℂ 2 surfaceAnalyticProductIso.inv).comp
      (Singular.cohomologyMap ℂ 2 surfaceFirstCMTopologicalMap)) x =
    ((Singular.cohomologyMap ℂ 2
        (curveCMTopologicalMap ⊗ₘ 𝟙 curveAnalyticSpace)).comp
      (Singular.cohomologyMap ℂ 2 surfaceAnalyticProductIso.inv)) x
  rw [← Singular.cohomologyMap_comp, ← Singular.cohomologyMap_comp,
    surfaceAnalyticProductIso_inv_intertwines_firstCM_topological]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem surfaceProductCohomologyEquiv_secondCM
    (x : Singular.Cohomology ℂ surfaceAnalyticSpace 2) :
    Singular.cohomologyLinearEquivOfIso ℂ surfaceAnalyticProductIso 2
        (Singular.cohomologyMap ℂ 2 surfaceSecondCMTopologicalMap x) =
      Singular.secondFactorCohomologyEnd curveAnalyticSpace curveAnalyticSpace
        curveCMTopologicalMap
        (Singular.cohomologyLinearEquivOfIso ℂ surfaceAnalyticProductIso 2 x) := by
  change ((Singular.cohomologyMap ℂ 2 surfaceAnalyticProductIso.inv).comp
      (Singular.cohomologyMap ℂ 2 surfaceSecondCMTopologicalMap)) x =
    ((Singular.cohomologyMap ℂ 2
        (𝟙 curveAnalyticSpace ⊗ₘ curveCMTopologicalMap)).comp
      (Singular.cohomologyMap ℂ 2 surfaceAnalyticProductIso.inv)) x
  rw [← Singular.cohomologyMap_comp, ← Singular.cohomologyMap_comp,
    surfaceAnalyticProductIso_inv_intertwines_secondCM_topological]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport through the product homeomorphism conjugates the surface detector
to the factorwise product detector. -/
theorem surfaceProductCohomologyEquiv_surfaceCMDoubleMinusEnd
    (x : Singular.Cohomology ℂ surfaceAnalyticSpace 2) :
    Singular.cohomologyLinearEquivOfIso ℂ surfaceAnalyticProductIso 2
        (surfaceCMDoubleMinusEnd x) =
      Singular.productCMDoubleMinusEnd curveAnalyticSpace curveAnalyticSpace
        curveCMTopologicalMap curveCMTopologicalMap
        (Singular.cohomologyLinearEquivOfIso ℂ surfaceAnalyticProductIso 2 x) := by
  simp only [surfaceCMDoubleMinusEnd,
    Singular.productCMDoubleMinusEnd, LinearMap.comp_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [map_sub, map_smul, surfaceProductCohomologyEquiv_firstCM,
    map_sub, map_smul, surfaceProductCohomologyEquiv_secondCM]

/-- The direct surface CM detector is nonzero on the named complexified rational
candidate. -/
theorem surfaceCMDoubleMinusEnd_explicitSurfaceClass_ne_zero :
    surfaceCMDoubleMinusEnd explicitSurfaceComplexifiedExternalTwoClass ≠ 0 := by
  intro hzero
  apply productCMDoubleMinusEnd_explicitSurfaceClass_ne_zero
  rw [← surfaceProductCohomologyEquiv_surfaceCMDoubleMinusEnd, hzero, map_zero]

end AlgebraicGeometry.ExplicitEllipticCandidate
