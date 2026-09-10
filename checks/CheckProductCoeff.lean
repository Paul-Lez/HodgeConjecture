import Other.AlgebraicTopology.SingularProductCoefficientChange

open CategoryTheory Limits MonoidalCategory
open AlgebraicTopology
open scoped Simplicial

namespace AlgebraicTopology.Singular

noncomputable section

local instance (X : TopCat) (n : ℕ) : Module ℚ ((CChains X).X n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (X : TopCat) (n : ℕ) : IsScalarTower ℚ ℂ ((CChains X).X n) :=
  IsScalarTower.of_compHom ℚ ℂ _

local instance (X : TopCat) (n : ℕ) : Module ℚ (CCyclesModel X n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (X : TopCat) (n : ℕ) : IsScalarTower ℚ ℂ (CCyclesModel X n) :=
  IsScalarTower.of_compHom ℚ ℂ _

local instance (X : TopCat) (n : ℕ) : Module ℚ ((CChains X).homology n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (X : TopCat) (n : ℕ) : IsScalarTower ℚ ℂ ((CChains X).homology n) :=
  IsScalarTower.of_compHom ℚ ℂ _

example (X : TopCat)
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

end

end AlgebraicTopology.Singular
