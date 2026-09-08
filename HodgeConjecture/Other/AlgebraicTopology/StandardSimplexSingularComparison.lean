/-
Copyright 2026 Paul Lezeau and The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Mathlib.Topology.Category.TopCat.Basic
public import HodgeConjecture.Other.AlgebraicTopology.SingularContractibleMapQuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Analysis.Convex.Contractible

/-!
# Singular chains of a standard simplex

The adjunction unit from a simplicial set to the singular simplicial set of its realization
induces a canonical chain map. For a standard simplex this map is a quasi-isomorphism with
arbitrary coefficients in `AddCommGrpCat`. Composing it with a map to any contractible space is
again a quasi-isomorphism.

The proofs are adapted from
[`SphereSixComplex.Topology.StandardSimplexSimplicialSingularComparisonGeneral`](https://github.com/deancureton/sphere-six-complex/blob/895c0a0/SphereSixComplex/Topology/StandardSimplexSimplicialSingularComparisonGeneral.lean)
and
[`SphereSixComplex.Topology.ContractibleSingularMapQuasiIso`](https://github.com/deancureton/sphere-six-complex/blob/895c0a0/SphereSixComplex/Topology/ContractibleSingularMapQuasiIso.lean),
including the coefficient-generalization work in
[`sphere-six-complex` pull request #144](https://github.com/deancureton/sphere-six-complex/pull/144).
That repository is released under the Apache License 2.0.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ContinuousMap Simplicial

namespace AlgebraicTopology

/-- The chain map induced by the unit from a simplicial set to the singular simplicial set of
its topological realization. -/
def simplicialToRealizationSingularChainMap
    (K : SSet.{0}) (R : AddCommGrpCat) :
    K.chainComplex R ⟶
      (TopCat.toSSet.obj (SSet.toTop.obj K)).chainComplex R :=
  SSet.chainComplexMap (sSetTopAdj.unit.app K) R

/-- In a nonnegatively graded chain complex, degree-zero chains are canonically the degree-zero
cycles. -/
def chainComplexXZeroIsoCyclesZero
    (K : ChainComplex AddCommGrpCat ℕ) : K.X 0 ≅ K.cycles 0 where
  hom := K.liftCycles (𝟙 _) 0 (by simp) (by simp)
  inv := K.iCycles 0
  hom_inv_id := by simp
  inv_hom_id := by
    rw [← cancel_mono (K.iCycles 0)]
    simp

/-- The degree-zero simplicial-homology augmentation is natural in the simplicial set. -/
theorem simplicialHomologyZeroAugmentation_naturality
    {X Y : SSet.{0}} (f : X ⟶ Y) (R : AddCommGrpCat) :
    SSet.homologyMap f R 0 ≫ Y.homology₀ε R = X.homology₀ε R := by
  let K := X.chainComplex R
  let L := Y.chainComplex R
  let φ := SSet.chainComplexMap f R
  let e₀ := chainComplexXZeroIsoCyclesZero K
  apply (cancel_epi (K.homologyπ 0)).1
  apply (cancel_epi e₀.hom).1
  apply X.chainComplex_hom_ext
  intro x
  change X.ιChainComplex x ≫ e₀.hom ≫ K.homologyπ 0 ≫
      HomologicalComplex.homologyMap φ 0 ≫ Y.homology₀ε R =
    X.ιChainComplex x ≫ e₀.hom ≫ K.homologyπ 0 ≫ X.homology₀ε R
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  change X.ιChainComplex x ≫
      K.liftCycles (𝟙 _) 0 (by simp) (by simp) ≫
        HomologicalComplex.cyclesMap φ 0 ≫ L.homologyπ 0 ≫
          Y.homology₀ε R =
    X.ιChainComplex x ≫ K.liftCycles (𝟙 _) 0 (by simp) (by simp) ≫
      K.homologyπ 0 ≫ X.homology₀ε R
  simp only [← Category.assoc, HomologicalComplex.comp_liftCycles,
    Category.comp_id]
  simp only [HomologicalComplex.liftCycles_comp_cyclesMap]
  change L.liftCycles
      (X.ιChainComplex x ≫ (SSet.chainComplexMap f R).f 0) 0 (by simp) (by simp) ≫
        L.homologyπ 0 ≫ Y.homology₀ε R =
    K.liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
      K.homologyπ 0 ≫ X.homology₀ε R
  have hlift : L.liftCycles
      (X.ιChainComplex x ≫ (SSet.chainComplexMap f R).f 0) 0 (by simp) (by simp) =
      L.liftCycles (Y.ιChainComplex (f.app _ x)) 0 (by simp) (by simp) := by
    apply (cancel_mono (L.iCycles 0)).1
    simpa only [HomologicalComplex.liftCycles_i] using
      SSet.ι_chainComplexMap_f X Y f R x
  rw [hlift]
  calc
    _ = 𝟙 R := by
      simpa only [] using
        Y.liftCycles_ιChainComplex_homologyπ_homology₀ε R (f.app _ x)
    _ = _ := by
      symm
      simpa only [] using
        X.liftCycles_ιChainComplex_homologyπ_homology₀ε R x

/-- Every standard simplex is connected as a simplicial set. -/
theorem standardSimplex_isConnected (n : ℕ) :
    (SSet.stdSimplex.obj (SimplexCategory.mk n)).IsConnected := by
  rw [SSet.isConnected_iff]
  constructor
  · constructor
    intro a b
    induction a using SSet.π₀.rec with
    | mk x =>
      induction b using SSet.π₀.rec with
      | mk y =>
        let i := SSet.stdSimplex.obj₀Equiv x
        let j := SSet.stdSimplex.obj₀Equiv y
        rcases le_total i j with hij | hji
        · let s := SSet.stdSimplex.edge n i j hij
          have hsrc : (SSet.stdSimplex.obj (SimplexCategory.mk n)).δ 1 s = x := by
            apply SSet.stdSimplex.obj₀Equiv.injective
            rfl
          have htgt : (SSet.stdSimplex.obj (SimplexCategory.mk n)).δ 0 s = y := by
            apply SSet.stdSimplex.obj₀Equiv.injective
            rfl
          simpa only [hsrc, htgt] using SSet.π₀.sound (SSet.Edge.mk' s)
        · let s := SSet.stdSimplex.edge n j i hji
          have hsrc : (SSet.stdSimplex.obj (SimplexCategory.mk n)).δ 1 s = y := by
            apply SSet.stdSimplex.obj₀Equiv.injective
            rfl
          have htgt : (SSet.stdSimplex.obj (SimplexCategory.mk n)).δ 0 s = x := by
            apply SSet.stdSimplex.obj₀Equiv.injective
            rfl
          symm
          simpa only [hsrc, htgt] using SSet.π₀.sound (SSet.Edge.mk' s)
  · exact ⟨SSet.stdSimplex.const n 0 _⟩

/-- The geometric realization of a standard simplex is contractible. -/
theorem standardSimplexRealization_contractibleSpace (n : ℕ) :
    ContractibleSpace
      (SSet.toTop.obj (SSet.stdSimplex.obj (SimplexCategory.mk n)) : Type) := by
  let : ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
      ⟨stdSimplex.vertex (0 : Fin (n + 1)),
        (stdSimplex.vertex (0 : Fin (n + 1))).2⟩
  exact (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).contractibleSpace

/-- Simplicial chains of a standard simplex are exact in positive degrees. -/
theorem standardSimplex_simplicialChains_exactAt
    (R : AddCommGrpCat) (n k : ℕ) (hk : k ≠ 0) :
    ((Δ[n] : SSet.{0}).chainComplex R).ExactAt k := by
  let ed := (SSet.Augmented.StandardSimplex.extraDegeneracy
    (SimplexCategory.mk n)).map (sigmaConst.obj R)
  let e := ed.homotopyEquiv
  exact (exactAt_iff_of_quasiIsoAt e.hom k).mpr
    (HomologicalComplex.exactAt_single_obj _ _ _ _ hk)

/-- Singular chains of the realization of a standard simplex are exact in positive degrees. -/
theorem standardSimplexRealization_singularChains_exactAt
    (R : AddCommGrpCat) (n k : ℕ) (hk : k ≠ 0) :
    ((TopCat.toSSet.obj (SSet.toTop.obj (Δ[n] : SSet.{0}))).chainComplex R).ExactAt k := by
  let : ContractibleSpace (SSet.toTop.obj (Δ[n] : SSet.{0}) : Type) :=
    standardSimplexRealization_contractibleSpace n
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit
    (SSet.toTop.obj (Δ[n] : SSet.{0}) : Type)
  have hunit := isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    AddCommGrpCat k R (TopCat.of Unit) hk
  let E := singularChainHomotopyEquivOfHomotopyEquivAddCommGrp R e
  have hzero := hunit.of_iso (E.toHomologyIso k)
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact hzero

/-- The canonical comparison for a standard simplex is a quasi-isomorphism for every
coefficient object in `AddCommGrpCat`. -/
theorem standardSimplex_simplicialToRealizationSingularChainMap_quasiIso
    (R : AddCommGrpCat) (n : ℕ) :
    QuasiIso (simplicialToRealizationSingularChainMap (Δ[n] : SSet.{0}) R) := by
  rw [quasiIso_iff]
  intro k
  by_cases hk : k = 0
  · subst k
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let : (SSet.stdSimplex.obj (SimplexCategory.mk n)).IsConnected :=
      standardSimplex_isConnected n
    let : ContractibleSpace
        (SSet.toTop.obj (Δ[n] : SSet.{0}) : Type) :=
      standardSimplexRealization_contractibleSpace n
    let : PathConnectedSpace
        (SSet.toTop.obj (Δ[n] : SSet.{0}) : Type) := inferInstance
    let : (TopCat.toSSet.obj (SSet.toTop.obj (Δ[n] : SSet.{0}))).IsConnected :=
      inferInstance
    let φ := simplicialToRealizationSingularChainMap (Δ[n] : SSet.{0}) R
    have hε : HomologicalComplex.homologyMap φ 0 ≫
        (SSet.toTop.obj (Δ[n] : SSet.{0})).singularHomology₀ε R =
      (Δ[n] : SSet.{0}).homology₀ε R :=
      simplicialHomologyZeroAugmentation_naturality
        (sSetTopAdj.unit.app (Δ[n] : SSet.{0})) R
    let hsource : IsIso ((Δ[n] : SSet.{0}).homology₀ε R) := inferInstance
    let htarget : IsIso
        ((SSet.toTop.obj (Δ[n] : SSet.{0})).singularHomology₀ε R) :=
      inferInstanceAs (IsIso ((TopCat.toSSet.obj
        (SSet.toTop.obj (Δ[n] : SSet.{0}))).homology₀ε R))
    have hcomp : IsIso (HomologicalComplex.homologyMap φ 0 ≫
        (SSet.toTop.obj (Δ[n] : SSet.{0})).singularHomology₀ε R) := by
      rw [hε]
      exact hsource
    exact @IsIso.of_isIso_comp_right _ _ _ _ _
      (HomologicalComplex.homologyMap φ 0)
      ((SSet.toTop.obj (Δ[n] : SSet.{0})).singularHomology₀ε R) htarget hcomp
  · exact (quasiIsoAt_iff_exactAt _ k
      (standardSimplex_simplicialChains_exactAt R n k hk)).mpr
        (standardSimplexRealization_singularChains_exactAt R n k hk)

/-- The standard-simplex comparison followed by the singular-chain map of a continuous map. -/
def standardSimplexToContractibleSingularChainMap
    {Z : Type} [TopologicalSpace Z] (R : AddCommGrpCat) (n : ℕ)
    (f : C((SSet.toTop.obj (Δ[n] : SSet.{0}) : Type), Z)) :
    (Δ[n] : SSet.{0}).chainComplex R ⟶
      (TopCat.toSSet.obj (TopCat.of Z)).chainComplex R :=
  simplicialToRealizationSingularChainMap (Δ[n] : SSet.{0}) R ≫
    SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) R

/-- The standard-simplex comparison followed by any map to a contractible space is a
quasi-isomorphism. -/
theorem standardSimplexToContractibleSingularChainMap_quasiIso
    {Z : Type} [TopologicalSpace Z] [ContractibleSpace Z]
    (R : AddCommGrpCat) (n : ℕ)
    (f : C((SSet.toTop.obj (Δ[n] : SSet.{0}) : Type), Z)) :
    QuasiIso (standardSimplexToContractibleSingularChainMap R n f) := by
  let : ContractibleSpace (SSet.toTop.obj (Δ[n] : SSet.{0}) : Type) :=
    standardSimplexRealization_contractibleSpace n
  let hstandard : QuasiIso
      (simplicialToRealizationSingularChainMap (Δ[n] : SSet.{0}) R) :=
    standardSimplex_simplicialToRealizationSingularChainMap_quasiIso R n
  let htarget : QuasiIso
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) R) :=
    singularChainMap_quasiIso_of_contractibleSpaces R f
  unfold standardSimplexToContractibleSingularChainMap
  infer_instance

end AlgebraicTopology
