/-
Copyright 2026 The Formal Conjectures Authors.

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

public import HodgeConjecture.Mathlib.Algebra.Category.Grp.Basic
public import HodgeConjecture.Other.AlgebraicTopology.OpenCoverOrderedCechBicomplex
public import HodgeConjecture.Other.AlgebraicTopology.SingularContractibleMapQuasiIso
public import HodgeConjecture.Other.AlgebraicTopology.SingularExcisionOpenCover

/-!
# Finite good covers and normalized singular Čech chains

This file combines the ordered Čech normalization adapted from Chris Birkbeck's
`sphere-six-complex` pull request #185 with the small-chain theorem ported from Paul Lezeau's
pull request #49.

For any open cover, the normalized total complex of singular chains on finite intersections
maps by a quasi-isomorphism to the ambient integral singular chain complex.  For a finite good
cover, its nonempty intersections also have the expected local comparison with a point.  The
remaining step toward a finite nerve model is to assemble these local comparisons while
discarding empty intersections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set

namespace AlgebraicTopology

/-- A morphism of first-quadrant bicomplexes which is a quasi-isomorphism on every vertical
column is a quasi-isomorphism after direct-sum totalization. -/
public theorem firstQuadrantTotal_quasiIso_of_columns
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L)
    (hcolumn : ∀ p : ℕ, QuasiIso (f.f p)) :
    QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) := by
  apply firstQuadrantTotal_quasiIso_of_singleColumns f
  intro p
  exact firstQuadrantSingleColumnTotal_quasiIso f p (hcolumn p)

namespace Singular

variable {ι : Type} [LinearOrder ι] (X : TopCat) (U : ι → Set X)

/-- The normalized ordered-intersection Čech total mapped to ambient integral singular chains. -/
public def openCoverNormalizedCechTotalToSingular :
    (openCoverIntersectionChainModels X U).cechTotal
        TupleClass.strictMono ⟶
      IntegralSingularChainComplexObj X :=
  openCoverNormalizedCechTotalAugmentation X U ≫
    coverSmallIntegralSingularChainInclusion X U

set_option linter.style.haveILetI false in
/-- An open cover is computed by its normalized ordered-intersection singular Čech total. -/
public theorem openCoverNormalizedCechTotalToSingular_quasiIso
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (openCoverNormalizedCechTotalToSingular X U) := by
  letI : QuasiIso (openCoverNormalizedCechTotalAugmentation X U) :=
    openCoverNormalizedCechTotalAugmentation_quasiIso X U
  letI : QuasiIso (coverSmallIntegralSingularChainInclusion X U) :=
    coverSmallChainQuasiIsomorphism_of_openCover X U hUopen hUcover
  exact quasiIso_comp _ _

/-- A finite good cover: every nonempty finite intersection is empty or contractible. -/
public structure FiniteGoodCover where
  /-- The index set is finite. -/
  finite_index : Finite ι
  /-- Every member is open. -/
  isOpen_openSet : ∀ i, IsOpen (U i)
  /-- The members cover the ambient space. -/
  iUnion_openSet : ⋃ i, U i = Set.univ
  /-- Every inhabited nonempty finite intersection is contractible. -/
  contractible_intersection : ∀ (s : Finset ι), s.Nonempty →
    (openCoverIntersection X U s).Nonempty →
      ContractibleSpace (openCoverIntersection X U s)

namespace FiniteGoodCover

variable {X U}

/-- The normalized singular Čech total of a finite good cover computes ambient singular chains. -/
public theorem normalizedCechTotalToSingular_quasiIso (h : FiniteGoodCover X U) :
    QuasiIso (openCoverNormalizedCechTotalToSingular X U) :=
  openCoverNormalizedCechTotalToSingular_quasiIso X U h.isOpen_openSet h.iUnion_openSet

/-- The normalized singular Čech total of a finite good cover has the same integral homology as
the ambient space. -/
public def normalizedCechHomologyIso (h : FiniteGoodCover X U) (n : ℕ) :
    ((openCoverIntersectionChainModels X U).cechTotal
      TupleClass.strictMono).homology n ≅
        (IntegralSingularChainComplexObj X).homology n := by
  letI : QuasiIso (openCoverNormalizedCechTotalToSingular X U) :=
    h.normalizedCechTotalToSingular_quasiIso
  exact asIso (HomologicalComplex.homologyMap
    (openCoverNormalizedCechTotalToSingular X U) n)

/-- For a finite good cover, the normalized outer Čech complex vanishes at and above the
cardinality of the index set. -/
public theorem isZero_normalizedCechObject (h : FiniteGoodCover X U)
    {n : ℕ} (hn : Nat.card ι ≤ n) :
    IsZero ((openCoverIntersectionChainModels X U).cechObject
      TupleClass.strictMono n) := by
  let : Finite ι := h.finite_index
  let : Fintype ι := Fintype.ofFinite ι
  rw [Nat.card_eq_fintype_card] at hn
  exact (openCoverIntersectionChainModels X U).isZero_cechObject_strictMono hn

/-- The canonical map from an inhabited finite intersection to a point. -/
public def intersectionToPoint (s : Finset ι) :
    C(openCoverIntersection X U s, PUnit) :=
  { toFun := fun _ ↦ PUnit.unit
    continuous_toFun := continuous_const }

omit [LinearOrder ι] in
set_option linter.style.haveILetI false in
/-- On each inhabited nonempty intersection of a finite good cover, the canonical map to a point
induces a quasi-isomorphism on integral singular chains. -/
public theorem intersectionToPoint_quasiIso (h : FiniteGoodCover X U)
    (s : Finset ι) (hs : s.Nonempty) (hne : (openCoverIntersection X U s).Nonempty) :
    QuasiIso (integralSingularChainMapObj
      (TopCat.ofHom (intersectionToPoint (X := X) (U := U) s))) := by
  letI : ContractibleSpace (openCoverIntersection X U s) :=
    h.contractible_intersection s hs hne
  exact singularChainMap_quasiIso_of_contractibleSpaces (AddCommGrpCat.of ℤ)
    (intersectionToPoint (X := X) (U := U) s)

end FiniteGoodCover

end Singular

end AlgebraicTopology
