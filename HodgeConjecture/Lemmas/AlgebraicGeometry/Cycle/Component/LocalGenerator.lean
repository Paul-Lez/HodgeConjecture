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

public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClass
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothLocus
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalCoordinates

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClassGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean

/-!
# Local generators from exact cycle-component coordinates

An exact étale coordinate package on the smooth locus of a cycle component gives an
analytic chart on its chosen affine neighborhood. This file constructs that chart directly from
the retained polynomial-ring homomorphism. It then transports the proved standard complex local
homology generator through the chart.

The chart map factors through its open target and the proved point-neighborhood excision theorem.
Consequently the resulting class generates the full local homology of the affine component
neighborhood. This file does not construct a supported cohomology class or prove purity for the
component inside the ambient variety.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicGeometry

attribute [local instance] overSpecAlgebra

variable {d n : ℕ} {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom] {x : X.left}
  [SmoothOfRelativeDimension d X.hom]

namespace CycleComponentSeparateLocalCoordinates

variable (C : CycleComponentSeparateLocalCoordinates X x d n)

/-- The complex structure map on the selected affine component neighborhood. -/
abbrev neighborhoodStructureMap :
    C.componentNeighborhood.toScheme ⟶ Spec ↧ℂ :=
  C.componentNeighborhood.ι ≫ (cycleComponentSmoothLocus X x).ι ≫ X.left.pointClosureι x ≫ X.hom

/-- The retained exact component coordinates, transported to global sections of the affine
neighborhood itself. -/
def coordinateRingHomOnNeighborhood :
    MvPolynomial (Fin n) ℂ →+* Γ(C.componentNeighborhood.toScheme, ⊤) :=
  C.componentNeighborhood.topIso.inv.hom.comp C.componentCoordinateAlgHom.toRingHom

/-- The transported coordinate map is compatible with the neighborhood's complex structure
map. -/
lemma C_comp_coordinateRingHomOnNeighborhood :
    CommRingCat.ofHom MvPolynomial.C ≫
        CommRingCat.ofHom C.coordinateRingHomOnNeighborhood =
      (Scheme.ΓSpecIso ↧ℂ).inv ≫ C.neighborhoodStructureMap.appTop := by
  apply (cancel_mono C.componentNeighborhood.topIso.hom).mp
  change (((CommRingCat.ofHom MvPolynomial.C) ≫
      CommRingCat.ofHom C.componentCoordinateAlgHom.toRingHom) ≫
        C.componentNeighborhood.topIso.inv) ≫
          C.componentNeighborhood.topIso.hom =
    (((Scheme.ΓSpecIso ↧ℂ).inv ≫
      C.neighborhoodStructureMap.appTop) ≫
        C.componentNeighborhood.topIso.hom)
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [neighborhoodStructureMap, Scheme.Hom.comp_appTop, Category.assoc]
  rw [Scheme.Opens.ι_appTop_topIso_hom]
  exact congrArg CommRingCat.ofHom C.componentCoordinateAlgHom.comp_algebraMap

/-- The transported exact coordinate map remains étale. -/
lemma coordinateRingHomOnNeighborhood_etale :
    C.coordinateRingHomOnNeighborhood.Etale :=
  RingHom.Etale.respectsIso.1 C.componentCoordinateAlgHom.toRingHom
    C.componentNeighborhood.topIso.symm.commRingCatIsoToRingEquiv
      C.componentCoordinateAlgHom_etale

/-- Complex affine `n`-space is standard smooth of relative dimension `n`, using its presentation
with `n` variables and no relations. -/
lemma mvPolynomial_C_isStandardSmoothOfRelativeDimension :
    (MvPolynomial.C : ℂ →+* MvPolynomial (Fin n) ℂ).IsStandardSmoothOfRelativeDimension n := by
  rw [show (MvPolynomial.C : ℂ →+* MvPolynomial (Fin n) ℂ) =
    algebraMap ℂ (MvPolynomial (Fin n) ℂ) from rfl]
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  let P : Algebra.SubmersivePresentation ℂ (MvPolynomial (Fin n) ℂ)
      (Fin n) Empty :=
    { toPreSubmersivePresentation :=
        { toPresentation :=
            { toGenerators := Algebra.Generators.mvPolynomial ℂ (Fin n)
              relation := Empty.elim
              span_range_relation_eq_ker := by
                rw [Algebra.Generators.ker_mvPolynomial]
                simp }
          map := Empty.elim
          map_inj := fun a ↦ a.elim }
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
          Matrix.det_isEmpty]
        simpa only [map_one] using
          (isUnit_one : IsUnit (1 : MvPolynomial (Fin n) ℂ)) }
  exact P.isStandardSmoothOfRelativeDimension (by
    simp [Algebra.Presentation.dimension])

/-- The structure map of the exact affine component neighborhood is standard smooth of the
coordinate package's specified dimension on global sections. -/
lemma neighborhoodStructureMap_appTop_isStandardSmoothOfRelativeDimension :
    C.neighborhoodStructureMap.appTop.hom.IsStandardSmoothOfRelativeDimension n := by
  have hcoord0 : C.coordinateRingHomOnNeighborhood.IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.mp
      C.coordinateRingHomOnNeighborhood_etale
  have hcomposite :
      RingHom.IsStandardSmoothOfRelativeDimension n
        (C.coordinateRingHomOnNeighborhood.comp MvPolynomial.C) := by
    simpa only [zero_add] using
      hcoord0.comp (mvPolynomial_C_isStandardSmoothOfRelativeDimension (n := n))
  have hcat := C.C_comp_coordinateRingHomOnNeighborhood
  have hcomp :
      RingHom.IsStandardSmoothOfRelativeDimension n
        (C.neighborhoodStructureMap.appTop.hom.comp
          (Scheme.ΓSpecIso ↧ℂ).inv.hom) := by
    have hring := congrArg CommRingCat.Hom.hom hcat
    change C.coordinateRingHomOnNeighborhood.comp MvPolynomial.C =
      C.neighborhoodStructureMap.appTop.hom.comp
        (Scheme.ΓSpecIso ↧ℂ).inv.hom at hring
    rw [← hring]
    exact hcomposite
  have h := hcomp.comp
    (RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso ↧ℂ).commRingCatIsoToRingEquiv)
  have heq :
      (C.neighborhoodStructureMap.appTop.hom.comp
        (Scheme.ΓSpecIso ↧ℂ).inv.hom).comp
          (Scheme.ΓSpecIso ↧ℂ).hom.hom =
        C.neighborhoodStructureMap.appTop.hom := by
    ext a
    have ha := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso ↧ℂ).hom_inv_id a
    exact congrArg C.neighborhoodStructureMap.appTop.hom ha
  exact heq ▸ h

/-- The exact coordinates prove that the selected affine component neighborhood is smooth of the
specified relative dimension. -/
noncomputable instance neighborhoodSmoothOfRelativeDimension :
    SmoothOfRelativeDimension n C.neighborhoodStructureMap where
  exists_isStandardSmoothOfRelativeDimension y := by
    let : IsAffine C.componentNeighborhood.toScheme :=
      C.componentNeighborhood_isAffine
    refine ⟨⊤, isAffineOpen_top _, C.neighborhoodStructureMap ⁻¹ᵁ ⊤,
      ?_, by simp, le_rfl, ?_⟩
    · simpa using (isAffineOpen_top C.componentNeighborhood.toScheme)
    · rw [Scheme.Hom.appLE_eq_app]
      exact C.neighborhoodStructureMap_appTop_isStandardSmoothOfRelativeDimension

noncomputable local instance coordinateRingAlgebra :
    Algebra (MvPolynomial (Fin n) ℂ) Γ(C.componentNeighborhood.toScheme, ⊤) :=
  C.coordinateRingHomOnNeighborhood.toAlgebra

noncomputable local instance coordinateRingComplexAlgebra :
    Algebra ℂ Γ(C.componentNeighborhood.toScheme, ⊤) :=
  (C.coordinateRingHomOnNeighborhood.comp MvPolynomial.C).toAlgebra

noncomputable local instance coordinateRingScalarTower :
    IsScalarTower ℂ (MvPolynomial (Fin n) ℂ)
      Γ(C.componentNeighborhood.toScheme, ⊤) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

noncomputable local instance coordinateRingEtale :
    Algebra.Etale (MvPolynomial (Fin n) ℂ)
      Γ(C.componentNeighborhood.toScheme, ⊤) :=
  RingHom.etale_algebraMap.mp C.coordinateRingHomOnNeighborhood_etale

end CycleComponentSeparateLocalCoordinates
end AlgebraicGeometry

namespace AlgebraicTopology.Singular

/-- The oriented standard complex local class generates rational local homology in every complex
dimension. -/
lemma span_standardComplexLocalClass_eq_top (n : ℕ) :
    Submodule.span ℚ {standardComplexLocalClass n} = ⊤ := by
  cases n with
  | zero => exact span_standardComplexLocalClass_zero_eq_top
  | succ n =>
      rw [span_standardComplexLocalClass_eq_top_iff]
      have hdeg : (n + 1) * 2 = n * 2 + 2 := by lia
      rw [hdeg]
      exact span_standardLocalClass_add_two_eq_top (n * 2)

end AlgebraicTopology.Singular
