/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache License, Version 2.0 (the "License");
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

public import Other.AlgebraicTopology.GlobalRawRelativeConnecting
public import Other.AlgebraicTopology.GlobalCochainRepresentative
public import Other.AlgebraicTopology.ExplicitCochainClass
public import Other.AlgebraicGeometry.BettiGlobalSectionsAdditivity

/-!
# From a supported singular cochain class to hypercohomology

This file records the direct route used for an explicit relative singular cochain.
Starting with a class of the actual pair `(X, X \\ Z)`, it first uses the literal
relative-to-ambient cochain inclusion to obtain a class in global raw singular cochains.
The standard universal-coefficient comparison gives ordinary singular cohomology, and the
proved rational Betti comparison then gives the repository's hypercohomology model.

No cycle-class or Chern-class correspondence occurs in these definitions.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom]
  [T2Space (ComplexPoint X)]
  [∀ U : Opens (ComplexPoint X), ParacompactSpace U]

/-- Move a literal closed ordinary singular cochain to rational constant-sheaf cohomology using
a supplied smooth relative dimension.  This is the comparison needed by explicit examples such
as the direct `Proj` model of `ℙ²`, where the smooth dimension is known before a separate
integrality presentation is installed. -/
def hypercohomologyClassOfSingularCochain_of_smoothOfRelativeDimension
    (d n : ℕ) [SmoothOfRelativeDimension d X.hom]
    (φ : (AlgebraicTopology.Singular.singularChainComplex ℚ
      (TopCat.of (ComplexPoint X))).linearDualCochainComplex.X n)
  (hφ : ((AlgebraicTopology.Singular.singularChainComplex ℚ
      (TopCat.of (ComplexPoint X))).linearDualCochainComplex).d n (n + 1) φ = 0) :
    H^(n : ℤ)(X; ℚ) :=
  (rationalCohomologyEquivSingularCohomology_of_smoothOfRelativeDimension X d n).symm
    (ordinarySingularCohomologyEquivCohomology ℚ (TopCat.of (ComplexPoint X)) n
      (AlgebraicTopology.Singular.cochainCohomologyClass ℚ
        (TopCat.of (ComplexPoint X)) n φ hφ))

@[simp]
lemma rationalCohomologyEquivSingularCohomology_hypercohomologyClassOfSingularCochain
    (d n : ℕ) [SmoothOfRelativeDimension d X.hom]
    (φ : (AlgebraicTopology.Singular.singularChainComplex ℚ
      (TopCat.of (ComplexPoint X))).linearDualCochainComplex.X n)
    (hφ : ((AlgebraicTopology.Singular.singularChainComplex ℚ
      (TopCat.of (ComplexPoint X))).linearDualCochainComplex).d n (n + 1) φ = 0) :
    rationalCohomologyEquivSingularCohomology_of_smoothOfRelativeDimension X d n
        (hypercohomologyClassOfSingularCochain_of_smoothOfRelativeDimension X d n φ hφ) =
      ordinarySingularCohomologyEquivCohomology ℚ (TopCat.of (ComplexPoint X)) n
        (AlgebraicTopology.Singular.cochainCohomologyClass ℚ
          (TopCat.of (ComplexPoint X)) n φ hφ) := by
  exact (rationalCohomologyEquivSingularCohomology_of_smoothOfRelativeDimension
    X d n).apply_symm_apply _

/-- The global raw singular-cochain class induced by a supported relative singular class.

The map is the literal cochain inclusion of the dual relative-chain short exact sequence,
transported through the fixed global raw-cochain model. -/
def globalRawClassOfSupportedSingularClass
    (Z : Set (ComplexPoint X)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) Z n) :
    (globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))).homology n :=
  ((globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))).extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).hom
      (globalRawRelativeCochainClass ℚ (TopCat.of (ComplexPoint X)) Zᶜ n a)

/-- A displayed closed global raw singular cochain representing the ordinary class induced by
the supported singular class. Its cohomology class comes from the local winding construction. -/
noncomputable def globalRawCochainOfSupportedSingularClass
    (Z : Set (ComplexPoint X)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) Z n) :
    (globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))).X n :=
  HomologicalComplex.cochainRepresentative
    (globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))) n
    (globalRawClassOfSupportedSingularClass X Z n a)

/-- The displayed global cochain is closed. -/
lemma globalRawCochainOfSupportedSingularClass_closed
    (Z : Set (ComplexPoint X)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) Z n) :
    ((globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))).d n (n + 1)).hom
      (globalRawCochainOfSupportedSingularClass X Z n a) = 0 :=
  HomologicalComplex.cochainRepresentative_closed
    (globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))) n
    (globalRawClassOfSupportedSingularClass X Z n a)

/-- The cycle underlying the displayed global cochain represents precisely the class induced by
the supported singular class. -/
lemma globalRawCochainOfSupportedSingularClass_class
    (Z : Set (ComplexPoint X)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) Z n) :
    ((globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))).homologyπ n).hom
      (HomologicalComplex.cochainCycleRepresentative
        (globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))) n
        (globalRawClassOfSupportedSingularClass X Z n a)) =
      globalRawClassOfSupportedSingularClass X Z n a :=
  HomologicalComplex.cochainCycleRepresentative_spec
    (globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))) n
    (globalRawClassOfSupportedSingularClass X Z n a)

/-- The ordinary singular class read directly from the displayed global raw cochain. -/
noncomputable def singularClassOfDisplayedGlobalRawCochain
    (Z : Set (ComplexPoint X)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) Z n) :
    Cohomology ℚ (TopCat.of (ComplexPoint X)) n :=
  ordinarySingularCohomologyEquivCohomology ℚ (TopCat.of (ComplexPoint X)) n
    ((ordinarySingularCohomologyEquivGlobalRaw ℚ (TopCat.of (ComplexPoint X)) n).symm
      (((globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))).homologyπ n).hom
        (HomologicalComplex.cochainCycleRepresentative
          (globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))) n
          (globalRawClassOfSupportedSingularClass X Z n a))))

/-- The ordinary singular class induced by a supported relative singular class, obtained from
the preceding global raw cochain class through the actual universal-coefficient equivalence. -/
def singularClassOfSupportedSingularClass
    (Z : Set (ComplexPoint X)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) Z n) :
    Cohomology ℚ (TopCat.of (ComplexPoint X)) n :=
  ordinarySingularCohomologyEquivCohomology ℚ (TopCat.of (ComplexPoint X)) n
    ((ordinarySingularCohomologyEquivGlobalRaw ℚ (TopCat.of (ComplexPoint X)) n).symm
      (globalRawClassOfSupportedSingularClass X Z n a))

/-- The displayed global raw cochain represents the ordinary singular class induced by the
supported local winding construction. -/
lemma singularClassOfDisplayedGlobalRawCochain_eq_singularClassOfSupportedSingularClass
    (Z : Set (ComplexPoint X)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) Z n) :
    singularClassOfDisplayedGlobalRawCochain X Z n a =
      singularClassOfSupportedSingularClass X Z n a := by
  rw [singularClassOfDisplayedGlobalRawCochain,
    globalRawCochainOfSupportedSingularClass_class]
  rfl

/-- Move the singular class of a supported relative cochain into constant-sheaf
hypercohomology using the proved rational Betti comparison. -/
def hypercohomologyClassOfSupportedSingularClass
    (Z : Set (ComplexPoint X)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) Z n) :
    H^(n : ℤ)(X; ℚ) :=
  (rationalCohomologyLinearEquivSingularCohomology X n).symm
    (singularClassOfSupportedSingularClass X Z n a)

@[simp]
lemma rationalCohomologyLinearEquivSingularCohomology_hypercohomologyClassOfSupportedSingularClass
    (Z : Set (ComplexPoint X)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) Z n) :
    rationalCohomologyLinearEquivSingularCohomology X n
      (hypercohomologyClassOfSupportedSingularClass X Z n a) =
        singularClassOfSupportedSingularClass X Z n a := by
  simp [hypercohomologyClassOfSupportedSingularClass]

end AlgebraicGeometry.ComplexPoint
