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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.HodgeFiltration
public import Other.LinearAlgebra.HodgeStructure

/-!
# Sanity checks on the Hodge filtration

The Hodge filtration is decreasing. The comparison map `H^n(X; K) → H^n_dR(X)` extends to a
complex-linear map `fieldToDeRhamComplexification` on `ℂ ⊗[K] H^n(X; K)`, along which the Hodge
filtration and the Hodge pieces of de Rham hypercohomology pull back to the complexification. Over
`ℚ` this map intertwines the conjugation of the complexification with the conjugation of de Rham
hypercohomology, so the pulled-back Hodge piece `F^p ⊓ conj F^q` is cut out by the pulled-back
filtration alone. Finally, the Hodge classes of the statement are the rational classes whose
complexifications lie in the pulled-back `(p,p)` piece.

None of this is needed to state the conjecture. `Other.AlgebraicGeometry.HodgeDecomposition` uses
it to relate the statement's Hodge classes to pure Hodge structures.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (K : Type) [Field K] [Algebra K ℂ]
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

attribute [local instance] hodgeFiltrationTopology

attribute [local instance] analyticHasDerivedCategory

/-- The Hodge filtration is decreasing: forms of degree at least `p'` have degree at least `p`
when `p ≤ p'`. -/
lemma hodgeFiltration_antitone (n : ℤ) : Antitone fun p ↦ hodgeFiltration X p n := by
  intro p p' hpp' α hα
  obtain ⟨β, rfl⟩ := hα
  obtain ⟨g, hg⟩ := HomologicalComplex.exists_comp_stupidTruncInclusion
    (holomorphicDeRhamComplexInt X) (ComplexShape.embeddingUpIntGE p)
    (ComplexShape.embeddingUpIntGE p') fun i ↦
      ⟨(p' - p).toNat + i, by simp only [ComplexShape.embeddingUpIntGE_f]; omega⟩
  exact ⟨hypercohomologyMap X g n β,
    (hypercohomologyMap_comp_apply X g (hodgeFilteredDeRhamInclusion X p) n β).symm.trans
      (congrArg (fun f ↦ hypercohomologyMap X f n β) hg)⟩

lemma hodgeFiltrationComplexSubmodule_antitone (n : ℤ) :
    Antitone fun p ↦ hodgeFiltrationComplexSubmodule X p n :=
  fun _ _ h _ hα ↦ hodgeFiltration_antitone X n h hα

/-- The balanced map that extends the comparison map after scalar extension from `K` to `ℂ`. -/
def fieldToDeRhamComplexificationBilinear (n : ℤ) :
    ℂ →ₗ[ℂ] H^n(X; K) →ₗ[K] DeRhamHypercohomology X n where
  toFun c := c • (fieldToDeRhamCohomologyLinear K X n)
  map_add' a b := by
    ext α
    simp [add_smul]
  map_smul' a b := by
    ext α
    simp [mul_smul]

/-- The complex-linear comparison from the complexification of constant-sheaf cohomology to
holomorphic de Rham hypercohomology. -/
def fieldToDeRhamComplexification (n : ℤ) :
    ℂ ⊗[K] H^n(X; K) →ₗ[ℂ] DeRhamHypercohomology X n :=
  TensorProduct.AlgebraTensorModule.lift (fieldToDeRhamComplexificationBilinear K X n)

@[simp] lemma fieldToDeRhamComplexification_tmul (n : ℤ) (c : ℂ) (α : H^n(X; K)) :
    fieldToDeRhamComplexification K X n (c ⊗ₜ[K] α) = c • fieldToDeRhamCohomology K X n α :=
  rfl

/-- On the rational lattice, the complexified comparison agrees with the original map. -/
@[simp] lemma fieldToDeRhamComplexification_ofField (n : ℤ) (α : H^n(X; K)) :
    fieldToDeRhamComplexification K X n (1 ⊗ₜ[K] α) = fieldToDeRhamCohomology K X n α := by
  simp

/-- The de Rham Hodge filtration pulled back to the complexification of constant-sheaf
cohomology along the comparison map. -/
def complexifiedFieldHodgeFiltration (p n : ℤ) : Submodule ℂ (ℂ ⊗[K] H^n(X; K)) :=
  (hodgeFiltrationComplexSubmodule X p n).comap (fieldToDeRhamComplexification K X n)

/-- The de Rham Hodge piece `F^p ⊓ conj F^q` pulled back to the complexification of
constant-sheaf cohomology along the comparison map. -/
def complexifiedFieldHodgePiece (p q n : ℤ) : Submodule ℂ (ℂ ⊗[K] H^n(X; K)) :=
  (hodgePiece X p q n).comap (fieldToDeRhamComplexification K X n)

/-- Pulled back to the complexification and indexed by naturals, the Hodge filtration is still
decreasing. -/
lemma complexifiedFieldHodgeFiltration_antitone (n : ℤ) :
    Antitone fun p : ℕ ↦ complexifiedFieldHodgeFiltration K X p n :=
  fun _ _ h ↦ Submodule.comap_mono
    (hodgeFiltrationComplexSubmodule_antitone X n (by exact_mod_cast h))

/-- The complexified comparison map carries the conjugation of `ℂ ⊗[ℚ] H^n(X; ℚ)` to the
conjugation of de Rham hypercohomology: rational classes are fixed by both. -/
lemma fieldToDeRhamComplexification_conjugate (n : ℤ) (x : ℂ ⊗[ℚ] H^n(X; ℚ)) :
    fieldToDeRhamComplexification ℚ X n (HodgeStructure.conjugate _ x) =
      deRhamConj X n (fieldToDeRhamComplexification ℚ X n x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z α =>
    rw [HodgeStructure.conjugate_tmul, fieldToDeRhamComplexification_tmul,
      fieldToDeRhamComplexification_tmul, deRhamConj_smul,
      deRhamConj_fieldToDeRhamCohomology ℚ X (fun q ↦ by simp) n α]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Pulled back to `ℂ ⊗[ℚ] H^n(X; ℚ)`, the Hodge piece `F^p ⊓ conj F^q` is cut out by the
pulled-back filtration and the conjugation of the complexification. -/
lemma complexifiedFieldHodgePiece_eq_inf_comap (p q n : ℤ) :
    complexifiedFieldHodgePiece ℚ X p q n =
      complexifiedFieldHodgeFiltration ℚ X p n ⊓
        (complexifiedFieldHodgeFiltration ℚ X q n).comap (HodgeStructure.conjugate _) := by
  ext x
  simp only [complexifiedFieldHodgePiece, complexifiedFieldHodgeFiltration, Submodule.mem_comap,
    Submodule.mem_inf, mem_hodgePiece_iff, fieldToDeRhamComplexification_conjugate]
  rfl

/-- The Hodge classes are the classes whose complexifications lie in the pulled-back `(p,p)`
piece. -/
lemma hodgeClasses_eq_comap_ofBase (p : ℕ) :
    Hdg^p(K; X) =
      Submodule.comap (HodgeStructure.ofBase K (H^(2 * p)(X; K)))
        ((complexifiedFieldHodgePiece K X p p (2 * p)).restrictScalars K) := by
  ext α
  change fieldToDeRhamCohomology K X (2 * (p : ℤ)) α ∈ hodgePiece X p p (2 * (p : ℤ)) ↔
    fieldToDeRhamComplexification K X (2 * (p : ℤ))
      (HodgeStructure.ofBase K (H^(2 * (p : ℤ))(X; K)) α) ∈ hodgePiece X p p (2 * (p : ℤ))
  rw [HodgeStructure.ofBase_apply, fieldToDeRhamComplexification_ofField]

end AlgebraicGeometry.ComplexPoint
