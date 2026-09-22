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

public import Other.AlgebraicTopology.WindingCochainTransition

/-!
# The raw two-open Čech--cochain total complex

For two cochain complexes on two members of an open cover and their common overlap, this file
defines the Čech--singular total complex directly.  In degree `n` it is

`K₀ⁿ ⊞ K₁ⁿ ⊞ K₀₁ⁿ⁻¹`.

Thus, two local cocycles which differ on the overlap by the differential of a *specified*
lower cochain form a literal total cocycle.  This is the raw cochain version of the first
Čech descent step; no passage to cohomology classes or choice of a representative occurs.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicTopology.Singular

variable {K₀ K₁ K₀₁ : CochainComplex (ModuleCat ℚ) ℤ}

/-- The alternating restriction from the two members of a cover to their overlap. -/
def twoOpenCechDifference (r₀ : K₀ ⟶ K₀₁) (r₁ : K₁ ⟶ K₀₁) :
    K₀ ⊞ K₁ ⟶ K₀₁ :=
  biprod.desc r₀ (-r₁)

/-- The two-open Čech--singular total complex, presented as the mapping cone of the alternating
restriction map.  Its term in degree `n - 1` is canonically
`K₀.X n ⊞ K₁.X n ⊞ K₀₁.X (n - 1)`. -/
def twoOpenCechTotal (r₀ : K₀ ⟶ K₀₁) (r₁ : K₁ ⟶ K₀₁) :
    CochainComplex (ModuleCat ℚ) ℤ :=
  CochainComplex.mappingCone (twoOpenCechDifference r₀ r₁)

/-- The literal total cochain represented by local cochains `a₀`, `a₁` and an overlap
cochain `b`.  The degree of `b` is one lower, as required by Čech totalization. -/
def twoOpenCechCochain (r₀ : K₀ ⟶ K₀₁) (r₁ : K₁ ⟶ K₀₁) (n : ℤ)
    (a₀ : K₀.X n) (a₁ : K₁.X n) (b : K₀₁.X (n - 1)) :
    (twoOpenCechTotal r₀ r₁).X (n - 1) :=
  let δ := twoOpenCechDifference r₀ r₁
  (CochainComplex.mappingCone.inl δ).v n (n - 1) (by omega)
      (((biprod.inl : K₀ ⟶ K₀ ⊞ K₁).f n).hom a₀ +
        ((biprod.inr : K₁ ⟶ K₀ ⊞ K₁).f n).hom a₁) +
    (CochainComplex.mappingCone.inr δ).f (n - 1) b

/-!
The following closure lemma is deliberately stated in the elementary elementwise form used by
the winding construction.  Its compatibility equation says that the alternating restriction of
the two local cochains is `-d b`.  Equivalently, the second local cochain is the first plus the
displayed overlap coboundary.
-/

theorem twoOpenCechCochain_closed (r₀ : K₀ ⟶ K₀₁) (r₁ : K₁ ⟶ K₀₁) (n : ℤ)
    (a₀ : K₀.X n) (a₁ : K₁.X n) (b : K₀₁.X (n - 1))
    (ha₀ : K₀.d n (n + 1) a₀ = 0) (ha₁ : K₁.d n (n + 1) a₁ = 0)
    (hcompat : r₀.f n a₀ - r₁.f n a₁ =
      -K₀₁.d (n - 1) n b) :
    (twoOpenCechTotal r₀ r₁).d (n - 1) n
      (twoOpenCechCochain r₀ r₁ n a₀ a₁ b) = 0 := by
  let F := K₀ ⊞ K₁
  let δ : F ⟶ K₀₁ := twoOpenCechDifference r₀ r₁
  let x : F.X n :=
    ((biprod.inl : K₀ ⟶ F).f n).hom a₀ + ((biprod.inr : K₁ ⟶ F).f n).hom a₁
  have hF : F.d n (n + 1) x = 0 := by
    change ((K₀ ⊞ K₁).d n (n + 1))
      (((biprod.inl : K₀ ⟶ K₀ ⊞ K₁).f n).hom a₀ +
        ((biprod.inr : K₁ ⟶ K₀ ⊞ K₁).f n).hom a₁) = 0
    rw [map_add]
    have h₀ := ConcreteCategory.congr_hom ((biprod.inl : K₀ ⟶ F).comm n (n + 1)) a₀
    have h₁ := ConcreteCategory.congr_hom ((biprod.inr : K₁ ⟶ F).comm n (n + 1)) a₁
    simp only [ConcreteCategory.comp_apply] at h₀ h₁
    rw [h₀, h₁, ha₀, ha₁, map_zero, map_zero, add_zero]
  have hδ : δ.f n x = r₀.f n a₀ - r₁.f n a₁ := by
    have hδ₀ : (biprod.inl : K₀ ⟶ F) ≫ δ = r₀ := by
      dsimp [δ, F, twoOpenCechDifference]
      simp
    have hδ₁ : (biprod.inr : K₁ ⟶ F) ≫ δ = -r₁ := by
      dsimp [δ, F, twoOpenCechDifference]
      simp
    have e₀ := ConcreteCategory.congr_hom (congrArg (fun f => f.f n) hδ₀) a₀
    have e₁ := ConcreteCategory.congr_hom (congrArg (fun f => f.f n) hδ₁) a₁
    have e₁' : δ.f n (((biprod.inr : K₁ ⟶ F).f n).hom a₁) = -r₁.f n a₁ := by
      change ((((biprod.inr : K₁ ⟶ F) ≫ δ).f n).hom a₁) = _
      rw [hδ₁]
      exact LinearMap.neg_apply _ _
    dsimp [x]
    rw [map_add]
    simpa only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply, sub_eq_add_neg] using
      congrArg₂ (· + ·) e₀ e₁'
  have hinl :
      (CochainComplex.mappingCone δ).d (n - 1) n
          ((CochainComplex.mappingCone.inl δ).v n (n - 1) (by omega) x) =
        (CochainComplex.mappingCone.inr δ).f n (δ.f n x) -
          (CochainComplex.mappingCone.inl δ).v (n + 1) n (by omega)
            (F.d n (n + 1) x) := by
    change (((CochainComplex.mappingCone.inl δ).v n (n - 1) (by omega) ≫
      (CochainComplex.mappingCone δ).d (n - 1) n).hom x) = _
    rw [CochainComplex.mappingCone.inl_v_d δ n (n - 1) (n + 1)
      (by omega) (by omega)]
    rfl
  have hinr :
      (CochainComplex.mappingCone δ).d (n - 1) n
          ((CochainComplex.mappingCone.inr δ).f (n - 1) b) =
        (CochainComplex.mappingCone.inr δ).f n (K₀₁.d (n - 1) n b) := by
    change (((CochainComplex.mappingCone.inr δ).f (n - 1) ≫
      (CochainComplex.mappingCone δ).d (n - 1) n).hom b) = _
    rw [CochainComplex.mappingCone.inr_f_d]
    rfl
  have hcone :
      (CochainComplex.mappingCone δ).d (n - 1) n
          ((CochainComplex.mappingCone.inl δ).v n (n - 1) (by omega) x +
            (CochainComplex.mappingCone.inr δ).f (n - 1) b) = 0 := by
    rw [map_add, hinl, hinr, hF, map_zero, sub_zero, ← map_add]
    rw [hδ, hcompat, neg_add_cancel]
    simp
  change (CochainComplex.mappingCone δ).d (n - 1) n
      ((CochainComplex.mappingCone.inl δ).v n (n - 1) (by omega) x +
        (CochainComplex.mappingCone.inr δ).f (n - 1) b) = 0
  exact hcone

end AlgebraicTopology.Singular
