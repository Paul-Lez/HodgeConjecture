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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.FlasqueAcyclic
import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.InjectiveFlasque

open CategoryTheory Limits Opposite TopologicalSpace

@[expose] public noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

attribute [local instance] TopCat.Sheaf.extAddCommGroup

namespace IsFlasque

/-- The degree-zero `Ext` group from `globalSectionsSource` is the group of global sections. This
is `CategoryTheory.Sheaf.H.equiv₀` as an equivalence of types, so that no
reducibility-sensitive typeclass search is needed. -/
def globalSectionsEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Abelian.Ext (globalSectionsSource (X := X)) F 0 ≃
      F.obj.obj (op (⊤ : Opens X)) :=
  letI : AddCommGroup (CategoryTheory.Sheaf.H F 0) := extAddCommGroup
  (CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop).toEquiv

/-- `globalSectionsEquiv` carries postcomposition to the map on global sections. -/
lemma globalSectionsEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (x : Abelian.Ext (globalSectionsSource (X := X)) F 0) :
    f.hom.app (op (⊤ : Opens X)) (globalSectionsEquiv F x) =
      globalSectionsEquiv G (x.comp (Abelian.Ext.mk₀ f) (add_zero 0)) :=
  CategoryTheory.Sheaf.H.equiv₀_naturality isTerminalTop f x

/-- Every positive-degree cohomology class of a flasque sheaf is zero. -/
theorem cohomology_succ_eq_zero
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque] (n : ℕ)
    (x : Abelian.Ext (globalSectionsSource (X := X)) F (n + 1)) : x = 0 := by
  induction n generalizing F with
  | zero =>
      let : AddCommGroup
          (Abelian.Ext (globalSectionsSource (X := X)) F 1) :=
        extAddCommGroup
      let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
        ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
          (cokernel.condition (Injective.ι F))
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
      let : S.X₁.IsFlasque := by dsimp [S]; infer_instance
      let : S.X₂.IsFlasque := by dsimp [S]; infer_instance
      let : S.X₃.IsFlasque := of_shortExact_of_isFlasque₁₂ hS
      let : Injective S.X₂ := by dsimp [S]; infer_instance
      let : AddCommGroup
          (Abelian.Ext (globalSectionsSource (X := X)) S.X₂ 1) :=
        extAddCommGroup
      let : AddCommGroup
          (Abelian.Ext (globalSectionsSource (X := X)) S.X₃ 0) :=
        extAddCommGroup
      have hx : x.comp (Abelian.Ext.mk₀ S.f) (add_zero 1) = 0 := by
        apply Abelian.Ext.eq_zero_of_injective
      obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS x hx rfl
      have hg : Function.Surjective
          (S.g.hom.app (op (⊤ : Opens X))) :=
        (AddCommGrpCat.epi_iff_surjective _).mp
          (epi_of_shortExact (U := (⊤ : Opens X)) hS)
      obtain ⟨z, hz⟩ := hg (globalSectionsEquiv S.X₃ y)
      let z' : Abelian.Ext (globalSectionsSource (X := X)) S.X₂ 0 :=
        (globalSectionsEquiv S.X₂).symm z
      let : AddCommGroup
          (Abelian.Ext (globalSectionsSource (X := X)) S.X₂ 0) :=
        extAddCommGroup
      have hz' : z'.comp (Abelian.Ext.mk₀ S.g) (add_zero 0) = y := by
        apply (globalSectionsEquiv S.X₃).injective
        calc
          globalSectionsEquiv S.X₃
              (z'.comp (Abelian.Ext.mk₀ S.g) (add_zero 0)) =
              S.g.hom.app (op (⊤ : Opens X))
                (globalSectionsEquiv S.X₂ z') :=
            (globalSectionsEquiv_naturality S.g z').symm
          _ = globalSectionsEquiv S.X₃ y := by
            simpa only [z', Equiv.apply_symm_apply] using hz
      rw [← hy, ← hz', Abelian.Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
        Abelian.Ext.comp_zero]
  | succ n ih =>
      let : AddCommGroup
          (Abelian.Ext (globalSectionsSource (X := X)) F (n + 2)) :=
        extAddCommGroup
      let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
        ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
          (cokernel.condition (Injective.ι F))
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
      let : S.X₁.IsFlasque := by dsimp [S]; infer_instance
      let : S.X₂.IsFlasque := by dsimp [S]; infer_instance
      let : S.X₃.IsFlasque := of_shortExact_of_isFlasque₁₂ hS
      let : Injective S.X₂ := by dsimp [S]; infer_instance
      let : AddCommGroup
          (Abelian.Ext (globalSectionsSource (X := X)) S.X₂ (n + 2)) :=
        extAddCommGroup
      let : AddCommGroup
          (Abelian.Ext (globalSectionsSource (X := X)) S.X₃ (n + 1)) :=
        extAddCommGroup
      have hx : x.comp (Abelian.Ext.mk₀ S.f) (add_zero (n + 2)) = 0 := by
        apply Abelian.Ext.eq_zero_of_injective
      obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS x hx rfl
      have hy0 : y = 0 := ih S.X₃ y
      rw [← hy, hy0]
      exact Abelian.Ext.zero_comp _ _ _ _ _

/-- A flasque sheaf of abelian groups has subsingleton cohomology in positive degree. -/
theorem subsingleton_cohomology_succ
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque] (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  constructor
  intro x y
  change Abelian.Ext (globalSectionsSource (X := X)) F (n + 1) at x y
  rw [cohomology_succ_eq_zero F n x, cohomology_succ_eq_zero F n y]

end TopCat.Sheaf.IsFlasque
