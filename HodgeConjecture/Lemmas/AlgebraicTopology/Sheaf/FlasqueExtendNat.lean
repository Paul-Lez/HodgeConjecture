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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.FlasqueQuasiIso
public import HodgeConjecture.Lemmas.Algebra.Homology.MapExtendNaturality

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

/-!
# Global sections of quasi-isomorphisms between flasque complexes indexed by `ℕ`

A quasi-isomorphism of nonnegatively indexed termwise-flasque complexes of sheaves remains a
quasi-isomorphism after taking global sections.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace TopCat.Sheaf

/-- Extension by zero of a natural-number-indexed termwise-flasque complex remains
termwise flasque. -/
theorem extendNat_term_isFlasque
    {Y : TopCat.{0}} (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℕ)
    (hK : ∀ m, (K.X m).IsFlasque) (q : ℤ) :
    ((K.extend ComplexShape.embeddingUpNat).X q).IsFlasque := by
  by_cases hq : ∃ m : ℕ, (m : ℤ) = q
  · obtain ⟨m, rfl⟩ := hq
    let e := K.extendXIso ComplexShape.embeddingUpNat (i := m) rfl
    let hP : TopCat.Presheaf.IsFlasque (K.X m).obj := hK m
    change TopCat.Presheaf.IsFlasque
      ((K.extend ComplexShape.embeddingUpNat).X (m : ℤ)).obj
    exact @TopCat.Presheaf.IsFlasque.of_iso _ _ _
      ((TopCat.Sheaf.forget AddCommGrpCat Y).mapIso e) hP
  · apply TopCat.Sheaf.IsFlasque.of_isZero
    exact K.isZero_extend_X ComplexShape.embeddingUpNat q
      (fun i hi ↦ hq ⟨i, hi⟩)

/-- A quasi-isomorphism of nonnegative termwise-flasque sheaf complexes remains a
quasi-isomorphism after taking global sections. -/
theorem globalSectionsNat_map_quasiIso
    {Y : TopCat.{0}}
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℕ}
    (f : K ⟶ L) [QuasiIso f]
    (hK : ∀ m, (K.X m).IsFlasque) (hL : ∀ m, (L.X m).IsFlasque) :
    QuasiIso
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex (ComplexShape.up ℕ)).map f) := by
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let KInt : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ :=
    K.extend ComplexShape.embeddingUpNat
  let LInt : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ :=
    L.extend ComplexShape.embeddingUpNat
  let fInt : KInt ⟶ LInt :=
    HomologicalComplex.extendMap f ComplexShape.embeddingUpNat
  let eK := HomologicalComplex.mapExtendCanonicalIso Γ K ComplexShape.embeddingUpNat
  let eL := HomologicalComplex.mapExtendCanonicalIso Γ L ComplexShape.embeddingUpNat
  let : QuasiIso ((Γ.mapHomologicalComplex ℤᵘᵖ).map fInt) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      fInt 0 0 (extendNat_term_isFlasque K hK) (extendNat_term_isFlasque L hL)
  have h : HomologicalComplex.extendMap
        ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map f)
          ComplexShape.embeddingUpNat ≫ eL.inv =
      eK.inv ≫ (Γ.mapHomologicalComplex ℤᵘᵖ).map fInt :=
    HomologicalComplex.mapExtendCanonicalIso_inv_naturality Γ f ComplexShape.embeddingUpNat
  have hcomp : QuasiIso
      (HomologicalComplex.extendMap
        ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map f)
          ComplexShape.embeddingUpNat ≫ eL.inv) := by
    rw [h]
    infer_instance
  have hext : QuasiIso (HomologicalComplex.extendMap
      ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map f)
        ComplexShape.embeddingUpNat) :=
    quasiIso_of_comp_right _ eL.inv
  exact (HomologicalComplex.quasiIso_extendMap_iff
    ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map f)
      ComplexShape.embeddingUpNat).mp hext

end TopCat.Sheaf

end
