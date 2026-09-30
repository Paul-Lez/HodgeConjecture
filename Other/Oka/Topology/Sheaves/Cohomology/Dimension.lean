/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Topology.Sheaves.Cohomology.MayerVietoris

/-!
# Cohomological dimension bounds from finite covers

Let `F` be an abelian sheaf on `X : TopCat` and let `U : ι → Opens X` be a finite family of
opens such that `F` is acyclic on every nonempty finite intersection `U_I = ⨅_{i ∈ I} U i`.
Then `Hᵠ(⋃ᵢ U i, F) = 0` for `q ≥ card ι`. The proof is by induction on the number of opens,
using the Mayer–Vietoris sequence for `W = U₀ ∪ V`, `V = ⋃_{i ≥ 1} U i`, where
`U₀ ∩ V = ⋃_{i ≥ 1} (U₀ ∩ U i)` is again covered by `card ι - 1` opens of the same kind.

All statements are first proved for Mathlib's cohomology of opens
`CategoryTheory.Sheaf.H' F q W = Extᵠ(ℤ[W], F)`, and then transferred to the cohomology of
restricted sheaves `Hᵠ(W, F|_W)` via `TopCat.Sheaf.H'AddEquiv`.

## Main results

* `TopCat.Sheaf.subsingleton_H'_bot`: `H'ᵠ(∅, F) = 0` for all `q`.
* `TopCat.Sheaf.subsingleton_H'_iSup_of_mem`: if `𝒜` is a set of opens closed under `⊓` on which
  `F` is acyclic, then `H'ᵠ(⋃ᵢ U i) = 0` for `q ≥ card ι` whenever all `U i ∈ 𝒜`.
* `TopCat.Sheaf.subsingleton_H'_iSup`, `TopCat.Sheaf.subsingleton_H_restrictOpen_of_iSup_eq`,
  `TopCat.Sheaf.subsingleton_H_of_iSup_eq_top`: the bound for a finite cover acyclic on all
  nonempty finite intersections, for `H'`, for `Hᵠ(W, F|_W)` with `W = ⋃ᵢ U i`, and for
  `Hᵠ(X, F)` when the `U i` cover `X`.
* `TopCat.Sheaf.subsingleton_H_restrictOpen_of_subset`: the same bound for the union of a
  subfamily `(U i)_{i ∈ S}`, for `q ≥ card S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (F : AbSheaf X)

/-- `ℤ[∅]` is a zero object: morphisms out of it are sections over `∅`. -/
lemma isZero_freeYoneda_bot : IsZero (freeYoneda (⊥ : Opens X)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (freeYonedaHomEquiv (⊥ : Opens X) (freeYoneda ⊥)).injective
  have := AddCommGrpCat.subsingleton_of_isZero
    (TopCat.Sheaf.isTerminalOfEmpty (C := AddCommGrpCat.{u}) (freeYoneda (⊥ : Opens X))).isZero
  exact Subsingleton.elim _ _

/-- The cohomology of the empty open vanishes in all degrees. -/
lemma subsingleton_H'_bot (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H'.{u} F q (⊥ : Opens X)) := by
  change Subsingleton (Ext (freeYoneda (⊥ : Opens X)) F q)
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← Ext.mk₀_id_comp x, (isZero_freeYoneda_bot (X := X)).eq_of_src (𝟙 _) 0, Ext.mk₀_zero,
    Ext.zero_comp]

/-- Mayer–Vietoris: if `H'^{q-1}(U ∩ V)`, `H'^q(U)` and `H'^q(V)` vanish, so does
`H'^q(U ∪ V)`. -/
lemma subsingleton_H'_sup (U V : Opens X) (q : ℕ)
    (h₁ : Subsingleton (CategoryTheory.Sheaf.H'.{u} F q (U ⊓ V)))
    (h₂ : Subsingleton (CategoryTheory.Sheaf.H'.{u} F (q + 1) U))
    (h₃ : Subsingleton (CategoryTheory.Sheaf.H'.{u} F (q + 1) V)) :
    Subsingleton (CategoryTheory.Sheaf.H'.{u} F (q + 1) (U ⊔ V)) := by
  have hS := mayerVietorisSequence_exact U V F q (q + 1) rfl
  have hex := (ShortComplex.ab_exact_iff_function_exact _).1 (hS.exact 2)
  have hA : IsZero (CategoryTheory.Sheaf.H'.{u} F (q + 1) U ⊞
      CategoryTheory.Sheaf.H'.{u} F (q + 1) V) :=
    (biprod_isZero_iff _ _).2
      ⟨AddCommGrpCat.isZero_of_subsingleton _, AddCommGrpCat.isZero_of_subsingleton _⟩
  have h₄ : Subsingleton
      ((mayerVietorisSequence U V F q (q + 1) rfl).sc hS.toIsComplex 2).X₃ :=
    AddCommGrpCat.subsingleton_of_isZero hA
  have h₅ : Subsingleton
      ((mayerVietorisSequence U V F q (q + 1) rfl).sc hS.toIsComplex 2).X₁ := h₁
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, hy⟩ := (hex x).1 (Subsingleton.elim _ _)
  rw [← hy, Subsingleton.elim y 0]
  exact map_zero _

/-- A finite union of opens is the first open union the union of the others. -/
lemma iSup_fin_succ_eq {m : ℕ} (U : Fin (m + 1) → Opens X) :
    ⨆ i, U i = U 0 ⊔ ⨆ i : Fin m, U i.succ := by
  refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup U 0) (iSup_le fun i => le_iSup U _))
  refine Fin.cases le_sup_left (fun j => ?_) i
  exact le_sup_of_le_right (le_iSup (fun i : Fin m => U i.succ) j)

/-- **Cohomological dimension bound, abstract form.** Let `𝒜` be a set of opens, closed under
binary intersections, on each of which `F` has vanishing higher cohomology. Then for opens
`U i ∈ 𝒜` indexed by a finite type, `H'ᵠ(⋃ᵢ U i, F) = 0` for `q ≥ card ι`. -/
theorem subsingleton_H'_iSup_of_mem (𝒜 : Set (Opens X))
    (h𝒜 : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ⊓ B ∈ 𝒜)
    (hF : ∀ A ∈ 𝒜, ∀ q, 0 < q → Subsingleton (CategoryTheory.Sheaf.H'.{u} F q A))
    {ι : Type*} [Fintype ι] (U : ι → Opens X) (hU : ∀ i, U i ∈ 𝒜) (q : ℕ)
    (hq : Fintype.card ι ≤ q) :
    Subsingleton (CategoryTheory.Sheaf.H'.{u} F q (⨆ i, U i)) := by
  suffices h : ∀ (m : ℕ) (U : Fin m → Opens X), (∀ i, U i ∈ 𝒜) → ∀ q, m ≤ q →
      Subsingleton (CategoryTheory.Sheaf.H'.{u} F q (⨆ i, U i)) by
    let e := Fintype.equivFin ι
    have : ⨆ i, U i = ⨆ j, U (e.symm j) := (e.symm.iSup_comp (g := U)).symm
    rw [this]
    exact h _ _ (fun j => hU _) q hq
  intro m
  induction m with
  | zero =>
    intro U _ q _
    rw [iSup_of_empty]
    exact subsingleton_H'_bot F q
  | succ m ih =>
    intro U hU q hq
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [iSup_fin_succ_eq]
    apply subsingleton_H'_sup
    · rw [inf_iSup_eq]
      exact ih (fun i => U 0 ⊓ U i.succ) (fun i => h𝒜 _ (hU 0) _ (hU _)) q (by omega)
    · exact hF _ (hU 0) _ (by omega)
    · exact ih (fun i => U i.succ) (fun i => hU _) (q + 1) (by omega)

/-- The set of nonempty finite intersections `U_I = ⨅_{i ∈ I} U i` of a family of opens. -/
def finiteInters {ι : Type*} (U : ι → Opens X) : Set (Opens X) :=
  {W | ∃ I : Finset ι, I.Nonempty ∧ W = ⨅ i ∈ I, U i}

/-- Each `U i` is a finite intersection. -/
lemma mem_finiteInters {ι : Type*} (U : ι → Opens X) (i : ι) : U i ∈ finiteInters U :=
  ⟨{i}, Finset.singleton_nonempty i, by simp⟩

/-- Finite intersections are closed under `⊓`. -/
lemma inf_mem_finiteInters {ι : Type*} (U : ι → Opens X) {A B : Opens X}
    (hA : A ∈ finiteInters U) (hB : B ∈ finiteInters U) : A ⊓ B ∈ finiteInters U := by
  classical
  obtain ⟨I, hI, rfl⟩ := hA
  obtain ⟨J, -, rfl⟩ := hB
  exact ⟨I ∪ J, hI.mono Finset.subset_union_left, (Finset.iInf_union).symm⟩

/-- **Cohomological dimension bound** (for `H'`). If `F` has vanishing higher cohomology on
every nonempty finite intersection of the finitely many opens `U i`, then
`H'ᵠ(⋃ᵢ U i, F) = 0` for `q ≥ card ι`. -/
theorem subsingleton_H'_iSup {ι : Type*} [Fintype ι] (U : ι → Opens X)
    (hF : ∀ I : Finset ι, I.Nonempty → ∀ q, 0 < q →
      Subsingleton (CategoryTheory.Sheaf.H'.{u} F q (⨅ i ∈ I, U i)))
    (q : ℕ) (hq : Fintype.card ι ≤ q) :
    Subsingleton (CategoryTheory.Sheaf.H'.{u} F q (⨆ i, U i)) := by
  classical
  refine subsingleton_H'_iSup_of_mem F (finiteInters U)
    (fun A hA B hB => inf_mem_finiteInters U hA hB) ?_ U (mem_finiteInters U) q hq
  rintro _ ⟨I, hI, rfl⟩ q hq
  exact hF I hI q hq

/-- **Cohomological dimension bound.** Let `U : ι → Opens X` be a finite family with union `W`
such that `Hᵠ(U_I, F|_{U_I}) = 0` for `q ≥ 1` and every nonempty finite intersection
`U_I = ⨅_{i ∈ I} U i`. Then `Hᵠ(W, F|_W) = 0` for `q ≥ card ι`. -/
theorem subsingleton_H_restrictOpen_of_iSup_eq {ι : Type*} [Fintype ι] (U : ι → Opens X)
    {W : Opens X} (hW : ⨆ i, U i = W)
    (hF : ∀ I : Finset ι, I.Nonempty → ∀ q, 0 < q →
      Subsingleton (H ((restrictOpen (⨅ i ∈ I, U i)).obj F) q))
    (q : ℕ) (hq : Fintype.card ι ≤ q) :
    Subsingleton (H ((restrictOpen W).obj F) q) := by
  subst hW
  have := subsingleton_H'_iSup F U (fun I hI q hq =>
    have := hF I hI q hq
    (H'AddEquiv _ F q).toEquiv.subsingleton) q hq
  exact (H'AddEquiv _ F q).symm.toEquiv.subsingleton

/-- **Cohomological dimension bound for a cover.** If finitely many opens `U i` cover `X` and
`Hᵠ(U_I, F|_{U_I}) = 0` for `q ≥ 1` and every nonempty finite intersection `U_I`, then
`Hᵠ(X, F) = 0` for `q ≥ card ι`. -/
theorem subsingleton_H_of_iSup_eq_top {ι : Type*} [Fintype ι] (U : ι → Opens X)
    (hW : ⨆ i, U i = ⊤)
    (hF : ∀ I : Finset ι, I.Nonempty → ∀ q, 0 < q →
      Subsingleton (H ((restrictOpen (⨅ i ∈ I, U i)).obj F) q))
    (q : ℕ) (hq : Fintype.card ι ≤ q) :
    Subsingleton (H F q) := by
  have := subsingleton_H'_iSup F U (fun I hI q hq =>
    have := hF I hI q hq
    (H'AddEquiv _ F q).toEquiv.subsingleton) q hq
  rw [hW] at this
  exact (H'TopAddEquiv F q).symm.toEquiv.subsingleton

/-- **Cohomological dimension bound for a subfamily.** If `F` is acyclic on every nonempty
finite intersection of the finitely many opens `U i`, then for any `S : Finset ι` and
`W = ⋃_{i ∈ S} U i` we have `Hᵠ(W, F|_W) = 0` for `q ≥ card S` (in particular for
`q ≥ card ι`). -/
theorem subsingleton_H_restrictOpen_of_subset {ι : Type*} (U : ι → Opens X) (S : Finset ι)
    {W : Opens X} (hW : ⨆ i ∈ S, U i = W)
    (hF : ∀ I : Finset ι, I.Nonempty → ∀ q, 0 < q →
      Subsingleton (H ((restrictOpen (⨅ i ∈ I, U i)).obj F) q))
    (q : ℕ) (hq : S.card ≤ q) :
    Subsingleton (H ((restrictOpen W).obj F) q) := by
  classical
  refine subsingleton_H_restrictOpen_of_iSup_eq F (fun i : S => U i) ?_ ?_ q
    (by simpa using hq)
  · rw [← hW, iSup_subtype']
  · intro I hI q hq
    have h : ⨅ i ∈ I, U (i : ι) = ⨅ i ∈ I.map (Function.Embedding.subtype _), U i := by
      refine le_antisymm (le_iInf₂ fun i hi => ?_) (le_iInf₂ fun i hi => ?_)
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
        exact iInf₂_le j hj
      · exact iInf₂_le (f := fun i _ => U i) _ (Finset.mem_map_of_mem _ hi)
    rw [h]
    exact hF _ (hI.map) q hq

end TopCat.Sheaf

end
