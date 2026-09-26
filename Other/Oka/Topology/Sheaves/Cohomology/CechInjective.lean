/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Other.Oka.Topology.Sheaves.Cohomology.Cech

/-!
# Injective sheaves are Čech acyclic

For a family `U : ι → Opens X` (with `ι : Type u`) and `n : ℕ`, the free abelian presheaf
`K_n = TopCat.Presheaf.cechK U n`, `V ↦ ℤ[Fin (n + 1) → {i | V ⊆ U i}]`, represents Čech
`n`-cochains: morphisms `K_n ⟶ P` are the same as elements of `Čⁿ(U, P)`
(`TopCat.Presheaf.cechKHom`, `TopCat.Presheaf.cechKCochain`), compatibly with the differentials.
The complex `K_•` is sectionwise the chain complex of the full simplex on the set
`{i | V ⊆ U i}` (`TopCat.Presheaf.simplexChains`), which is exact in positive degrees by the
cone construction (`TopCat.Presheaf.simplexD_exact`). Applying `Hom(-, P)` for an injective
presheaf `P` therefore gives an exact complex:

* `TopCat.Presheaf.isCechAcyclic_of_injective`: an injective abelian presheaf has vanishing
  Čech cohomology in positive degrees for every family of opens;
* `TopCat.Presheaf.isCechAcyclic_of_injective_sheaf`: the same for an injective abelian sheaf
  (its underlying presheaf is injective since sheafification preserves monomorphisms).

No covering condition on `U` is needed.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite Simplicial

namespace TopCat.Presheaf

/-- The simplicial abelian group `[n] ↦ ℤ[Fin (n + 1) → S]`. -/
noncomputable def simplexChainsSimplicial (S : Type u) : SimplicialObject AddCommGrpCat.{u} where
  obj Δ := AddCommGrpCat.of (FreeAbelianGroup (Fin (Δ.unop.len + 1) → S))
  map θ := AddCommGrpCat.ofHom (FreeAbelianGroup.map fun σ => σ ∘ θ.unop.toOrderHom)
  map_id Δ := by
    ext σ
    simp
  map_comp θ θ' := by
    ext σ
    simp
    rfl

/-- The chain complex of the full simplex on `S`: in degree `n`, `ℤ[Fin (n + 1) → S]`. -/
noncomputable abbrev simplexChains (S : Type u) : ChainComplex AddCommGrpCat.{u} ℕ :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj (simplexChainsSimplicial S)

/-- The differential of `simplexChains S`, as a map of free abelian groups. -/
noncomputable def simplexD (S : Type u) (n : ℕ) :
    FreeAbelianGroup (Fin (n + 2) → S) →+ FreeAbelianGroup (Fin (n + 1) → S) :=
  ((simplexChains S).d (n + 1) n).hom

lemma simplexD_of (S : Type u) (n : ℕ) (σ : Fin (n + 2) → S) :
    simplexD S n (FreeAbelianGroup.of σ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • FreeAbelianGroup.of (σ ∘ i.succAbove) := by
  change ((simplexChains S).d (n + 1) n) (FreeAbelianGroup.of σ) = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  erw [AddCommGrpCat.finsetSum_apply]
  rfl


lemma cons_comp_succAbove_succ {S : Type u} {n : ℕ} (s₀ : S) (σ : Fin (n + 1) → S)
    (k : Fin (n + 1)) :
    (Fin.cons s₀ σ : Fin (n + 2) → S) ∘ k.succ.succAbove = Fin.cons s₀ (σ ∘ k.succAbove) := by
  funext a
  cases a using Fin.cases <;> simp [Fin.succ_succAbove_succ]

/-- The cone contraction `σ ↦ (s₀, σ)` of the chains on the full simplex. -/
noncomputable def simplexCone {S : Type u} (s₀ : S) (n : ℕ) :
    FreeAbelianGroup (Fin (n + 1) → S) →+ FreeAbelianGroup (Fin (n + 2) → S) :=
  FreeAbelianGroup.map fun σ => (Fin.cons s₀ σ : Fin (n + 2) → S)

lemma simplexChains_homotopy {S : Type u} (s₀ : S) (n : ℕ)
    (x : FreeAbelianGroup (Fin (n + 2) → S)) :
    simplexD S (n + 1) (simplexCone s₀ (n + 1) x) + simplexCone s₀ n (simplexD S n x) = x := by
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp
  | of σ =>
    simp only [simplexCone, FreeAbelianGroup.map_of_apply]
    rw [simplexD_of, simplexD_of, Fin.sum_univ_succ, map_sum]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.val_succ, pow_succ,
      map_zsmul, FreeAbelianGroup.map_of_apply, cons_comp_succAbove_succ]
    have : (Fin.cons s₀ σ : Fin (n + 3) → S) ∘ Fin.succ = σ := by
      funext a; simp
    rw [this]
    simp [mul_neg, neg_smul, Finset.sum_neg_distrib]
  | neg x hx => rw [map_neg, map_neg, map_neg, map_neg, ← neg_add, hx]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, add_add_add_comm, hx, hy]


/-- The chains on the full simplex on `S` are exact in positive degrees. -/
lemma simplexD_exact (S : Type u) (n : ℕ) (x : FreeAbelianGroup (Fin (n + 2) → S))
    (hx : simplexD S n x = 0) : ∃ y, simplexD S (n + 1) y = x := by
  by_cases hS : Nonempty S
  · obtain ⟨s₀⟩ := hS
    refine ⟨simplexCone s₀ (n + 1) x, ?_⟩
    have := simplexChains_homotopy s₀ n x
    rwa [hx, map_zero, add_zero] at this
  · have h0 : ∀ y : FreeAbelianGroup (Fin (n + 2) → S), y = 0 := fun y => by
      induction y using FreeAbelianGroup.induction_on with
      | zero => rfl
      | of σ => exact (hS ⟨σ 0⟩).elim
      | neg y hy => rw [hy, neg_zero]
      | add y z hy hz => rw [hy, hz, add_zero]
    exact ⟨0, by rw [map_zero, h0 x]⟩

lemma simplexD_comp (S : Type u) (n : ℕ) (x : FreeAbelianGroup (Fin (n + 3) → S)) :
    simplexD S n (simplexD S (n + 1) x) = 0 :=
  ConcreteCategory.congr_hom ((simplexChains S).d_comp_d (n + 2) (n + 1) n) x

lemma simplexD_map {S S' : Type u} (f : S → S') (n : ℕ) (x : FreeAbelianGroup (Fin (n + 2) → S)) :
    simplexD S' n (FreeAbelianGroup.map (fun σ => f ∘ σ) x) =
      FreeAbelianGroup.map (fun σ => f ∘ σ) (simplexD S n x) := by
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp
  | of σ =>
    simp only [FreeAbelianGroup.map_of_apply, simplexD_of, map_sum, map_zsmul]
    rfl
  | neg x hx => rw [map_neg, map_neg, map_neg, map_neg, hx]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]


section Resolution

lemma freeHom_ext {S : Type u} {A : AddCommGrpCat.{u}}
    {f g : AddCommGrpCat.of (FreeAbelianGroup S) ⟶ A}
    (h : ∀ σ, f (FreeAbelianGroup.of σ) = g (FreeAbelianGroup.of σ)) : f = g :=
  AddCommGrpCat.hom_ext (FreeAbelianGroup.lift_ext _ _ h)

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- The indices `i` with `V ⊆ U i`. -/
abbrev cechIdx (V : Opens X) : Type u := {i : ι // V ≤ U i}

/-- The inclusion `cechIdx U V → cechIdx U V'` for `V' ⊆ V`. -/
def cechIdxMap {V V' : Opens X} (h : V' ≤ V) (i : cechIdx U V) : cechIdx U V' :=
  ⟨i.1, h.trans i.2⟩

/-- The presheaf `V ↦ ℤ[Fin (n + 1) → {i | V ⊆ U i}]`: the free abelian presheaf on the
`n`-simplices of the Čech nerve. Morphisms out of it are Čech `n`-cochains
(`TopCat.Presheaf.cechKHom`, `TopCat.Presheaf.cechKCochain`). -/
noncomputable def cechK (n : ℕ) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (FreeAbelianGroup (Fin (n + 1) → cechIdx U V.unop))
  map f := AddCommGrpCat.ofHom
    (FreeAbelianGroup.map fun σ => cechIdxMap U (leOfHom f.unop) ∘ σ)
  map_id V := freeHom_ext fun σ => by
    change FreeAbelianGroup.map _ (FreeAbelianGroup.of σ) = FreeAbelianGroup.of σ
    rw [FreeAbelianGroup.map_of_apply]
    rfl
  map_comp f g := freeHom_ext fun σ => by
    change FreeAbelianGroup.map _ (FreeAbelianGroup.of σ) =
      FreeAbelianGroup.map _ (FreeAbelianGroup.map _ (FreeAbelianGroup.of σ))
    simp only [FreeAbelianGroup.map_of_apply]
    rfl

lemma cechK_map_of {n : ℕ} {V V' : (Opens X)ᵒᵖ} (f : V ⟶ V')
    (σ : Fin (n + 1) → cechIdx U V.unop) :
    (cechK U n).map f (FreeAbelianGroup.of σ) =
      FreeAbelianGroup.of (cechIdxMap U (leOfHom f.unop) ∘ σ) :=
  FreeAbelianGroup.map_of_apply σ

lemma cechK_hom_ext {n : ℕ} {V : (Opens X)ᵒᵖ} {A : AddCommGrpCat.{u}}
    {f g : (cechK U n).obj V ⟶ A}
    (h : ∀ σ, f (FreeAbelianGroup.of σ) = g (FreeAbelianGroup.of σ)) : f = g :=
  freeHom_ext h

/-- The differential `cechK U (n + 1) ⟶ cechK U n`. -/
noncomputable def cechKd (n : ℕ) : cechK U (n + 1) ⟶ cechK U n where
  app V := AddCommGrpCat.ofHom (simplexD (cechIdx U V.unop) n)
  naturality _ _ _ := freeHom_ext fun σ => simplexD_map _ n (FreeAbelianGroup.of σ)

lemma cechKd_app_of (n : ℕ) (V : (Opens X)ᵒᵖ) (σ : Fin (n + 2) → cechIdx U V.unop) :
    (cechKd U n).app V (FreeAbelianGroup.of σ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • FreeAbelianGroup.of (σ ∘ i.succAbove) :=
  simplexD_of _ n σ

/-- The short complex `cechK U (n + 2) ⟶ cechK U (n + 1) ⟶ cechK U n`. -/
noncomputable def cechKsc (n : ℕ) : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  ShortComplex.mk (cechKd U (n + 1)) (cechKd U n)
    (NatTrans.ext (funext fun _ => freeHom_ext fun σ =>
      simplexD_comp _ n (FreeAbelianGroup.of σ)))

/-- A short complex of abelian presheaves is exact if it is exact after evaluation at every
object. -/
lemma exact_of_evaluation {C : Type*} [Category C]
    {S : ShortComplex (C ⥤ AddCommGrpCat.{u})}
    (h : ∀ c, (S.map ((evaluation _ _).obj c)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  refine Functor.isZero _ fun c => ?_
  exact ((ShortComplex.exact_iff_isZero_homology _).1 (h c)).of_iso
    (S.mapHomologyIso ((evaluation _ _).obj c)).symm

lemma cechKsc_exact (n : ℕ) : (cechKsc U n).Exact := by
  refine exact_of_evaluation fun V => ?_
  rw [ShortComplex.ab_exact_iff]
  exact fun x hx => simplexD_exact _ n x hx

variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})

lemma le_cechOpen_val {V : Opens X} {n : ℕ} (τ : Fin (n + 1) → cechIdx U V) :
    V ≤ cechOpen U (Subtype.val ∘ τ) :=
  le_iInf fun a => (τ a).2

/-- A Čech cochain as a morphism out of `cechK`. -/
noncomputable def cechKHom {n : ℕ} (c : CechCochain U P n) : cechK U n ⟶ P where
  app V := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun τ =>
    P.map (homOfLE (le_cechOpen_val U τ)).op (c (Subtype.val ∘ τ)))
  naturality V V' f := freeHom_ext fun τ => by
    change FreeAbelianGroup.lift _ ((cechK U n).map f (FreeAbelianGroup.of τ)) =
      P.map f (FreeAbelianGroup.lift _ (FreeAbelianGroup.of τ))
    rw [cechK_map_of, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      ← ConcreteCategory.comp_apply, ← P.map_comp]
    rfl

lemma cechKHom_app_of {n : ℕ} (c : CechCochain U P n) (V : (Opens X)ᵒᵖ)
    (τ : Fin (n + 1) → cechIdx U V.unop) :
    (cechKHom U P c).app V (FreeAbelianGroup.of τ) =
      P.map (homOfLE (le_cechOpen_val U τ)).op (c (Subtype.val ∘ τ)) :=
  FreeAbelianGroup.lift_apply_of _ _

/-- The Čech cochain of a morphism out of `cechK`. -/
noncomputable def cechKCochain {n : ℕ} (φ : cechK U n ⟶ P) : CechCochain U P n :=
  fun σ => φ.app (op (cechOpen U σ)) (FreeAbelianGroup.of fun a => ⟨σ a, iInf_le _ a⟩)

lemma cechKCochain_cechKHom {n : ℕ} (c : CechCochain U P n) :
    cechKCochain U P (cechKHom U P c) = c := by
  funext σ
  rw [cechKCochain, cechKHom_app_of]
  change P.map (𝟙 _) (c σ) = c σ
  rw [P.map_id]
  rfl

lemma cechKHom_cechKCochain {n : ℕ} (φ : cechK U n ⟶ P) :
    cechKHom U P (cechKCochain U P φ) = φ := by
  refine NatTrans.ext (funext fun V => cechK_hom_ext U fun τ => ?_)
  rw [cechKHom_app_of, cechKCochain, ← ConcreteCategory.comp_apply, ← φ.naturality,
    ConcreteCategory.comp_apply, cechK_map_of]
  rfl

lemma cechKHom_cechD {n : ℕ} (c : CechCochain U P n) :
    cechKHom U P (cechD U P n c) = cechKd U n ≫ cechKHom U P c := by
  refine NatTrans.ext (funext fun V => cechK_hom_ext U fun τ => ?_)
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, cechKd_app_of, cechKHom_app_of,
    cechD_apply, map_sum]
  erw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  erw [map_zsmul, map_zsmul, cechKHom_app_of, map_homOfLE_map_homOfLE]
  rfl

lemma cechKHom_zero {n : ℕ} : cechKHom U P (0 : CechCochain U P n) = 0 :=
  NatTrans.ext (funext fun V => cechK_hom_ext U fun τ => by
    rw [cechKHom_app_of]
    exact map_zero _)

/-- The Čech complex of an injective presheaf is exact in positive degrees, for every family
of opens. -/
theorem isCechAcyclic_of_injective [Injective P] : IsCechAcyclic U P := by
  rw [isCechAcyclic_iff]
  intro n c hc
  have h0 : (cechKsc U n).f ≫ cechKHom U P c = 0 := by
    change cechKd U (n + 1) ≫ cechKHom U P c = 0
    rw [← cechKHom_cechD, hc, cechKHom_zero]
  let ψ := (cechKsc_exact U n).descToInjective (cechKHom U P c) h0
  have hψ : cechKd U n ≫ ψ = cechKHom U P c := (cechKsc_exact U n).comp_descToInjective _ h0
  refine ⟨cechKCochain U P ψ, ?_⟩
  rw [← cechKCochain_cechKHom U P (cechD U P n _), cechKHom_cechD, cechKHom_cechKCochain, hψ,
    cechKCochain_cechKHom]

/-- The underlying presheaf of an injective abelian sheaf is injective. -/
instance injective_sheafToPresheaf_obj (I : TopCat.AbSheaf X) [Injective I] :
    Injective ((sheafToPresheaf _ _).obj I) :=
  Injective.injective_of_adjoint
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}) I

/-- **Injective sheaves are Čech acyclic**: the Čech complex of an injective abelian sheaf is
exact in positive degrees, for every family of opens. -/
theorem isCechAcyclic_of_injective_sheaf (I : TopCat.AbSheaf X) [Injective I] :
    IsCechAcyclic U I.obj :=
  isCechAcyclic_of_injective U ((sheafToPresheaf _ _).obj I)

end Resolution

end TopCat.Presheaf

end
