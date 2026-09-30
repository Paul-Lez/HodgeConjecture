/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Other.Oka.Topology.Sheaves.Cohomology.CechInjective
public import Other.Oka.Topology.Sheaves.Cohomology.Restrict

/-!
# Leray's theorem and Cartan's criterion

We compare sheaf cohomology with Čech cohomology by dimension shifting along
`0 → F → I(F) → I(F)/F → 0` (`TopCat.Sheaf.injSES`), using that injective sheaves are Čech acyclic
(`TopCat.Presheaf.isCechAcyclic_of_injective_sheaf`) and restrict to injective sheaves on opens.

## Main results

* `TopCat.Presheaf.exists_lift_of_cech`: for `0 → F → G → Q → 0` exact and a cover `U` of `W`
  with Čech `H¹(U, F) = 0`, a section of `Q` over `W` which lifts to `G` on every `U i` lifts
  over `W`.
* `TopCat.Sheaf.isCechAcyclic_X₃`: Čech acyclicity passes to quotients `G/F` if the sequence is
  surjective on all finite intersections.
* `TopCat.Sheaf.H_eq_zero_of_isCechAcyclic` (**Leray**, vanishing form): if `U` covers `X`,
  `Hⁿ(U_σ, F) = 0` for `n ≥ 1` on all finite intersections `U_σ`, and `Č•(U, F)` is exact in
  positive degrees, then `Hⁿ(X, F) = 0` for `n ≥ 1`.
* `TopCat.Sheaf.cartan` (**Cartan's criterion**): for a family `ℬ` of opens closed under
  intersections and a class of admissible covers which is cofinal among covers of members of `ℬ`,
  Čech acyclicity of `F` on admissible `ℬ`-covers of members of `ℬ` implies `Hⁿ(B, F|_B) = 0`
  for all `B ∈ ℬ` and `n ≥ 1`. `TopCat.Sheaf.cartan_of_isCompact` is the version for a basis of
  compact opens and finite covers.

Along the way: `TopCat.Sheaf.surjective_of_H_one`, `TopCat.Sheaf.H_one_eq_zero_of_surjective`,
`TopCat.Sheaf.H_succ_succ_eq_zero`, `TopCat.Sheaf.H_succ_eq_zero_of_H_succ_succ` and their
`restrictOpen` versions relate sections and cohomology in a short exact sequence whose middle
term is injective.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace TopCat.Presheaf

section Cochains

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

lemma cechD_cechD (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (c : CechCochain U P n) :
    cechD U P (n + 1) (cechD U P n c) = 0 := by
  have h := ConcreteCategory.congr_hom ((cechComplex U P).d_comp_d n (n + 1) (n + 2)) c
  funext τ
  have h' := congrFun h τ
  rw [ConcreteCategory.comp_apply, cechComplex_d_apply] at h'
  have hin : ((cechComplex U P).d n (n + 1) c : CechCochain U P (n + 1)) = cechD U P n c :=
    funext (cechComplex_d_apply U P n c)
  rw [hin] at h'
  exact h'

variable {U} in
lemma cechD_cechCochainMap {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q) (n : ℕ)
    (c : CechCochain U P n) :
    cechD U Q n (cechCochainMap U φ n c) = cechCochainMap U φ (n + 1) (cechD U P n c) := by
  funext τ
  simp only [cechD_apply, cechCochainMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum,
    map_zsmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, φ.naturality]

lemma cechCochainMap_cechAugment {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q)
    {W : Opens X} (hW : ∀ i, U i ≤ W) (s : P.obj (op W)) :
    cechCochainMap U φ 0 (cechAugment U P hW s) = cechAugment U Q hW (φ.app _ s) := by
  funext σ
  simp only [cechCochainMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, cechAugment_apply]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, φ.naturality]

end Cochains

section Lift

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- **Lifting along a Čech-acyclic kernel.** Let `0 → F → G → Q → 0` be a short exact sequence of
sheaves and `U` a family of opens covering `W` with Čech `H¹(U, F) = 0`. A section `s` of `Q` over
`W` which lifts to `G` on every `U i` lifts to `G` over `W`. -/
theorem exists_lift_of_cech {S : ShortComplex (TopCat.AbSheaf X)} (hS : S.ShortExact)
    {W : Opens X} (hW : ∀ i, U i ≤ W) (hcov : W ≤ ⨆ i, U i)
    (h₁ : (cechComplex U S.X₁.obj).ExactAt 1) (s : S.X₃.obj.obj (op W))
    (t : CechCochain U S.X₂.obj 0)
    (ht : cechCochainMap U S.g.hom 0 t = cechAugment U S.X₃.obj hW s) :
    ∃ x : S.X₂.obj.obj (op W), S.g.hom.app _ x = s := by
  have hex := fun V => sections_exact hS V
  -- `d t` maps to zero in `Č¹(Q)`, hence comes from `Č¹(F)`.
  have hdt : cechCochainMap U S.g.hom 1 (cechD U S.X₂.obj 0 t) = 0 := by
    rw [← cechD_cechCochainMap, ht, cechD_cechAugment]
  choose y hy using fun τ : Fin 2 → ι => (hex (cechOpen U τ)).2 _ (congrFun hdt τ)
  have hy' : cechCochainMap U S.f.hom 1 y = cechD U S.X₂.obj 0 t := funext hy
  -- `y` is a cocycle, hence a coboundary.
  have hdy : cechD U S.X₁.obj 1 y = 0 := by
    funext τ
    apply (hex (cechOpen U τ)).1
    have := congrFun (cechD_cechCochainMap S.f.hom 1 y) τ
    rw [hy', cechD_cechD] at this
    exact this.symm.trans (map_zero _).symm
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_succ_iff U S.X₁.obj 0).1 h₁ y hdy
  -- `t - f b` is a cocycle of `G`, hence glues.
  have hcoc : cechD U S.X₂.obj 0 (t - cechCochainMap U S.f.hom 0 b) = 0 := by
    rw [map_sub, cechD_cechCochainMap, hb, hy', sub_self]
  obtain ⟨x, hx⟩ := exists_cechAugment_eq U hW S.X₂ hcov _ hcoc
  refine ⟨x, cechAugment_injective U hW S.X₃ hcov ?_⟩
  rw [← cechCochainMap_cechAugment, hx, map_sub, ht, sub_eq_self]
  funext σ
  simp only [cechCochainMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply]
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
    S.zero]
  rfl

end Lift

end TopCat.Presheaf

namespace TopCat.Sheaf

open TopCat.Presheaf

variable {X : TopCat.{u}}

section DimensionShifting

variable {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
include hS

/-- If `H¹(X, S.X₁) = 0` then `S.X₂(X) → S.X₃(X)` is surjective. -/
lemma surjective_of_H_one (h : ∀ x : H S.X₁ 1, x = 0) :
    Function.Surjective (S.g.hom.app (op ⊤)) := by
  intro y
  obtain ⟨w, hw⟩ := (H.exact₃ hS 0 1 rfl ((H.equiv₀ _).symm y)).1 (h _)
  refine ⟨H.equiv₀ _ w, ?_⟩
  rw [← H.equiv₀_map, hw, AddEquiv.apply_symm_apply]

/-- If S.X₂ is injective and `S.X₂(X) → S.X₃(X)` is surjective then `H¹(X, S.X₁) = 0`. -/
lemma H_one_eq_zero_of_surjective [Injective S.X₂]
    (hsurj : Function.Surjective (S.g.hom.app (op ⊤))) (x : H S.X₁ 1) : x = 0 := by
  obtain ⟨z, rfl⟩ := (H.exact₁ hS 0 1 rfl x).1 (H.eq_zero_of_injective S.X₂ (n := 0) _)
  obtain ⟨t, ht⟩ := hsurj (H.equiv₀ _ z)
  have : z = H.map S.g 0 ((H.equiv₀ S.X₂).symm t) := by
    rw [H.map_equiv₀_symm, ht, AddEquiv.symm_apply_apply]
  rw [this, H.δ_map_g]

/-- Dimension shifting: if S.X₂ is injective, `Hⁿ⁺¹(S.X₃) = 0` implies `Hⁿ⁺²(S.X₁) = 0`. -/
lemma H_succ_succ_eq_zero [Injective S.X₂] {q : ℕ} (h : ∀ z : H S.X₃ (q + 1), z = 0)
    (x : H S.X₁ (q + 2)) : x = 0 := by
  obtain ⟨z, rfl⟩ := (H.exact₁ hS (q + 1) (q + 2) rfl x).1 (H.eq_zero_of_injective S.X₂ _)
  rw [h z, map_zero]

/-- Dimension shifting: if S.X₂ is injective, `Hⁿ⁺²(S.X₁) = 0` implies `Hⁿ⁺¹(S.X₃) = 0`. -/
lemma H_succ_eq_zero_of_H_succ_succ [Injective S.X₂] {q : ℕ} (h : ∀ x : H S.X₁ (q + 2), x = 0)
    (z : H S.X₃ (q + 1)) : z = 0 := by
  obtain ⟨w, rfl⟩ := (H.exact₃ hS (q + 1) (q + 2) rfl z).1 (h _)
  rw [H.eq_zero_of_injective S.X₂ w, map_zero]

end DimensionShifting

section Open

variable (V : Opens X)

lemma surjective_restrictOpen_map_app_top_iff {F G : AbSheaf X} (φ : F ⟶ G) :
    Function.Surjective (((restrictOpen V).map φ).hom.app (op ⊤)) ↔
      Function.Surjective (φ.hom.app (op V)) := by
  change Function.Surjective (φ.hom.app (op (V.isOpenEmbedding.isOpenMap.functor.obj ⊤))) ↔ _
  rw [functor_obj_top]

variable {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
include hS

lemma shortExact_restrictOpen : (S.map (restrictOpen V)).ShortExact :=
  hS.map_of_exact (restrictOpen V)

/-- If `H¹(V, S.X₁|_V) = 0` then `S.X₂(V) → S.X₃(V)` is surjective. -/
lemma surjective_of_H_one_restrictOpen (h : ∀ x : H ((restrictOpen V).obj S.X₁) 1, x = 0) :
    Function.Surjective (S.g.hom.app (op V)) :=
  (surjective_restrictOpen_map_app_top_iff V S.g).1
    (surjective_of_H_one (shortExact_restrictOpen V hS) h)

/-- If S.X₂ is injective and `S.X₂(V) → S.X₃(V)` is surjective then `H¹(V, S.X₁|_V) = 0`. -/
lemma H_one_restrictOpen_eq_zero_of_surjective [Injective S.X₂]
    (hsurj : Function.Surjective (S.g.hom.app (op V)))
    (x : H ((restrictOpen V).obj S.X₁) 1) : x = 0 :=
  have : Injective (S.map (restrictOpen V)).X₂ := injective_restrictAb _ S.X₂
  H_one_eq_zero_of_surjective (shortExact_restrictOpen V hS)
    ((surjective_restrictOpen_map_app_top_iff V S.g).2 hsurj) x

lemma H_succ_succ_restrictOpen_eq_zero [Injective S.X₂] {q : ℕ}
    (h : ∀ z : H ((restrictOpen V).obj S.X₃) (q + 1), z = 0)
    (x : H ((restrictOpen V).obj S.X₁) (q + 2)) : x = 0 :=
  have : Injective (S.map (restrictOpen V)).X₂ := injective_restrictAb _ S.X₂
  H_succ_succ_eq_zero (shortExact_restrictOpen V hS) h x

lemma H_succ_restrictOpen_eq_zero_of_H_succ_succ [Injective S.X₂] {q : ℕ}
    (h : ∀ x : H ((restrictOpen V).obj S.X₁) (q + 2), x = 0)
    (z : H ((restrictOpen V).obj S.X₃) (q + 1)) : z = 0 :=
  have : Injective (S.map (restrictOpen V)).X₂ := injective_restrictAb _ S.X₂
  H_succ_eq_zero_of_H_succ_succ (shortExact_restrictOpen V hS) h z

end Open

section InjectiveSES

variable (F : AbSheaf X)

/-- The short exact sequence `0 → F → I(F) → I(F)/F → 0` with `I(F)` injective. -/
noncomputable def injSES : ShortComplex (AbSheaf X) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)

lemma injSES_shortExact : (injSES F).ShortExact :=
  have : Mono (injSES F).f := inferInstanceAs (Mono (Injective.ι F))
  have : Epi (injSES F).g := inferInstanceAs (Epi (cokernel.π (Injective.ι F)))
  { exact := ShortComplex.exact_cokernel _ }

instance : Injective (injSES F).X₂ := inferInstanceAs (Injective (Injective.under F))

end InjectiveSES

/-- In a short exact sequence of sheaves which is surjective on all finite intersections `U_σ`,
if the first two terms are Čech acyclic then so is the third. -/
lemma isCechAcyclic_X₃ {ι : Type u} {U : ι → Opens X} {S : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (h₁ : IsCechAcyclic U S.X₁.obj) (h₂ : IsCechAcyclic U S.X₂.obj)
    (hsurj : ∀ (n : ℕ) (σ : Fin (n + 1) → ι),
      Function.Surjective (S.g.hom.app (op (cechOpen U σ)))) :
    IsCechAcyclic U S.X₃.obj := by
  have hT := cechComplex_shortExact_of_sheaf hS hsurj
  intro n
  have e := hT.homology_exact₃ (n + 1) (n + 2) (by simp)
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine e.isZero_X₂ ?_ ?_
  · exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₂ n)).eq_of_src _ _
  · exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₁ (n + 1))).eq_of_tgt _ _

section Leray

variable {ι : Type u} (U : ι → Opens X)

/-- If `F` has vanishing `H¹` on the finite intersections `U_σ` and Čech
`H¹(U, F) = 0`, and `U` covers `W`, then `F → I(F)/F` is surjective on sections over `W`, for any
injective resolution step. -/
lemma surjective_of_cech {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    {W : Opens X} (hW : ∀ i, U i ≤ W) (hcov : W ≤ ⨆ i, U i)
    (hH : ∀ σ : Fin 1 → ι, ∀ x : H ((restrictOpen (cechOpen U σ)).obj S.X₁) 1, x = 0)
    (hC : (cechComplex U S.X₁.obj).ExactAt 1) :
    Function.Surjective (S.g.hom.app (op W)) := by
  intro s
  choose t ht using fun σ : Fin 1 → ι =>
    surjective_of_H_one_restrictOpen (cechOpen U σ) hS (hH σ) (cechAugment U S.X₃.obj hW s σ)
  exact exists_lift_of_cech U hS hW hcov hC s t (funext ht)

/-- **Leray's theorem** (vanishing form). Let `U` be an open cover of `X` such that `F` has no
higher cohomology on any finite intersection `U_σ`, and such that the Čech complex `Č•(U, F)` is
exact in positive degrees. Then `Hⁿ(X, F) = 0` for all `n ≥ 1`. -/
theorem H_eq_zero_of_isCechAcyclic (hU : ⨆ i, U i = ⊤) (F : AbSheaf X)
    (hF : ∀ (n : ℕ) (σ : Fin (n + 1) → ι) (q : ℕ)
      (x : H ((restrictOpen (cechOpen U σ)).obj F) (q + 1)), x = 0)
    (hC : IsCechAcyclic U F.obj) (q : ℕ) (x : H F (q + 1)) : x = 0 := by
  induction q generalizing F with
  | zero =>
    exact H_one_eq_zero_of_surjective (injSES_shortExact F)
      (surjective_of_cech U (injSES_shortExact F) (fun _ => le_top) hU.ge
        (fun σ => hF 0 σ 0) (hC 0)) x
  | succ q ih =>
    let S := injSES F
    have hS : S.ShortExact := injSES_shortExact F
    have hsurj : ∀ (n : ℕ) (σ : Fin (n + 1) → ι),
        Function.Surjective (S.g.hom.app (op (cechOpen U σ))) :=
      fun n σ => surjective_of_H_one_restrictOpen _ hS (hF n σ 0)
    refine H_succ_succ_eq_zero hS (fun z => ih S.X₃ (fun n σ q' z' => ?_) ?_ z) x
    · exact H_succ_restrictOpen_eq_zero_of_H_succ_succ _ hS (hF n σ (q' + 1)) z'
    · exact isCechAcyclic_X₃ hS hC (isCechAcyclic_of_injective_sheaf U S.X₂) hsurj

end Leray

section Cartan

lemma iInf_fin_succ {α : Type*} [CompleteLattice α] {n : ℕ} (f : Fin (n + 2) → α) :
    ⨅ a, f a = f 0 ⊓ ⨅ a : Fin (n + 1), f a.succ :=
  le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun a => iInf_le _ a.succ))
    (le_iInf fun a => Fin.cases inf_le_left (fun a => inf_le_right.trans (iInf_le _ a)) a)

/-- A family of opens closed under binary intersections contains all finite intersections
`U_σ` of its members. -/
lemma cechOpen_mem {ℬ : Set (Opens X)} (hℬ : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, B ⊓ B' ∈ ℬ) {ι : Type u}
    {U : ι → Opens X} (hU : ∀ i, U i ∈ ℬ) {n : ℕ} (σ : Fin (n + 1) → ι) :
    cechOpen U σ ∈ ℬ := by
  induction n with
  | zero =>
    have : cechOpen U σ = U (σ 0) := le_antisymm (iInf_le _ 0)
      (le_iInf fun a => by rw [Subsingleton.elim (α := Fin 1) a 0])
    rw [this]
    exact hU _
  | succ n ih =>
    rw [cechOpen, iInf_fin_succ]
    exact hℬ _ (hU _) _ (ih (σ ∘ Fin.succ))

variable (ℬ : Set (Opens X)) (hℬ : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, B ⊓ B' ∈ ℬ)
  (Adm : ∀ ι : Type u, (ι → Opens X) → Prop)
  (hcof : ∀ B ∈ ℬ, ∀ 𝒱 : Set (Opens X), (∀ x ∈ B, ∃ V ∈ 𝒱, x ∈ V) →
    ∃ (ι : Type u) (U : ι → Opens X), Adm ι U ∧ (∀ i, U i ∈ ℬ) ∧ (∀ i, ∃ V ∈ 𝒱, U i ≤ V) ∧
      ⨆ i, U i = B)

include hcof in
/-- The degree one case of Cartan's criterion. -/
lemma cartan_H_one (F : AbSheaf X)
    (hF : ∀ (ι : Type u) (U : ι → Opens X), Adm ι U → (∀ i, U i ∈ ℬ) → ⨆ i, U i ∈ ℬ →
      IsCechAcyclic U F.obj)
    (B : Opens X) (hB : B ∈ ℬ) (x : H ((restrictOpen B).obj F) 1) : x = 0 := by
  let S := injSES F
  have hS : S.ShortExact := injSES_shortExact F
  refine H_one_restrictOpen_eq_zero_of_surjective B hS (fun s => ?_) x
  have hloc := (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).1
    ((TopCat.Sheaf.isLocallySurjective_iff_epi (F := (S.X₂ : X.Sheaf AddCommGrpCat.{u}))
      (G := (S.X₃ : X.Sheaf AddCommGrpCat.{u})) S.g).2 hS.epi_g) B s
  let 𝒱 : Set (Opens X) := {V | ∃ h : V ≤ B, ∃ t : S.X₂.obj.obj (op V),
    S.g.hom.app _ t = S.X₃.obj.map (homOfLE h).op s}
  obtain ⟨ι, U, hAdm, hUℬ, hsub, hsup⟩ := hcof B hB 𝒱 fun x hx => by
    obtain ⟨V, hVB, ⟨t, ht⟩, hxV⟩ := hloc x hx
    exact ⟨V, ⟨hVB, t, ht⟩, hxV⟩
  have hW : ∀ i, U i ≤ B := fun i => hsup ▸ le_iSup U i
  have hlift : ∀ σ : Fin 1 → ι, ∃ t : S.X₂.obj.obj (op (cechOpen U σ)),
      S.g.hom.app _ t = cechAugment U S.X₃.obj hW s σ := by
    intro σ
    obtain ⟨V, ⟨hVB, t, ht⟩, hUV⟩ := hsub (σ 0)
    have hσV : cechOpen U σ ≤ V := (iInf_le _ 0).trans hUV
    refine ⟨S.X₂.obj.map (homOfLE hσV).op t, ?_⟩
    rw [← ConcreteCategory.comp_apply]
    erw [S.g.hom.naturality]
    rw [ConcreteCategory.comp_apply, ht, cechAugment_apply, map_homOfLE_map_homOfLE]
  choose t ht using hlift
  exact exists_lift_of_cech U hS hW hsup.ge (hF ι U hAdm hUℬ (hsup ▸ hB) 0) s t (funext ht)

include hℬ hcof in
/-- **Cartan's criterion.** Let `ℬ` be a family of opens closed under binary intersections and
let `Adm` be a class of families of opens ("admissible covers") such that every open cover of a
member `B ∈ ℬ` is refined by an admissible cover of `B` by members of `ℬ`. If the Čech complex of
`F` is exact in positive degrees for every admissible cover by members of `ℬ` of a member of
`ℬ`, then `Hⁿ(B, F|_B) = 0` for all `B ∈ ℬ` and `n ≥ 1`. -/
theorem cartan (F : AbSheaf X)
    (hF : ∀ (ι : Type u) (U : ι → Opens X), Adm ι U → (∀ i, U i ∈ ℬ) → ⨆ i, U i ∈ ℬ →
      IsCechAcyclic U F.obj)
    (B : Opens X) (hB : B ∈ ℬ) (q : ℕ) (x : H ((restrictOpen B).obj F) (q + 1)) : x = 0 := by
  induction q generalizing F with
  | zero => exact cartan_H_one ℬ Adm hcof F hF B hB x
  | succ q ih =>
    let S := injSES F
    have hS : S.ShortExact := injSES_shortExact F
    refine H_succ_succ_restrictOpen_eq_zero B hS (fun z => ih S.X₃ ?_ z) x
    intro ι U hAdm hUℬ hsup
    refine isCechAcyclic_X₃ hS (hF ι U hAdm hUℬ hsup) (isCechAcyclic_of_injective_sheaf U S.X₂)
      fun n σ => surjective_of_H_one_restrictOpen _ hS fun y => ?_
    exact cartan_H_one ℬ Adm hcof F hF _ (cechOpen_mem hℬ hUℬ σ) y

omit hcof in
include hℬ in
/-- **Cartan's criterion** for a basis of quasi-compact opens. Let `ℬ` be a basis of the topology
closed under binary intersections whose members are compact. If the Čech complex of `F` is exact
in positive degrees for every finite cover by members of `ℬ` of a member of `ℬ`, then
`Hⁿ(B, F|_B) = 0` for all `B ∈ ℬ` and `n ≥ 1`. -/
theorem cartan_of_isCompact (hbasis : Opens.IsBasis ℬ) (hcpt : ∀ B ∈ ℬ, IsCompact (B : Set X))
    (F : AbSheaf X)
    (hF : ∀ (ι : Type u) (U : ι → Opens X), Finite ι → (∀ i, U i ∈ ℬ) → ⨆ i, U i ∈ ℬ →
      IsCechAcyclic U F.obj)
    (B : Opens X) (hB : B ∈ ℬ) (q : ℕ) (x : H ((restrictOpen B).obj F) (q + 1)) : x = 0 := by
  refine cartan ℬ hℬ (fun ι _ => Finite ι) ?_ F hF B hB q x
  intro B hB 𝒱 hcov
  have : ∀ x : B, ∃ W ∈ ℬ, (x : X) ∈ W ∧ W ≤ B ∧ ∃ V ∈ 𝒱, W ≤ V := by
    intro x
    obtain ⟨V, hV, hxV⟩ := hcov x x.2
    obtain ⟨W, hW, hxW, hWle⟩ :=
      (Opens.isBasis_iff_nbhd.1 hbasis) (show (x : X) ∈ V ⊓ B from ⟨hxV, x.2⟩)
    exact ⟨W, hW, hxW, hWle.trans inf_le_right, V, hV, hWle.trans inf_le_left⟩
  choose W hWℬ hxW hWB hWV using this
  obtain ⟨t, ht⟩ := (hcpt B hB).elim_finite_subcover (fun x : B => (W x : Set X))
    (fun x => (W x).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxW _⟩)
  refine ⟨t, fun x => W x.1, Finite.of_fintype _, fun x => hWℬ _, fun x => hWV x.1,
    le_antisymm (iSup_le fun x => hWB _) fun y hy => ?_⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, hyx⟩

end Cartan

end TopCat.Sheaf

end
