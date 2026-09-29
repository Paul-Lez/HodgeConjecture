/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Topology.Sheaves.Cohomology.Leray
public import Other.Oka.Topology.Sheaves.Cohomology.PullbackZero

/-!
# Čech cohomology in degree one

Let `U : ι → Opens X` be an open cover of `X` and `F` an abelian sheaf. We construct the
comparison map `H¹(U, F) → H¹(X, F)` from Čech to sheaf cohomology and show that it is
always injective, and bijective as soon as `H¹(U i, F|_{U i}) = 0` for all `i` (no condition on
the intersections).

The map is the classical one. Embed `F` into an injective sheaf, `0 → F → I → Q → 0`
(`TopCat.Sheaf.injSES`). A Čech `1`-cocycle `z` of `F` is a coboundary `d t` in `Č•(U, I)` (the
injective sheaf `I` is Čech acyclic), the image of `t` in `Č⁰(U, Q)` is a `0`-cocycle, hence a
global section `s` of `Q`, and `z ↦ δ s`. The value does not depend on the choices, nor on the
short exact sequence: for *every* short exact sequence `0 → F → G → Q → 0` and every such pair
`(t, s)` (`TopCat.Sheaf.IsCechLift`) the image of `z` is `δ s` (`TopCat.Sheaf.cechToH_eq`). This
characterisation gives additivity, naturality in `F`, and compatibility with refinement.

## Main definitions and results

* `TopCat.Presheaf.cechRefine`, `TopCat.Presheaf.cechRefineHom`: the refinement map
  `Č•(U, P) → Č•(V, P)` for a family `V` with `V k ≤ U (τ k)`.
* `TopCat.Sheaf.cechToH hU F z hz : H F 1`: the class of a Čech `1`-cocycle, characterised by
  `TopCat.Sheaf.cechToH_eq`; it vanishes exactly on coboundaries
  (`TopCat.Sheaf.cechToH_eq_zero_iff`), is natural (`TopCat.Sheaf.cechToH_map`), compatible with
  refinement (`TopCat.Sheaf.cechToH_cechRefine`) and surjective if `H¹(U i, F) = 0` for all `i`
  (`TopCat.Sheaf.cechToH_surjective`).
* `TopCat.Sheaf.cechHomologyToH hU F : (cechComplex U F.obj).homology 1 →+ H F 1`, injective
  (`TopCat.Sheaf.cechHomologyToH_injective`), natural in `F`
  (`TopCat.Sheaf.cechHomologyToH_naturality`) and compatible with refinement
  (`TopCat.Sheaf.cechHomologyToH_refine`).
* `TopCat.Sheaf.cechH1Equiv hU hH : (cechComplex U F.obj).homology 1 ≃+ H F 1` if
  `H¹(U i, F|_{U i}) = 0` for all `i`.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

lemma cechCochainMap_comp {P Q R : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q) (ψ : Q ⟶ R)
    (n : ℕ) (c : CechCochain U P n) :
    cechCochainMap U (φ ≫ ψ) n c = cechCochainMap U ψ n (cechCochainMap U φ n c) := rfl

lemma cechCochainMap_id (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (c : CechCochain U P n) :
    cechCochainMap U (𝟙 P) n c = c := rfl

/-- A Čech cocycle of the complex `Č•(U, P)`, read off from an element of its cycles. -/
lemma cechD_iCycles (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (c : (cechComplex U P).cycles 1) :
    cechD U P 1 ((cechComplex U P).iCycles 1 c) = 0 := by
  funext τ
  rw [← cechComplex_d_apply]
  have := ConcreteCategory.congr_hom ((cechComplex U P).iCycles_d 1 2) c
  rw [ConcreteCategory.comp_apply] at this
  exact congrFun this τ

section Refinement

variable {κ : Type u} {V : κ → Opens X} {τ : κ → ι} (hτ : ∀ k, V k ≤ U (τ k))

include hτ in
lemma cechOpen_le_cechOpen_comp {n : ℕ} (σ : Fin (n + 1) → κ) :
    cechOpen V σ ≤ cechOpen U (τ ∘ σ) :=
  le_iInf fun a => (iInf_le _ a).trans (hτ _)

variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})

/-- The refinement map `Čⁿ(U, P) → Čⁿ(V, P)`, `c ↦ (σ ↦ c(τ ∘ σ)|_{V_σ})`, for a family `V` with
`V k ≤ U (τ k)`. -/
def cechRefine (n : ℕ) : CechCochain U P n →+ CechCochain V P n where
  toFun c σ := P.map (homOfLE (cechOpen_le_cechOpen_comp U hτ σ)).op (c (τ ∘ σ))
  map_zero' := by ext; simp
  map_add' c c' := by ext; simp

lemma cechRefine_apply {n : ℕ} (c : CechCochain U P n) (σ : Fin (n + 1) → κ) :
    cechRefine U hτ P n c σ = P.map (homOfLE (cechOpen_le_cechOpen_comp U hτ σ)).op (c (τ ∘ σ)) :=
  rfl

/-- Refinement commutes with the Čech differential. -/
lemma cechD_cechRefine (n : ℕ) (c : CechCochain U P n) :
    cechD V P n (cechRefine U hτ P n c) = cechRefine U hτ P (n + 1) (cechD U P n c) := by
  funext σ
  simp only [cechD_apply, cechRefine_apply, map_sum, map_zsmul, map_homOfLE_map_homOfLE]
  rfl

/-- Refinement commutes with the augmentation. -/
lemma cechRefine_cechAugment {W : Opens X} (hW : ∀ i, U i ≤ W) (hV : ∀ k, V k ≤ W)
    (s : P.obj (op W)) : cechRefine U hτ P 0 (cechAugment U P hW s) = cechAugment V P hV s := by
  funext σ
  simp only [cechRefine_apply, cechAugment_apply, map_homOfLE_map_homOfLE]

/-- Refinement is natural in the presheaf. -/
lemma cechRefine_cechCochainMap {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q) (n : ℕ)
    (c : CechCochain U P n) :
    cechRefine U hτ Q n (cechCochainMap U φ n c) =
      cechCochainMap V φ n (cechRefine U hτ P n c) := by
  funext σ
  simp only [cechRefine_apply, cechCochainMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, φ.naturality]

/-- The refinement map as a morphism of Čech complexes `Č•(U, P) ⟶ Č•(V, P)`. -/
def cechRefineHom : cechComplex U P ⟶ cechComplex V P where
  f n := AddCommGrpCat.ofHom (cechRefine U hτ P n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    ext c : 2
    funext σ
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, cechComplex_d_apply]
    have hd : ((cechComplex U P).d i (i + 1) c : CechCochain U P (i + 1)) = cechD U P i c :=
      funext (cechComplex_d_apply U P i c)
    change _ = cechRefine U hτ P (i + 1) ((cechComplex U P).d i (i + 1) c) σ
    rw [hd, ← cechD_cechRefine]
    rfl

lemma cechRefineHom_f_apply (n : ℕ) (c : (cechComplex U P).X n) :
    ((cechRefineHom U hτ P).f n c : CechCochain V P n) = cechRefine U hτ P n c := rfl

end Refinement

end TopCat.Presheaf

namespace TopCat.Sheaf

open TopCat.Presheaf

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

section Sections

variable {S S' : ShortComplex (AbSheaf X)} (hS : S.ShortExact) (hS' : S'.ShortExact)

/-- The connecting homomorphism `S.X₃(X) = H⁰(X, S.X₃) → H¹(X, S.X₁)` on global sections. -/
noncomputable def H.δSections : S.X₃.obj.obj (op ⊤) →+ H S.X₁ 1 :=
  (H.δ hS 0 1 rfl).comp (H.equiv₀ S.X₃).symm.toAddMonoidHom

lemma H.δSections_apply (s : S.X₃.obj.obj (op ⊤)) :
    H.δSections hS s = H.δ hS 0 1 rfl ((H.equiv₀ S.X₃).symm s) := rfl

/-- Global sections of `S.X₃` coming from `S.X₂` have zero connecting image. -/
lemma H.δSections_g (a : S.X₂.obj.obj (op ⊤)) : H.δSections hS (S.g.hom.app _ a) = 0 := by
  rw [H.δSections_apply, ← H.map_equiv₀_symm, H.δ_map_g]

/-- The connecting image of a global section of `S.X₃` vanishes iff it lifts to `S.X₂`. -/
lemma H.δSections_eq_zero_iff (s : S.X₃.obj.obj (op ⊤)) :
    H.δSections hS s = 0 ↔ ∃ a, S.g.hom.app _ a = s := by
  refine ⟨fun h => ?_, fun ⟨a, ha⟩ => ha ▸ H.δSections_g hS a⟩
  obtain ⟨w, hw⟩ := (H.exact₃ hS 0 1 rfl ((H.equiv₀ _).symm s)).1 h
  refine ⟨H.equiv₀ _ w, ?_⟩
  rw [← H.equiv₀_map, hw, AddEquiv.apply_symm_apply]

/-- The connecting map on global sections is natural in the short exact sequence. -/
lemma H.δSections_naturality (Φ : S ⟶ S') (s : S.X₃.obj.obj (op ⊤)) :
    H.δSections hS' (Φ.τ₃.hom.app _ s) = H.map Φ.τ₁ 1 (H.δSections hS s) := by
  rw [H.δSections_apply, H.δSections_apply, ← H.map_equiv₀_symm, H.δ_naturality hS hS' Φ]

end Sections

section Lift

variable (S : ShortComplex (AbSheaf X))

/-- `(t, s)` lifts the Čech `1`-cochain `z` of `S.X₁` along `0 → S.X₁ → S.X₂ → S.X₃ → 0`:
`d t = f z` in `Č¹(U, S.X₂)` and the image of `t` in `Č⁰(U, S.X₃)` is the restriction of the
global section `s`. -/
def IsCechLift (z : CechCochain U S.X₁.obj 1) (t : CechCochain U S.X₂.obj 0)
    (s : S.X₃.obj.obj (op ⊤)) : Prop :=
  cechD U S.X₂.obj 0 t = cechCochainMap U S.f.hom 1 z ∧
    cechCochainMap U S.g.hom 0 t = cechAugment U S.X₃.obj (fun _ => le_top) s

variable {U S}

lemma cechCochainMap_g_f {n : ℕ} (x : CechCochain U S.X₁.obj n) :
    cechCochainMap U S.g.hom n (cechCochainMap U S.f.hom n x) = 0 := by
  rw [← cechCochainMap_comp]
  have : S.f.hom ≫ S.g.hom = 0 := congrArg (fun φ => φ.hom) S.zero
  rw [this]
  rfl

/-- Morphisms of short complexes transport lifts. -/
lemma IsCechLift.map {S' : ShortComplex (AbSheaf X)} (Φ : S ⟶ S')
    {z : CechCochain U S.X₁.obj 1} {t : CechCochain U S.X₂.obj 0} {s : S.X₃.obj.obj (op ⊤)}
    (h : IsCechLift U S z t s) :
    IsCechLift U S' (cechCochainMap U Φ.τ₁.hom 1 z) (cechCochainMap U Φ.τ₂.hom 0 t)
      (Φ.τ₃.hom.app _ s) := by
  refine ⟨?_, ?_⟩
  · rw [cechD_cechCochainMap, h.1, ← cechCochainMap_comp, ← cechCochainMap_comp]
    exact congrArg (fun φ : S.X₁ ⟶ S'.X₂ => cechCochainMap U φ.hom 1 z) Φ.comm₁₂.symm
  · rw [← cechCochainMap_cechAugment, ← h.2, ← cechCochainMap_comp, ← cechCochainMap_comp]
    exact congrArg (fun φ : S.X₂ ⟶ S'.X₃ => cechCochainMap U φ.hom 0 t) Φ.comm₂₃


/-- Two lifts of the same cochain have the same connecting image. -/
lemma IsCechLift.δSections_eq (hS : S.ShortExact) {z : CechCochain U S.X₁.obj 1}
    {t t' : CechCochain U S.X₂.obj 0}
    {s s' : S.X₃.obj.obj (op ⊤)} (h : IsCechLift U S z t s) (h' : IsCechLift U S z t' s')
    (hU : ⨆ i, U i = ⊤) : H.δSections hS s = H.δSections hS s' := by
  have hd : cechD U S.X₂.obj 0 (t - t') = 0 := by rw [map_sub, h.1, h'.1, sub_self]
  obtain ⟨a, ha⟩ := exists_cechAugment_eq U (fun _ => le_top) S.X₂ hU.ge _ hd
  have hs : S.g.hom.app _ a = s - s' := by
    apply cechAugment_injective U (fun _ => le_top) S.X₃ hU.ge
    rw [← cechCochainMap_cechAugment, ha, map_sub, map_sub, h.2, h'.2]
  rw [← sub_eq_zero, ← map_sub, ← hs, H.δSections_g]

/-- A Čech `1`-cocycle has a lift if the Čech complex of `S.X₂` is exact in degree one. -/
lemma exists_isCechLift (hU : ⨆ i, U i = ⊤) (hC : (cechComplex U S.X₂.obj).ExactAt 1)
    {z : CechCochain U S.X₁.obj 1} (hz : cechD U S.X₁.obj 1 z = 0) :
    ∃ t s, IsCechLift U S z t s := by
  have hfz : cechD U S.X₂.obj 1 (cechCochainMap U S.f.hom 1 z) = 0 := by
    rw [cechD_cechCochainMap, hz, map_zero]
  obtain ⟨t, ht⟩ := (exactAt_cechComplex_succ_iff U S.X₂.obj 0).1 hC _ hfz
  have hgt : cechD U S.X₃.obj 0 (cechCochainMap U S.g.hom 0 t) = 0 := by
    rw [cechD_cechCochainMap, ht, cechCochainMap_g_f]
  obtain ⟨s, hs⟩ := exists_cechAugment_eq U (fun _ => le_top) S.X₃ hU.ge _ hgt
  exact ⟨t, s, ht, hs.symm⟩

/-- The morphism from a short exact sequence `S` to `0 → G → I(G) → I(G)/G → 0` extending a
morphism `S.X₁ ⟶ G`. -/
noncomputable def homToInjSES (hS : S.ShortExact) {G : AbSheaf X} (φ : S.X₁ ⟶ G) :
    S ⟶ injSES G :=
  have := hS.mono_f
  let τ₂ : S.X₂ ⟶ (injSES G).X₂ := Injective.factorThru (φ ≫ Injective.ι G) S.f
  have hτ₂ : S.f ≫ τ₂ = φ ≫ (injSES G).f := Injective.comp_factorThru _ _
  let d := CokernelCofork.IsColimit.desc' hS.gIsCokernel (τ₂ ≫ (injSES G).g) (by
    rw [← Category.assoc, hτ₂, Category.assoc]
    change φ ≫ Injective.ι G ≫ cokernel.π (Injective.ι G) = 0
    rw [cokernel.condition, comp_zero])
  { τ₁ := φ
    τ₂ := τ₂
    τ₃ := d.1
    comm₁₂ := hτ₂.symm
    comm₂₃ := d.2.symm }

@[simp]
lemma homToInjSES_τ₁ (hS : S.ShortExact) {G : AbSheaf X} (φ : S.X₁ ⟶ G) :
    (homToInjSES hS φ).τ₁ = φ := rfl

end Lift

section Comparison

variable {U} (hU : ⨆ i, U i = ⊤)
include hU

lemma exists_isCechLift_injSES (F : AbSheaf X) {z : CechCochain U F.obj 1}
    (hz : cechD U F.obj 1 z = 0) : ∃ t s, IsCechLift U (injSES F) z t s :=
  exists_isCechLift hU (isCechAcyclic_of_injective_sheaf U _ 0) hz

/-- **The class of a Čech `1`-cocycle** of an abelian sheaf `F` for an open cover `U` of `X`, in
`H¹(X, F)`: lift `z = d t` to the injective sheaf `I(F)`, glue the image of `t` in `I(F)/F` to a
global section `s` and take its connecting image `δ s`. See `TopCat.Sheaf.cechToH_eq` for the
characterisation by any short exact sequence. -/
noncomputable def cechToH (F : AbSheaf X) (z : CechCochain U F.obj 1)
    (hz : cechD U F.obj 1 z = 0) : H F 1 :=
  H.δSections (injSES_shortExact F) (exists_isCechLift_injSES hU F hz).choose_spec.choose

/-- **Characterisation of the class of a Čech cocycle**: for every short exact sequence
`0 → F → G → Q → 0` and every lift `(t, s)` of `z` along it, the class of `z` is `δ s`. -/
theorem cechToH_eq {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    {z : CechCochain U S.X₁.obj 1} (hz : cechD U S.X₁.obj 1 z = 0)
    {t : CechCochain U S.X₂.obj 0} {s : S.X₃.obj.obj (op ⊤)} (h : IsCechLift U S z t s) :
    cechToH hU S.X₁ z hz = H.δSections hS s := by
  have h₀ := (exists_isCechLift_injSES hU S.X₁ hz).choose_spec.choose_spec
  have h₁ : IsCechLift U (injSES S.X₁) z _ _ := h.map (homToInjSES hS (𝟙 S.X₁))
  rw [cechToH, IsCechLift.δSections_eq (injSES_shortExact S.X₁) h₀ h₁ hU,
    H.δSections_naturality hS (injSES_shortExact S.X₁)]
  exact H.map_id_apply _

/-- `TopCat.Sheaf.cechToH_eq` for the chosen sequence `0 → F → I(F) → I(F)/F → 0`. -/
theorem cechToH_eq_of_injSES (F : AbSheaf X) {z : CechCochain U F.obj 1}
    (hz : cechD U F.obj 1 z = 0) {t : CechCochain U (injSES F).X₂.obj 0}
    {s : (injSES F).X₃.obj.obj (op ⊤)} (h : IsCechLift U (injSES F) z t s) :
    cechToH hU F z hz = H.δSections (injSES_shortExact F) s :=
  cechToH_eq hU (injSES_shortExact F) hz h

/-- The class of a Čech cocycle is natural in the sheaf. -/
theorem cechToH_map {F G : AbSheaf X} (φ : F ⟶ G) {z : CechCochain U F.obj 1}
    (hz : cechD U F.obj 1 z = 0) :
    cechToH hU G (cechCochainMap U φ.hom 1 z)
        (by rw [cechD_cechCochainMap, hz, map_zero]) =
      H.map φ 1 (cechToH hU F z hz) := by
  obtain ⟨t, s, h⟩ := exists_isCechLift_injSES hU F hz
  have hF := injSES_shortExact F
  have h₂ := cechToH_eq_of_injSES hU G (z := cechCochainMap U φ.hom 1 z)
    (by rw [cechD_cechCochainMap, hz, map_zero]) (h.map (homToInjSES hF φ))
  rw [cechToH_eq_of_injSES hU F hz h, h₂, H.δSections_naturality hF (injSES_shortExact G)]
  rfl

lemma cechToH_congr (F : AbSheaf X) {z z' : CechCochain U F.obj 1} (h : z = z')
    (hz : cechD U F.obj 1 z = 0) (hz' : cechD U F.obj 1 z' = 0) :
    cechToH hU F z hz = cechToH hU F z' hz' := by
  subst h
  rfl

/-- The class of a Čech cocycle is additive. -/
theorem cechToH_add (F : AbSheaf X) {z z' : CechCochain U F.obj 1}
    (hz : cechD U F.obj 1 z = 0) (hz' : cechD U F.obj 1 z' = 0) :
    cechToH hU F (z + z') (by rw [map_add, hz, hz', add_zero]) =
      cechToH hU F z hz + cechToH hU F z' hz' := by
  obtain ⟨t, s, h⟩ := exists_isCechLift_injSES hU F hz
  obtain ⟨t', s', h'⟩ := exists_isCechLift_injSES hU F hz'
  have hF := injSES_shortExact F
  have h'' : IsCechLift U (injSES F) (z + z') (t + t') (s + s') :=
    ⟨by rw [map_add, h.1, h'.1]; exact (map_add _ _ _).symm,
      by rw [map_add, h.2, h'.2]; exact (map_add _ _ _).symm⟩
  rw [cechToH_eq_of_injSES hU F _ h'', cechToH_eq_of_injSES hU F hz h,
    cechToH_eq_of_injSES hU F hz' h', map_add]
  rfl

/-- **The class of a Čech cocycle vanishes exactly on coboundaries.** -/
theorem cechToH_eq_zero_iff (F : AbSheaf X) {z : CechCochain U F.obj 1}
    (hz : cechD U F.obj 1 z = 0) :
    cechToH hU F z hz = 0 ↔ ∃ b : CechCochain U F.obj 0, cechD U F.obj 0 b = z := by
  let S := injSES F
  have hS : S.ShortExact := injSES_shortExact F
  obtain ⟨t, s, h⟩ := exists_isCechLift_injSES hU F hz
  have hex := fun V => sections_exact hS V
  rw [cechToH_eq_of_injSES hU F hz h]
  constructor
  · intro h0
    obtain ⟨a, ha⟩ := (H.δSections_eq_zero_iff hS s).1 h0
    have hg : cechCochainMap U S.g.hom 0 (t - cechAugment U S.X₂.obj (fun _ => le_top) a) = 0 := by
      rw [map_sub, h.2, cechCochainMap_cechAugment, ha, sub_self]
    choose b hb using fun σ : Fin 1 → ι => (hex (cechOpen U σ)).2 _ (congrFun hg σ)
    have hb' : cechCochainMap U S.f.hom 0 b = t - cechAugment U S.X₂.obj (fun _ => le_top) a :=
      funext hb
    refine ⟨b, funext fun τ => (hex (cechOpen U τ)).1 ?_⟩
    have := congrFun (cechD_cechCochainMap S.f.hom 0 b) τ
    rw [hb', map_sub, cechD_cechAugment, sub_zero, h.1] at this
    simp only [cechCochainMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    exact this.symm
  · rintro ⟨b, rfl⟩
    have h' : IsCechLift U S (cechD U F.obj 0 b) (cechCochainMap U S.f.hom 0 b) 0 :=
      ⟨cechD_cechCochainMap S.f.hom 0 b, (cechCochainMap_g_f (S := S) b).trans (map_zero _).symm⟩
    exact (IsCechLift.δSections_eq hS h h' hU).trans (map_zero _)

/-- The class of a coboundary vanishes. -/
lemma cechToH_cechD (F : AbSheaf X) (b : CechCochain U F.obj 0) :
    cechToH hU F (cechD U F.obj 0 b) (cechD_cechD U F.obj 0 b) = 0 :=
  (cechToH_eq_zero_iff hU F _).2 ⟨b, rfl⟩

/-- **Every class in `H¹(X, F)` comes from a Čech cocycle** if `H¹(U i, F|_{U i}) = 0` for all
`i`. -/
theorem cechToH_surjective (F : AbSheaf X)
    (hH : ∀ i, ∀ x : H ((restrictOpen (U i)).obj F) 1, x = 0) (x : H F 1) :
    ∃ (z : CechCochain U F.obj 1) (hz : cechD U F.obj 1 z = 0), cechToH hU F z hz = x := by
  let S := injSES F
  have hS : S.ShortExact := injSES_shortExact F
  have hex := fun V => sections_exact hS V
  obtain ⟨w, hw⟩ := (H.exact₁ hS 0 1 rfl x).1 (H.eq_zero_of_injective S.X₂ (n := 0) _)
  let s : S.X₃.obj.obj (op ⊤) := H.equiv₀ _ w
  have hH' : ∀ σ : Fin 1 → ι, ∀ x : H ((restrictOpen (cechOpen U σ)).obj F) 1, x = 0 := by
    intro σ
    rw [fin_one_eq_const σ, cechOpen_const]
    exact hH _
  choose t ht using fun σ : Fin 1 → ι =>
    surjective_of_H_one_restrictOpen (cechOpen U σ) hS (hH' σ)
      (cechAugment U S.X₃.obj (fun _ => le_top) s σ)
  have ht' : cechCochainMap U S.g.hom 0 t = cechAugment U S.X₃.obj (fun _ => le_top) s :=
    funext ht
  have hg : cechCochainMap U S.g.hom 1 (cechD U S.X₂.obj 0 t) = 0 := by
    rw [← cechD_cechCochainMap, ht', cechD_cechAugment]
  choose z hz using fun τ : Fin 2 → ι => (hex (cechOpen U τ)).2 _ (congrFun hg τ)
  have hz' : cechCochainMap U S.f.hom 1 z = cechD U S.X₂.obj 0 t := funext hz
  have hdz : cechD U F.obj 1 z = 0 := by
    funext τ
    apply (hex (cechOpen U τ)).1
    have := congrFun (cechD_cechCochainMap S.f.hom 1 z) τ
    rw [hz', cechD_cechD] at this
    exact this.symm.trans (map_zero _).symm
  refine ⟨z, hdz, ?_⟩
  rw [cechToH_eq_of_injSES hU F hdz ⟨hz'.symm, ht'⟩, ← hw, H.δSections_apply]
  exact congrArg (H.δ hS 0 1 rfl) ((H.equiv₀ S.X₃).symm_apply_apply w)

/-- **The class of a Čech cocycle is compatible with refinement**: for a cover `V` with
`V k ≤ U (τ k)`, a cocycle for `U` and its refinement for `V` have the same class. -/
theorem cechToH_cechRefine {κ : Type u} {V : κ → Opens X} (hV : ⨆ k, V k = ⊤) {τ : κ → ι}
    (hτ : ∀ k, V k ≤ U (τ k)) (F : AbSheaf X) {z : CechCochain U F.obj 1}
    (hz : cechD U F.obj 1 z = 0) :
    cechToH hV F (cechRefine U hτ F.obj 1 z) (by rw [cechD_cechRefine, hz, map_zero]) =
      cechToH hU F z hz := by
  obtain ⟨t, s, h⟩ := exists_isCechLift_injSES hU F hz
  have hF := injSES_shortExact F
  have h' : IsCechLift V (injSES F) (cechRefine U hτ F.obj 1 z)
      (cechRefine U hτ (injSES F).X₂.obj 0 t) s :=
    ⟨by rw [cechD_cechRefine, h.1, cechRefine_cechCochainMap]; rfl,
      by rw [← cechRefine_cechCochainMap, h.2, cechRefine_cechAugment]⟩
  rw [cechToH_eq_of_injSES hU F hz h, cechToH_eq_of_injSES hV F _ h']

end Comparison

section Homology

variable {U} (hU : ⨆ i, U i = ⊤)
include hU

/-- The comparison map on cycles `Z¹(U, F) → H¹(X, F)`. -/
noncomputable def cechCyclesToH (F : AbSheaf X) :
    (cechComplex U F.obj).cycles 1 ⟶ AddCommGrpCat.of (H F 1) :=
  AddCommGrpCat.ofHom
    { toFun c := cechToH hU F ((cechComplex U F.obj).iCycles 1 c) (cechD_iCycles U F.obj c)
      map_zero' := (cechToH_eq_zero_iff hU F _).2 ⟨0, (map_zero _).trans (map_zero _).symm⟩
      map_add' c c' :=
        (cechToH_congr hU F (map_add _ c c') _ _).trans (cechToH_add hU F _ _) }

lemma cechCyclesToH_apply (F : AbSheaf X) (c : (cechComplex U F.obj).cycles 1) :
    cechCyclesToH hU F c =
      cechToH hU F ((cechComplex U F.obj).iCycles 1 c) (cechD_iCycles U F.obj c) := rfl

/-- `d b ∈ Z¹` maps to zero. -/
lemma toCycles_comp_cechCyclesToH (F : AbSheaf X) :
    (cechComplex U F.obj).toCycles 0 1 ≫ cechCyclesToH hU F = 0 := by
  ext b
  rw [ConcreteCategory.comp_apply, cechCyclesToH_apply]
  have hb : ((cechComplex U F.obj).iCycles 1 ((cechComplex U F.obj).toCycles 0 1 b) :
      CechCochain U F.obj 1) = cechD U F.obj 0 b := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i]
    exact funext (cechComplex_d_apply U F.obj 0 b)
  simp only [hb, cechToH_cechD]
  rfl

/-- **The comparison map `H¹(U, F) → H¹(X, F)`** for an open cover `U` of `X`. -/
noncomputable def cechHomologyToH (F : AbSheaf X) :
    (cechComplex U F.obj).homology 1 →+ H F 1 :=
  (((cechComplex U F.obj).homologyIsCokernel 0 1 (by simp)).desc
    (CokernelCofork.ofπ _ (toCycles_comp_cechCyclesToH hU F))).hom

lemma cechHomologyToH_homologyπ (F : AbSheaf X) (c : (cechComplex U F.obj).cycles 1) :
    cechHomologyToH hU F ((cechComplex U F.obj).homologyπ 1 c) =
      cechToH hU F ((cechComplex U F.obj).iCycles 1 c) (cechD_iCycles U F.obj c) := by
  rw [← cechCyclesToH_apply]
  exact ConcreteCategory.congr_hom
    (Cofork.IsColimit.π_desc ((cechComplex U F.obj).homologyIsCokernel 0 1 (by simp))) c

omit hU in
lemma exists_homologyπ_eq {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (x : (cechComplex U P).homology 1) : ∃ c, (cechComplex U P).homologyπ 1 c = x :=
  (AddCommGrpCat.epi_iff_surjective _).1 inferInstance x

omit hU in
lemma exists_iCycles_eq {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {z : CechCochain U P 1}
    (hz : cechD U P 1 z = 0) : ∃ c, ((cechComplex U P).iCycles 1 c : CechCochain U P 1) = z := by
  let K := cechComplex U P
  have hex := ShortComplex.exact_of_f_is_kernel
    (ShortComplex.mk (K.iCycles 1) (K.d 1 2) (K.iCycles_d 1 2)) (K.cyclesIsKernel 1 2 (by simp))
  refine (ShortComplex.ab_exact_iff _).1 hex z ?_
  funext τ
  exact (cechComplex_d_apply U P 1 z τ).trans (congrFun hz τ)

/-- The comparison map `H¹(U, F) → H¹(X, F)` is injective. -/
theorem cechHomologyToH_injective (F : AbSheaf X) : Function.Injective (cechHomologyToH hU F) := by
  let K := cechComplex U F.obj
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, rfl⟩ := exists_homologyπ_eq x
  rw [cechHomologyToH_homologyπ, cechToH_eq_zero_iff] at hx
  obtain ⟨b, hb⟩ := hx
  have hc : K.toCycles 0 1 b = c := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles 1)).1 inferInstance
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i]
    exact (funext (cechComplex_d_apply U F.obj 0 b)).trans hb
  rw [← hc, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
  rfl

/-- The comparison map `H¹(U, F) → H¹(X, F)` is surjective if `H¹(U i, F|_{U i}) = 0` for all
`i`. -/
theorem cechHomologyToH_surjective (F : AbSheaf X)
    (hH : ∀ i, ∀ x : H ((restrictOpen (U i)).obj F) 1, x = 0) :
    Function.Surjective (cechHomologyToH hU F) := by
  intro x
  obtain ⟨z, hz, rfl⟩ := cechToH_surjective hU F hH x
  obtain ⟨c, hc⟩ := exists_iCycles_eq hz
  refine ⟨(cechComplex U F.obj).homologyπ 1 c, ?_⟩
  rw [cechHomologyToH_homologyπ]
  congr 1

/-- **Čech `H¹` computes sheaf `H¹`**: for an open cover `U` of `X` with
`H¹(U i, F|_{U i}) = 0` for all `i`, the comparison map `H¹(U, F) → H¹(X, F)` is an
isomorphism. -/
noncomputable def cechH1Equiv (F : AbSheaf X)
    (hH : ∀ i, ∀ x : H ((restrictOpen (U i)).obj F) 1, x = 0) :
    (cechComplex U F.obj).homology 1 ≃+ H F 1 :=
  AddEquiv.ofBijective (cechHomologyToH hU F)
    ⟨cechHomologyToH_injective hU F, cechHomologyToH_surjective hU F hH⟩

@[simp]
lemma cechH1Equiv_apply (F : AbSheaf X) (hH : ∀ i, ∀ x : H ((restrictOpen (U i)).obj F) 1, x = 0)
    (x : (cechComplex U F.obj).homology 1) : cechH1Equiv hU F hH x = cechHomologyToH hU F x :=
  rfl

/-- The comparison map `H¹(U, F) → H¹(X, F)` is natural in `F`. -/
theorem cechHomologyToH_naturality {F G : AbSheaf X} (φ : F ⟶ G)
    (x : (cechComplex U F.obj).homology 1) :
    cechHomologyToH hU G (HomologicalComplex.homologyMap ((cechComplexFunctor U).map φ.hom) 1 x) =
      H.map φ 1 (cechHomologyToH hU F x) := by
  obtain ⟨c, rfl⟩ := exists_homologyπ_eq x
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply, cechHomologyToH_homologyπ, cechHomologyToH_homologyπ,
    ← cechToH_map]
  congr 1
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
  rfl

/-- The comparison map `H¹(U, F) → H¹(X, F)` is compatible with refinement: for a cover `V`
with `V k ≤ U (τ k)`, the refinement map `H¹(U, F) → H¹(V, F)` commutes with the comparison
maps. -/
theorem cechHomologyToH_refine {κ : Type u} {V : κ → Opens X} (hV : ⨆ k, V k = ⊤) {τ : κ → ι}
    (hτ : ∀ k, V k ≤ U (τ k)) (F : AbSheaf X) (x : (cechComplex U F.obj).homology 1) :
    cechHomologyToH hV F (HomologicalComplex.homologyMap (cechRefineHom U hτ F.obj) 1 x) =
      cechHomologyToH hU F x := by
  obtain ⟨c, rfl⟩ := exists_homologyπ_eq x
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply, cechHomologyToH_homologyπ, cechHomologyToH_homologyπ,
    ← cechToH_cechRefine hU hV hτ]
  congr 1
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
  rfl

end Homology

end TopCat.Sheaf

end
