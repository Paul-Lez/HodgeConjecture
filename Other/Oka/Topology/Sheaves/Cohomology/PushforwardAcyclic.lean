/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Topology.Sheaves.Cohomology.BaseChange
public import Other.Oka.Topology.Sheaves.Cohomology.LocalVanishing
public import Other.Oka.Topology.Sheaves.Cohomology.PullbackZero

/-!
# Cohomology of pushforwards of acyclic sheaves

Let `f : Y ⟶ X` be a continuous map and `G` an abelian sheaf on `Y`. We call `G` *`f`-acyclic*
(`TopCat.Sheaf.IsPushforwardAcyclic f G`) if for every `q ≥ 1`, every open `V ⊆ X` and every
class `c ∈ Hᵠ(f⁻¹ V, G)`, each point of `V` has an open neighbourhood `V' ⊆ V` with
`c|_{f⁻¹ V'} = 0`; that is, the higher direct images `Rᵠ f_* G` vanish.

The *edge map* `TopCat.Sheaf.H.pushforwardEdge f G n : Hⁿ(X, f_* G) →+ Hⁿ(Y, G)` is the pullback
map `Hⁿ(X, f_* G) → Hⁿ(Y, f⁻¹ f_* G)` followed by the counit `f⁻¹ f_* G ⟶ G`. It is natural in
`G`, compatible with connecting homomorphisms, and in degree zero it is the identity of
`Γ(X, f_* G) = Γ(Y, G)` (`TopCat.Sheaf.H.equiv₀_pushforwardEdge`).

## Main results

* `TopCat.Sheaf.shortExact_map_pushforwardAb`: `f_*` preserves short exact sequences whose first
  term is `f`-acyclic.
* `TopCat.Sheaf.IsPushforwardAcyclic.X₃`: in `0 → G → I → Q → 0` with `I` injective and `G`
  `f`-acyclic, `Q` is `f`-acyclic.
* `TopCat.Sheaf.H.bijective_pushforwardEdge`: for `G` `f`-acyclic the edge map is bijective in
  all degrees, and `TopCat.Sheaf.H.pushforwardAcyclicAddEquiv : Hⁿ(Y, G) ≃+ Hⁿ(X, f_* G)`.
* `TopCat.Sheaf.H.pushforwardEdge_pullback`, `TopCat.Sheaf.H.pushforwardAcyclicAddEquiv_pullback`:
  for a commutative square `f' ≫ g = g' ≫ f` of continuous maps, the edge maps intertwine the
  pullback maps along `g` and `g'` up to the base change morphism `g⁻¹ f_* G ⟶ f'_* g'⁻¹ G`
  (`TopCat.Sheaf.pullbackPushforwardBaseChangeApp`). The two composite pullbacks are compared by
  `TopCat.Sheaf.pullbackAbCommSq : g⁻¹ ⋙ f'⁻¹ ⟶ f⁻¹ ⋙ g'⁻¹`, the conjugate of `f_* g'_* ≅ g_* f'_*`
  (`TopCat.Sheaf.H.map_pullbackAbCommSqApp_pullback_pullback`).
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}} (f : Y ⟶ X)

section Acyclic

/-- An abelian sheaf `G` on `Y` is *`f`-acyclic* if every class of positive degree in
`Hᵠ(f⁻¹ V, G)` (Mathlib's `CategoryTheory.Sheaf.H'`) vanishes, locally on `V`, after restriction
to `f⁻¹ V'`; i.e. the higher direct images `Rᵠ f_* G` vanish. -/
def IsPushforwardAcyclic (G : AbSheaf Y) : Prop :=
  ∀ (q : ℕ) (V : Opens X) (c : CategoryTheory.Sheaf.H'.{u} G (q + 1) ((Opens.map f).obj V))
    (x : X), x ∈ V → ∃ (V' : Opens X) (h : V' ≤ V), x ∈ V' ∧
      H'res G (q + 1) ((Opens.map f).monotone h) c = 0

variable {f}

/-- `f`-acyclicity in terms of the cohomology `Hᵠ(f⁻¹ V, G|_{f⁻¹ V})` of restrictions. -/
lemma isPushforwardAcyclic_iff (G : AbSheaf Y) :
    IsPushforwardAcyclic f G ↔ ∀ (q : ℕ) (V : Opens X)
      (c : H ((restrictOpen ((Opens.map f).obj V)).obj G) (q + 1)) (x : X), x ∈ V →
        ∃ (V' : Opens X) (h : V' ≤ V), x ∈ V' ∧
          restrictOpenRes G (q + 1) ((Opens.map f).monotone h) c = 0 := by
  constructor
  · intro hG q V c x hx
    obtain ⟨V', h, hx', hc⟩ := hG q V ((H'AddEquiv _ G (q + 1)).symm c) x hx
    exact ⟨V', h, hx', by rw [restrictOpenRes_apply, hc, map_zero]⟩
  · intro hG q V c x hx
    obtain ⟨V', h, hx', hc⟩ := hG q V (H'AddEquiv _ G (q + 1) c) x hx
    refine ⟨V', h, hx', (H'AddEquiv _ G (q + 1)).injective ?_⟩
    rw [← restrictOpenRes_H'AddEquiv, hc, map_zero]

variable (f) in
/-- Injective sheaves are `f`-acyclic. -/
lemma isPushforwardAcyclic_of_injective (I : AbSheaf Y) [Injective I] :
    IsPushforwardAcyclic f I := by
  intro q V c x hx
  refine ⟨V, le_rfl, hx, ?_⟩
  rw [show c = 0 from Ext.eq_zero_of_injective _, map_zero]

variable {S : ShortComplex (AbSheaf Y)} (hS : S.ShortExact)

include hS in
/-- **Pushforward of a short exact sequence with `f`-acyclic kernel is short exact**: sections of
`S.X₃` over `f⁻¹ V` lift to `S.X₂` locally on `V`, since the obstruction in `H¹(f⁻¹ V, S.X₁)`
vanishes locally. -/
lemma shortExact_map_pushforwardAb (h₁ : IsPushforwardAcyclic f S.X₁) :
    (S.map (pushforwardAb f)).ShortExact := by
  have := hS.mono_f
  have hmono : Mono (S.map (pushforwardAb f)).f :=
    inferInstanceAs (Mono ((pushforwardAb f).map S.f))
  have hex : (S.map (pushforwardAb f)).Exact :=
    hS.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance
  refine { exact := hex, mono_f := hmono, epi_g := ?_ }
  change Epi ((pushforwardAb f).map S.g)
  refine (TopCat.Sheaf.isLocallySurjective_iff_epi
    (F := (((pushforwardAb f).obj S.X₂ : AbSheaf X) : X.Sheaf AddCommGrpCat.{u}))
    (G := (((pushforwardAb f).obj S.X₃ : AbSheaf X) : X.Sheaf AddCommGrpCat.{u})) _).1 ?_
  refine (TopCat.Presheaf.isLocallySurjective_iff _).2 fun V t x hx ↦ ?_
  let W := (Opens.map f).obj V
  let z : freeYoneda W ⟶ S.X₃ := (freeYonedaHomEquiv W S.X₃).symm t
  obtain ⟨V', hV, hxV', hc⟩ := h₁ 0 V ((Ext.mk₀ z).comp hS.extClass (zero_add 1)) x hx
  have hW : (Opens.map f).obj V' ≤ W := (Opens.map f).monotone hV
  rw [H'res_apply] at hc
  change ((Ext.mk₀ (freeYonedaMap hW)).comp ((Ext.mk₀ z).comp hS.extClass (zero_add 1))
    (zero_add 1) : Ext (freeYoneda ((Opens.map f).obj V')) S.X₁ 1) = 0 at hc
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀] at hc
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ _ hS _ (zero_add 1) hc
  obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
  rw [Ext.mk₀_comp_mk₀] at hy
  have hy' := congrArg (freeYonedaHomEquiv _ S.X₃) ((Ext.mk₀_bijective _ _).1 hy)
  rw [freeYonedaHomEquiv_comp, freeYonedaHomEquiv_freeYonedaMap_comp, Equiv.apply_symm_apply]
    at hy'
  exact ⟨V', hV, ⟨freeYonedaHomEquiv _ S.X₂ s, hy'⟩, hxV'⟩

include hS in
/-- In a short exact sequence `0 → G → I → Q → 0` with `I` injective, if `G` is `f`-acyclic then
so is `Q`: `Hᵠ(f⁻¹ V, Q) ≅ Hᵠ⁺¹(f⁻¹ V, G)` for `q ≥ 1`, compatibly with restriction. -/
lemma IsPushforwardAcyclic.X₃ [Injective S.X₂] (h₁ : IsPushforwardAcyclic f S.X₁) :
    IsPushforwardAcyclic f S.X₃ := by
  intro q V c x hx
  obtain ⟨V', hV, hxV', hc⟩ := h₁ (q + 1) V (c.comp hS.extClass rfl) x hx
  refine ⟨V', hV, hxV', ?_⟩
  rw [H'res_apply] at hc ⊢
  change ((Ext.mk₀ _).comp (c.comp hS.extClass rfl) (zero_add _) :
    Ext (freeYoneda ((Opens.map f).obj V')) S.X₁ (q + 2)) = 0 at hc
  rw [← Ext.comp_assoc _ _ _ (zero_add _) rfl (by omega)] at hc
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ _ hS _ rfl hc
  change ((Ext.mk₀ _).comp (c : Ext (freeYoneda ((Opens.map f).obj V)) S.X₃ (q + 1))
    (zero_add _) : Ext (freeYoneda ((Opens.map f).obj V')) S.X₃ (q + 1)) = 0
  rw [← hy, Ext.eq_zero_of_injective y, Ext.zero_comp]

end Acyclic

section Edge

/-- The counit `f⁻¹ f_* G ⟶ G` of the adjunction `f⁻¹ ⊣ f_*`. -/
noncomputable def pushforwardCounit (G : AbSheaf Y) :
    (pullbackAb f).obj ((pushforwardAb f).obj G) ⟶ G :=
  (pullbackPushforwardAbAdj f).counit.app G

@[reassoc]
lemma pushforwardCounit_naturality {G G' : AbSheaf Y} (φ : G ⟶ G') :
    (pullbackAb f).map ((pushforwardAb f).map φ) ≫ pushforwardCounit f G' =
      pushforwardCounit f G ≫ φ :=
  (pullbackPushforwardAbAdj f).counit.naturality φ

/-- **The edge map** `Hⁿ(X, f_* G) → Hⁿ(Y, G)`: the pullback map to `Hⁿ(Y, f⁻¹ f_* G)` followed
by the counit `f⁻¹ f_* G ⟶ G`. -/
noncomputable def H.pushforwardEdge (G : AbSheaf Y) (n : ℕ) :
    H ((pushforwardAb f).obj G) n →+ H G n :=
  (H.map (pushforwardCounit f G) n).comp (H.pullback f)

lemma H.pushforwardEdge_apply (G : AbSheaf Y) {n : ℕ} (x : H ((pushforwardAb f).obj G) n) :
    H.pushforwardEdge f G n x = H.map (pushforwardCounit f G) n (H.pullback f x) :=
  rfl

/-- The edge map is natural in the sheaf. -/
lemma H.pushforwardEdge_map {G G' : AbSheaf Y} (φ : G ⟶ G') {n : ℕ}
    (x : H ((pushforwardAb f).obj G) n) :
    H.pushforwardEdge f G' n (H.map ((pushforwardAb f).map φ) n x) =
      H.map φ n (H.pushforwardEdge f G n x) := by
  rw [H.pushforwardEdge_apply, H.pushforwardEdge_apply, H.pullback_map,
    ← H.map_comp_apply, ← H.map_comp_apply, pushforwardCounit_naturality]

/-- The edge map commutes with the connecting homomorphisms of a short exact sequence whose
pushforward is short exact. -/
lemma H.pushforwardEdge_δ {S : ShortComplex (AbSheaf Y)} (hS : S.ShortExact)
    (hS' : (S.map (pushforwardAb f)).ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    (x : H ((pushforwardAb f).obj S.X₃) n₀) :
    H.pushforwardEdge f S.X₁ n₁ (H.δ hS' n₀ n₁ h x) =
      H.δ hS n₀ n₁ h (H.pushforwardEdge f S.X₃ n₀ x) := by
  let φ : (S.map (pushforwardAb f)).map (pullbackAb f) ⟶ S :=
    { τ₁ := pushforwardCounit f S.X₁
      τ₂ := pushforwardCounit f S.X₂
      τ₃ := pushforwardCounit f S.X₃
      comm₁₂ := (pushforwardCounit_naturality f S.f).symm
      comm₂₃ := (pushforwardCounit_naturality f S.g).symm }
  exact (congrArg (H.map (pushforwardCounit f S.X₁) n₁) (H.pullback_δ f hS' h x)).trans
    (H.δ_naturality (hS'.map_of_exact (pullbackAb f)) hS φ h _).symm

/-- In degree zero the edge map sends `x : ℤ_X ⟶ f_* G` to its adjoint `ℤ_Y ≅ f⁻¹ ℤ_X ⟶ G`. -/
lemma H.pushforwardEdge_mk₀ (G : AbSheaf Y) (x : constZ X ⟶ (pushforwardAb f).obj G) :
    H.pushforwardEdge f G 0 (Ext.mk₀ x) =
      Ext.mk₀ ((pullbackConstZIso f).inv ≫ ((pullbackPushforwardAbAdj f).homEquiv _ _).symm x) := by
  rw [H.pushforwardEdge_apply, H.pullback, H.mapOfExact_apply, H.map_apply,
    Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, Adjunction.homEquiv_counit,
    Category.assoc]
  rfl

/-- The edge map is bijective in degree zero. -/
lemma H.bijective_pushforwardEdge_zero (G : AbSheaf Y) :
    Function.Bijective (H.pushforwardEdge f G 0) := by
  rw [← Function.Bijective.of_comp_iff _ (Ext.mk₀_bijective (constZ X) _)]
  have : H.pushforwardEdge f G 0 ∘ Ext.mk₀ = Ext.mk₀ ∘
      (Iso.homCongr (pullbackConstZIso f) (Iso.refl G)) ∘
        ((pullbackPushforwardAbAdj f).homEquiv _ _).symm := by
    funext x
    simp [H.pushforwardEdge_mk₀]
  rw [this]
  exact (Ext.mk₀_bijective _ _).comp ((Equiv.bijective _).comp (Equiv.bijective _))

/-- In degree zero the edge map is the identity of `Γ(X, f_* G) = Γ(Y, G)`. -/
lemma H.equiv₀_pushforwardEdge (G : AbSheaf Y) (x : H ((pushforwardAb f).obj G) 0) :
    H.equiv₀ G (H.pushforwardEdge f G 0 x) = H.equiv₀ _ x := by
  rw [H.pushforwardEdge_apply, H.equiv₀_map, H.equiv₀_pullback]
  exact congrArg (fun φ ↦ φ.hom.app (op ⊤) (H.equiv₀ _ x))
    ((pullbackPushforwardAbAdj f).right_triangle_components G)

/-- **Cohomology of the pushforward of an `f`-acyclic sheaf**: the edge map
`Hⁿ(X, f_* G) → Hⁿ(Y, G)` is bijective in all degrees. -/
theorem H.bijective_pushforwardEdge {G : AbSheaf Y} (hG : IsPushforwardAcyclic f G) (n : ℕ) :
    Function.Bijective (H.pushforwardEdge f G n) := by
  induction n generalizing G with
  | zero => exact H.bijective_pushforwardEdge_zero f G
  | succ n ih =>
    let S := injSES G
    have hS : S.ShortExact := injSES_shortExact G
    have hS' := shortExact_map_pushforwardAb hS hG
    have : Injective (S.map (pushforwardAb f)).X₂ := (pushforwardAb f).injective_obj S.X₂
    have hsurj : ∀ {A B : Type u} [AddCommGroup A] [AddCommGroup B] [Subsingleton B]
        (δ : A →+ H S.X₁ (n + 1)) (φ : H S.X₁ (n + 1) →+ B),
        Function.Exact δ φ → Function.Surjective δ := fun δ φ hex y ↦
      (hex y).1 (Subsingleton.elim _ _)
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      (H.map (S.map (pushforwardAb f)).g n) (H.δ hS' n (n + 1) rfl)
      (H.map S.g n) (H.δ hS n (n + 1) rfl)
      (H.pushforwardEdge f S.X₂ n) (H.pushforwardEdge f S.X₃ n) (H.pushforwardEdge f G (n + 1))
      ?_ ?_ (H.exact₃ hS' n (n + 1) rfl) (H.exact₃ hS n (n + 1) rfl) ?_
      (ih (hG.X₃ hS)) ?_ ?_
    · ext x
      exact (H.pushforwardEdge_map f S.g x).symm
    · ext x
      exact (H.pushforwardEdge_δ f hS hS' rfl x).symm
    · cases n with
      | zero => exact (H.bijective_pushforwardEdge_zero f S.X₂).2
      | succ m => exact fun y ↦ ⟨0, Subsingleton.elim _ _⟩
    · exact fun y ↦ (H.exact₁ hS' n (n + 1) rfl y).1 (Subsingleton.elim _ _)
    · exact fun y ↦ (H.exact₁ hS n (n + 1) rfl y).1 (Subsingleton.elim _ _)

/-- **Cohomology of the pushforward of an `f`-acyclic sheaf**: `Hⁿ(Y, G) ≃+ Hⁿ(X, f_* G)`, the
inverse of the edge map `TopCat.Sheaf.H.pushforwardEdge`. -/
noncomputable def H.pushforwardAcyclicAddEquiv {G : AbSheaf Y} (hG : IsPushforwardAcyclic f G)
    (n : ℕ) : H G n ≃+ H ((pushforwardAb f).obj G) n :=
  (AddEquiv.ofBijective (H.pushforwardEdge f G n) (H.bijective_pushforwardEdge f hG n)).symm

@[simp]
lemma H.pushforwardEdge_pushforwardAcyclicAddEquiv {G : AbSheaf Y}
    (hG : IsPushforwardAcyclic f G) {n : ℕ} (x : H G n) :
    H.pushforwardEdge f G n (H.pushforwardAcyclicAddEquiv f hG n x) = x :=
  (AddEquiv.ofBijective _ (H.bijective_pushforwardEdge f hG n)).apply_symm_apply x

@[simp]
lemma H.pushforwardAcyclicAddEquiv_pushforwardEdge {G : AbSheaf Y}
    (hG : IsPushforwardAcyclic f G) {n : ℕ} (x : H ((pushforwardAb f).obj G) n) :
    H.pushforwardAcyclicAddEquiv f hG n (H.pushforwardEdge f G n x) = x :=
  (AddEquiv.ofBijective _ (H.bijective_pushforwardEdge f hG n)).symm_apply_apply x

/-- `Hⁿ(Y, G) ≃+ Hⁿ(X, f_* G)` is natural in the `f`-acyclic sheaf `G`. -/
lemma H.pushforwardAcyclicAddEquiv_map {G G' : AbSheaf Y} (hG : IsPushforwardAcyclic f G)
    (hG' : IsPushforwardAcyclic f G') (φ : G ⟶ G') {n : ℕ} (x : H G n) :
    H.pushforwardAcyclicAddEquiv f hG' n (H.map φ n x) =
      H.map ((pushforwardAb f).map φ) n (H.pushforwardAcyclicAddEquiv f hG n x) := by
  apply (H.bijective_pushforwardEdge f hG' n).1
  rw [H.pushforwardEdge_pushforwardAcyclicAddEquiv, H.pushforwardEdge_map,
    H.pushforwardEdge_pushforwardAcyclicAddEquiv]

/-- In degree zero `H⁰(Y, G) ≃+ H⁰(X, f_* G)` is the identity of `Γ(Y, G) = Γ(X, f_* G)`. -/
lemma H.equiv₀_pushforwardAcyclicAddEquiv {G : AbSheaf Y} (hG : IsPushforwardAcyclic f G)
    (x : H G 0) : H.equiv₀ _ (H.pushforwardAcyclicAddEquiv f hG 0 x) = H.equiv₀ G x := by
  rw [← H.equiv₀_pushforwardEdge, H.pushforwardEdge_pushforwardAcyclicAddEquiv]

end Edge
section BaseChange

variable {X' Y' : TopCat.{u}} {f' : Y' ⟶ X'} {g : X' ⟶ X} {g' : Y' ⟶ Y}
  (h : f' ≫ g = g' ≫ f)

/-- The morphism `f'⁻¹ g⁻¹ ⟶ g'⁻¹ f⁻¹` of inverse images of a commutative square
`f' ≫ g = g' ≫ f`, conjugate to `f_* g'_* ≅ g_* f'_*`. -/
noncomputable def pullbackAbCommSq : pullbackAb g ⋙ pullbackAb f' ⟶ pullbackAb f ⋙ pullbackAb g' :=
  (conjugateEquiv ((pullbackPushforwardAbAdj f).comp (pullbackPushforwardAbAdj g'))
    ((pullbackPushforwardAbAdj g).comp (pullbackPushforwardAbAdj f'))).symm
    (pushforwardAbCommSqIso h).hom

/-- The component `f'⁻¹ g⁻¹ F ⟶ g'⁻¹ f⁻¹ F` of `TopCat.Sheaf.pullbackAbCommSq`. -/
noncomputable def pullbackAbCommSqApp (F : AbSheaf X) :
    (pullbackAb f').obj ((pullbackAb g).obj F) ⟶ (pullbackAb g').obj ((pullbackAb f).obj F) :=
  (pullbackAbCommSq f h).app F

@[reassoc]
lemma pullbackAbCommSqApp_naturality {F F' : AbSheaf X} (φ : F ⟶ F') :
    (pullbackAb f').map ((pullbackAb g).map φ) ≫ pullbackAbCommSqApp f h F' =
      pullbackAbCommSqApp f h F ≫ (pullbackAb g').map ((pullbackAb f).map φ) :=
  (pullbackAbCommSq f h).naturality φ

/-- The adjoint of `f'⁻¹ g⁻¹ F ⟶ g'⁻¹ f⁻¹ F` under `g⁻¹ ⊣ g_*` and `f'⁻¹ ⊣ f'_*` is the unit
`F ⟶ f_* g'_* g'⁻¹ f⁻¹ F` followed by `f_* g'_* ≅ g_* f'_*`. -/
lemma homEquiv_homEquiv_pullbackAbCommSqApp (F : AbSheaf X) :
    (pullbackPushforwardAbAdj g).homEquiv _ _ ((pullbackPushforwardAbAdj f').homEquiv _ _
      (pullbackAbCommSqApp f h F)) =
      (pullbackPushforwardAbAdj f).unit.app F ≫ (pushforwardAb f).map
        ((pullbackPushforwardAbAdj g').unit.app _) ≫ (pushforwardAbCommSqIso h).hom.app _ := by
  have := unit_conjugateEquiv_symm
    ((pullbackPushforwardAbAdj f).comp (pullbackPushforwardAbAdj g'))
    ((pullbackPushforwardAbAdj g).comp (pullbackPushforwardAbAdj f'))
    (pushforwardAbCommSqIso h).hom F
  simp only [Adjunction.comp_unit_app, Functor.comp_map] at this
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
  exact ((Category.assoc _ _ _).symm.trans this.symm).trans (Category.assoc _ _ _)

/-- `f'⁻¹ g⁻¹ ℤ_X ⟶ g'⁻¹ f⁻¹ ℤ_X` is compatible with the identifications of both sides with
`ℤ_{Y'}`. -/
lemma pullbackAbCommSqApp_constZ :
    (pullbackConstZIso f').inv ≫ (pullbackAb f').map (pullbackConstZIso g).inv ≫
        pullbackAbCommSqApp f h (constZ X) =
      (pullbackConstZIso g').inv ≫ (pullbackAb g').map (pullbackConstZIso f).inv := by
  let A := fun (S : TopCat.{u}) ↦
    constantSheafAdj (Opens.grothendieckTopology S) AddCommGrpCat.{u} isTerminalTop
  apply ((A Y').homEquiv _ _).injective
  rw [constantSheafAdj_homEquiv_pullbackConstZIso_inv_comp,
    constantSheafAdj_homEquiv_pullbackConstZIso_inv_comp, Adjunction.homEquiv_naturality_left,
    ← Category.comp_id ((pullbackAb g').map (pullbackConstZIso f).inv),
    Adjunction.homEquiv_naturality_left, constantSheafAdj_homEquiv_pullbackConstZIso_inv_comp,
    constantSheafAdj_homEquiv_pullbackConstZIso_inv_comp, homEquiv_homEquiv_pullbackAbCommSqApp,
    Adjunction.homEquiv_id]
  have key : ∀ (M : AbSheaf Y')
      (φ : constZ X ⟶ (pushforwardAb f).obj ((pushforwardAb g').obj M)),
      (A X).homEquiv _ _ (φ ≫ (pushforwardAbCommSqIso h).hom.app M) = (A X).homEquiv _ _ φ := by
    intro M φ
    rw [Adjunction.homEquiv_naturality_right]
    refine (congrArg _ ?_).trans (Category.comp_id _)
    exact pushforwardAbCommSqIso_hom_app_hom_app_top h M
  refine Eq.trans ?_ (key _ _)
  congr 1

/-- The base change morphism `g⁻¹ f_* G ⟶ f'_* g'⁻¹ G` is compatible with the counits of
`f⁻¹ ⊣ f_*` and `f'⁻¹ ⊣ f'_*`. -/
lemma pullbackAb_map_pullbackPushforwardBaseChangeApp_comp_pushforwardCounit (G : AbSheaf Y) :
    (pullbackAb f').map (pullbackPushforwardBaseChangeApp h G) ≫
        pushforwardCounit f' ((pullbackAb g').obj G) =
      pullbackAbCommSqApp f h ((pushforwardAb f).obj G) ≫
        (pullbackAb g').map (pushforwardCounit f G) := by
  apply ((pullbackPushforwardAbAdj f').homEquiv _ _).injective
  apply ((pullbackPushforwardAbAdj g).homEquiv _ _).injective
  have e₁ : (pullbackAb f').map (pullbackPushforwardBaseChangeApp h G) ≫
      pushforwardCounit f' ((pullbackAb g').obj G) =
        ((pullbackPushforwardAbAdj f').homEquiv _ _).symm
          (pullbackPushforwardBaseChangeApp h G) :=
    (Adjunction.homEquiv_counit _ _ _ _).symm
  rw [e₁, Equiv.apply_symm_apply, homEquiv_pullbackPushforwardBaseChangeApp,
    Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    homEquiv_homEquiv_pullbackAbCommSqApp]
  have n₁ := (pushforwardAbCommSqIso h).hom.naturality ((pullbackAb g').map (pushforwardCounit f G))
  have n₂ := (pullbackPushforwardAbAdj g').unit.naturality (pushforwardCounit f G)
  have t : (pullbackPushforwardAbAdj f).unit.app ((pushforwardAb f).obj G) ≫
      (pushforwardAb f).map ((𝟭 (AbSheaf Y)).map (pushforwardCounit f G)) = 𝟙 _ :=
    (pullbackPushforwardAbAdj f).right_triangle_components G
  symm
  erw [Category.assoc, Category.assoc, ← n₁, ← Functor.map_comp_assoc, ← n₂, Functor.map_comp,
    ← Category.assoc, ← Category.assoc, t, Category.id_comp]

/-- The pullback maps along the two composites of a commutative square `f' ≫ g = g' ≫ f` agree
up to `f'⁻¹ g⁻¹ F ⟶ g'⁻¹ f⁻¹ F`. -/
lemma H.map_pullbackAbCommSqApp_pullback_pullback (F : AbSheaf X) {n : ℕ} (x : H F n) :
    H.map (pullbackAbCommSqApp f h F) n (H.pullback f' (H.pullback g x)) =
      H.pullback g' (H.pullback f x) := by
  have nat := Ext.mapExactFunctor_mapExactFunctor_comp_mk₀ (Φ₁ := pullbackAb g)
    (Φ₂ := pullbackAb f') (Ψ₁ := pullbackAb f) (Ψ₂ := pullbackAb g') (pullbackAbCommSqApp f h)
    (pullbackAbCommSqApp_naturality f h) x
  rw [H.pullback, H.pullback, H.pullback, H.pullback, H.mapOfExact_apply, H.mapOfExact_apply,
    H.mapOfExact_apply, H.mapOfExact_apply, H.map_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero, nat,
    Ext.mk₀_comp_mk₀_assoc, Category.assoc, pullbackAbCommSqApp_constZ]

/-- **The edge maps commute with pullback**: for a commutative square `f' ≫ g = g' ≫ f` of
continuous maps and `x ∈ Hⁿ(X, f_* G)`, the edge map of `f'` applied to the image of `g^* x`
under the base change morphism `g⁻¹ f_* G ⟶ f'_* g'⁻¹ G` is `g'^*` of the edge map of `x`. -/
theorem H.pushforwardEdge_pullback (G : AbSheaf Y) {n : ℕ} (x : H ((pushforwardAb f).obj G) n) :
    H.pushforwardEdge f' ((pullbackAb g').obj G) n
        (H.map (pullbackPushforwardBaseChangeApp h G) n (H.pullback g x)) =
      H.pullback g' (H.pushforwardEdge f G n x) := by
  rw [H.pushforwardEdge_apply, H.pushforwardEdge_apply, H.pullback_map, ← H.map_comp_apply,
    pullbackAb_map_pullbackPushforwardBaseChangeApp_comp_pushforwardCounit, H.map_comp_apply,
    H.map_pullbackAbCommSqApp_pullback_pullback, H.pullback_map]

/-- **`Hⁿ(Y, G) ≃+ Hⁿ(X, f_* G)` commutes with pullback**: for a commutative square
`f' ≫ g = g' ≫ f` of continuous maps, `G` `f`-acyclic, `g'⁻¹ G` `f'`-acyclic and `x ∈ Hⁿ(Y, G)`,
the class `g'^* x` corresponds in `Hⁿ(X', f'_* g'⁻¹ G)` to the image of `g^* x` under the base
change morphism `g⁻¹ f_* G ⟶ f'_* g'⁻¹ G`. -/
theorem H.pushforwardAcyclicAddEquiv_pullback {G : AbSheaf Y} (hG : IsPushforwardAcyclic f G)
    (hG' : IsPushforwardAcyclic f' ((pullbackAb g').obj G)) {n : ℕ} (x : H G n) :
    H.pushforwardAcyclicAddEquiv f' hG' n (H.pullback g' x) =
      H.map (pullbackPushforwardBaseChangeApp h G) n
        (H.pullback g (H.pushforwardAcyclicAddEquiv f hG n x)) := by
  apply (H.bijective_pushforwardEdge f' hG' n).1
  rw [H.pushforwardEdge_pushforwardAcyclicAddEquiv, H.pushforwardEdge_pullback,
    H.pushforwardEdge_pushforwardAcyclicAddEquiv]

end BaseChange

end TopCat.Sheaf

end
