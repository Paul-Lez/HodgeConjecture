/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.CocycleTwistLocal
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.FiniteStalk
public import Mathlib.RingTheory.Nakayama

/-!
# Multiplication by a section on stalks, and Nakayama's lemma for sheaves of modules

Let `ψ : P ⟶ Q` be a morphism of sheaves of modules on a locally ringed space `Y`, and
`x ∈ Γ(Y, O)` a section over an open `O`. We consider three conditions on `ψ` over `O`:

- (image) `ψ(P(W)) ⊆ x · Q(W)` for all `W ≤ O`;
- (kernel) `ψ(s) = 0` implies `x · s = 0`, for `s ∈ P(W)`, `W ≤ O`;
- (cokernel) `x · Q(W) ⊆ ψ(P(W))` for all `W ≤ O`.

They pass to stalks at points `y ∈ O`: `ψ_y(P_y) ⊆ x_y Q_y`
(`LocallyRingedSpace.exists_stalk_map_eq_germ_smul`), `x_y` kills `(ker ψ)_y`
(`LocallyRingedSpace.germ_smul_stalk_kernel_eq_zero`) and `(coker ψ)_y`
(`LocallyRingedSpace.germ_smul_stalk_cokernel_eq_zero`).

**Nakayama** (`LocallyRingedSpace.surjective_stalk_of_surjective_stalk_comp_cokernel`): if `Q` is of
finite type, `ψ` satisfies (image) near `y`, `x_y` lies in the maximal ideal, and `σ : F ⟶ Q` is
such that `F ⟶ Q ⟶ coker ψ` is surjective on the stalk at `y`, then `σ` is surjective on the stalk
at `y`. Stalks of sheaves of finite type are finitely generated
(`LocallyRingedSpace.finite_stalk_of_isFiniteType`).

Further tools: `LocallyRingedSpace.surjective_stalk_iff_forall` (stalk surjectivity in terms of
sections), `LocallyRingedSpace.surjective_stalk_pushforward` (pushforward along a homeomorphism),
`LocallyRingedSpace.surjective_stalk_modTwistMap_iff` (twisting),
`LocallyRingedSpace.freeMkTop` (the morphism `𝒪^I ⟶ M` given by global sections),
`LocallyRingedSpace.exists_surjective_stalk_comp_of_surjective_app_top` (lifting generators along a
morphism surjective on global sections),
`LocallyRingedSpace.exists_surjective_stalk_of_subsingleton` (one-point spaces), and the
predicates `LocallyRingedSpace.RangeLESMul`, `LocallyRingedSpace.SMulKerEqZero`,
`LocallyRingedSpace.SMulLERange` for the three conditions above.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace Opposite Limits

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

variable {Y : LocallyRingedSpace.{u}}

variable {P Q : SheafOfModules.{u} Y.ringSheaf} (ψ : P ⟶ Q) {O : Opens Y.toPresheafedSpace}
  (x : Y.presheaf.obj (op O))

/-- The germ at `y` of a section of a sheaf of modules, as an element of the stalk module. -/
def germMod (M : SheafOfModules.{u} Y.ringSheaf) {W : Opens Y.toPresheafedSpace} {y : Y}
    (hy : y ∈ W) (s : M.val.obj (op W)) : (Y.stalkFunctor y).obj M :=
  TopCat.Presheaf.germ M.val.presheaf W y hy s

/-- Every element of a stalk is the germ of a section over an open inside a given
neighbourhood. -/
lemma exists_germMod_eq_of_le {M : SheafOfModules.{u} Y.ringSheaf} {y : Y} (hy : y ∈ O)
    (m : (Y.stalkFunctor y).obj M) :
    ∃ (W : Opens Y.toPresheafedSpace) (_ : W ≤ O) (hyW : y ∈ W) (s : M.val.obj (op W)),
      germMod M hyW s = m := by
  obtain ⟨V, hyV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  exact ⟨V ⊓ O, inf_le_right, ⟨hyV, hy⟩, M.val.presheaf.map (homOfLE inf_le_left).op t,
    TopCat.Presheaf.germ_res_apply M.val.presheaf _ y _ t⟩

/-- The germ of `r • s` is the product of the germs. -/
lemma germMod_smul {M : SheafOfModules.{u} Y.ringSheaf} {W : Opens Y.toPresheafedSpace} {y : Y}
    (hy : y ∈ W) (r : Y.presheaf.obj (op W)) (s : M.val.obj (op W)) :
    germMod M hy (r • s) = Y.presheaf.germ W y hy r • germMod M hy s :=
  PresheafOfModules.germ_smul _ _ _ _ _ _

@[simp]
lemma germMod_zero {M : SheafOfModules.{u} Y.ringSheaf} {W : Opens Y.toPresheafedSpace} {y : Y}
    (hy : y ∈ W) : germMod M hy (0 : M.val.obj (op W)) = 0 :=
  map_zero _

/-- The stalk map of a morphism on the germ of a section. -/
lemma stalkFunctor_map_germMod {W : Opens Y.toPresheafedSpace} {y : Y} (hy : y ∈ W)
    (s : P.val.obj (op W)) :
    (Y.stalkFunctor y).map ψ (germMod P hy s) = germMod Q hy (ψ.val.app (op W) s) :=
  PresheafOfModules.stalkFunctor_map_germ y P.val Q.val ψ.val W hy s

/-- The germ of a restriction of a section of `𝒪_Y`. -/
lemma germ_restrictOpen {W : Opens Y.toPresheafedSpace} (hW : W ≤ O) {y : Y} (hy : y ∈ W) :
    Y.presheaf.germ W y hy (TopCat.Presheaf.restrictOpen x W hW) =
      Y.presheaf.germ O y (hW hy) x :=
  TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hW) y hy x

/-- **Image condition on stalks**: if `ψ(P(W)) ⊆ x · Q(W)` for all `W ≤ O`, then
`ψ_y(P_y) ⊆ x_y Q_y` for `y ∈ O`. -/
lemma exists_stalk_map_eq_germ_smul
    (hψ : ∀ (W : Opens Y.toPresheafedSpace) (hW : W ≤ O) (s : P.val.obj (op W)),
      ∃ q : Q.val.obj (op W), ψ.val.app (op W) s = TopCat.Presheaf.restrictOpen x W hW • q)
    {y : Y} (hy : y ∈ O) (p : (Y.stalkFunctor y).obj P) :
    ∃ q : (Y.stalkFunctor y).obj Q, (Y.stalkFunctor y).map ψ p = Y.presheaf.germ O y hy x • q := by
  obtain ⟨W, hW, hyW, s, rfl⟩ := exists_germMod_eq_of_le hy p
  obtain ⟨q, hq⟩ := hψ W hW s
  refine ⟨germMod Q hyW q, ?_⟩
  rw [stalkFunctor_map_germMod, hq, germMod_smul, germ_restrictOpen]

/-- **Kernel condition on stalks**: if `ψ(s) = 0` implies `x · s = 0` over opens `W ≤ O`, then
`x_y` kills `(ker ψ)_y` for `y ∈ O`. -/
lemma germ_smul_stalk_kernel_eq_zero
    (hψ : ∀ (W : Opens Y.toPresheafedSpace) (hW : W ≤ O) (s : P.val.obj (op W)),
      ψ.val.app (op W) s = 0 → TopCat.Presheaf.restrictOpen x W hW • s = 0)
    {y : Y} (hy : y ∈ O) (a : (Y.stalkFunctor y).obj (kernel ψ)) :
    Y.presheaf.germ O y hy x • a = 0 := by
  obtain ⟨W, hW, hyW, t, rfl⟩ := exists_germMod_eq_of_le hy a
  apply injective_stalk_of_mono (kernel.ι ψ) y
  have h0 : ψ.val.app (op W) ((kernel.ι ψ).val.app (op W) t) = 0 :=
    congrArg (fun φ : kernel ψ ⟶ Q ↦ φ.val.app (op W) t) (kernel.condition ψ)
  rw [map_smul, map_zero, stalkFunctor_map_germMod, ← germ_restrictOpen x hW hyW,
    ← germMod_smul, hψ W hW _ h0, germMod_zero]

/-- **Cokernel condition on stalks**: if `x · Q(W) ⊆ ψ(P(W))` for all `W ≤ O`, then `x_y` kills
`(coker ψ)_y` for `y ∈ O`. -/
lemma germ_smul_stalk_cokernel_eq_zero
    (hψ : ∀ (W : Opens Y.toPresheafedSpace) (hW : W ≤ O) (q : Q.val.obj (op W)),
      ∃ s : P.val.obj (op W), ψ.val.app (op W) s = TopCat.Presheaf.restrictOpen x W hW • q)
    {y : Y} (hy : y ∈ O) (c : (Y.stalkFunctor y).obj (cokernel ψ)) :
    Y.presheaf.germ O y hy x • c = 0 := by
  obtain ⟨m, rfl⟩ := surjective_stalk_of_epi (cokernel.π ψ) y c
  obtain ⟨W, hW, hyW, q, rfl⟩ := exists_germMod_eq_of_le hy m
  obtain ⟨s, hs⟩ := hψ W hW q
  rw [← map_smul, ← germ_restrictOpen x hW hyW, ← germMod_smul, ← hs,
    ← stalkFunctor_map_germMod]
  exact stalkFunctor_map_map_eq_zero _ _ (cokernel.condition ψ) y _

/-- **Nakayama's lemma for sheaves of modules**: let `Q` be of finite type, let `ψ : P ⟶ Q`
satisfy `ψ(P(W)) ⊆ x · Q(W)` for `W ≤ O`, and let `y ∈ O` with `x_y` in the maximal ideal. If
`σ : F ⟶ Q` composed with `Q ⟶ coker ψ` is surjective on the stalk at `y`, then `σ` is surjective
on the stalk at `y`. -/
theorem surjective_stalk_of_surjective_stalk_comp_cokernel [Q.IsFiniteType]
    {F : SheafOfModules.{u} Y.ringSheaf} (σ : F ⟶ Q)
    (hψ : ∀ (W : Opens Y.toPresheafedSpace) (hW : W ≤ O) (s : P.val.obj (op W)),
      ∃ q : Q.val.obj (op W), ψ.val.app (op W) s = TopCat.Presheaf.restrictOpen x W hW • q)
    {y : Y} (hy : y ∈ O) (hx : Y.presheaf.germ O y hy x ∈ IsLocalRing.maximalIdeal _)
    (hσ : Function.Surjective ((Y.stalkFunctor y).map (σ ≫ cokernel.π ψ))) :
    Function.Surjective ((Y.stalkFunctor y).map σ) := by
  rw [← subsingleton_stalk_cokernel_iff]
  haveI : (cokernel σ).IsFiniteType := SheafOfModules.isFiniteType_cokernel σ
  haveI := finite_stalk_of_isFiniteType (cokernel σ) y
  set I : Ideal (Y.presheaf.stalk y) := Ideal.span {Y.presheaf.germ O y hy x}
  have hle : (⊤ : Submodule (Y.presheaf.stalk y) ((Y.stalkFunctor y).obj (cokernel σ))) ≤
      I • ⊤ := by
    intro n _
    obtain ⟨m, rfl⟩ := surjective_stalk_of_epi (cokernel.π σ) y n
    obtain ⟨f, hf⟩ := hσ ((Y.stalkFunctor y).map (cokernel.π ψ) m)
    have hex := exact_stalk (ShortComplex.mk ψ (cokernel.π ψ) (cokernel.condition ψ))
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ψ)) y
    obtain ⟨p, hp⟩ := (hex (m - (Y.stalkFunctor y).map σ f)).1 (by
      rw [map_sub, sub_eq_zero, ← hf, Functor.map_comp]
      rfl)
    obtain ⟨q, hq⟩ := exists_stalk_map_eq_germ_smul ψ x hψ hy p
    have hm : m = (Y.stalkFunctor y).map σ f + Y.presheaf.germ O y hy x • q := by
      rw [← hq]
      rw [hp, add_sub_cancel]
    rw [hm, map_add, stalkFunctor_map_map_eq_zero _ _ (cokernel.condition σ), zero_add,
      map_smul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I ⊤ Module.Finite.fg_top hle (by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le,
      Set.singleton_subset_iff]
    exact hx)
  exact ⟨fun a b ↦ by
    have ha : a ∈ (⊥ : Submodule (Y.presheaf.stalk y) _) := hbot ▸ Submodule.mem_top
    have hb : b ∈ (⊥ : Submodule (Y.presheaf.stalk y) _) := hbot ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at ha hb
    rw [ha, hb]⟩

section Local

/-- **Stalk surjectivity in terms of sections**: `f` is surjective on the stalk at `y` if and only
if every section of the target near `y` lifts near `y`. -/
lemma surjective_stalk_iff_forall (f : P ⟶ Q) (y : Y) :
    Function.Surjective ((Y.stalkFunctor y).map f) ↔
      ∀ (W : Opens Y.toPresheafedSpace), y ∈ W → ∀ s : Q.val.obj (op W),
        ∃ (W' : Opens Y.toPresheafedSpace) (h : W' ≤ W), y ∈ W' ∧
          ∃ t : P.val.obj (op W'), f.val.app (op W') t = modRes s W' h := by
  constructor
  · intro hf W hy s
    obtain ⟨p, hp⟩ := hf (germMod Q hy s)
    obtain ⟨W₀, -, hy₀, t₀, rfl⟩ := exists_germMod_eq_of_le (O := ⊤) trivial p
    rw [stalkFunctor_map_germMod] at hp
    obtain ⟨W', hyW', i₁, i₂, heq⟩ := TopCat.Presheaf.germ_eq Q.val.presheaf y hy₀ hy _ _ hp
    refine ⟨W', i₂.le, hyW', modRes t₀ W' i₁.le, ?_⟩
    rw [modHom_modRes]
    exact heq
  · intro h m
    obtain ⟨W, -, hy, s, rfl⟩ := exists_germMod_eq_of_le (O := ⊤) trivial m
    obtain ⟨W', hW', hy', t, ht⟩ := h W hy s
    refine ⟨germMod P hy' t, ?_⟩
    rw [stalkFunctor_map_germMod, ht]
    exact TopCat.Presheaf.germ_res_apply Q.val.presheaf (homOfLE hW') y hy' s

/-- **Pushforward along a homeomorphism preserves stalk surjectivity**: for `a : X ⟶ Y` whose
underlying map has an inverse `b`, if `f` is surjective on the stalk at `x`, then `a_* f` is
surjective on the stalk at `a x`. -/
lemma surjective_stalk_pushforward {X : LocallyRingedSpace.{u}} (a : X ⟶ Y) (b : Y ⟶ X)
    (hab : ∀ x, b.base (a.base x) = x) (hba : ∀ y, a.base (b.base y) = y)
    {P' Q' : SheafOfModules.{u} X.ringSheaf} (f : P' ⟶ Q') (x : X)
    (hf : Function.Surjective ((X.stalkFunctor x).map f)) :
    Function.Surjective ((Y.stalkFunctor (a.base x)).map
      ((SheafOfModules.pushforward.{u} a.toRingSheafHom).map f)) := by
  rw [surjective_stalk_iff_forall] at hf ⊢
  intro W hy s
  obtain ⟨W'', hW'', hx, t, ht⟩ := hf ((Opens.map a.base).obj W) hy s
  let W' : Opens Y.toPresheafedSpace := (Opens.map b.base).obj W''
  have h₁ : W' ≤ W := fun y hy ↦ by
    have := hW'' hy
    change a.base (b.base y) ∈ W at this
    rwa [hba] at this
  have h₂ : (Opens.map a.base).obj W' ≤ W'' := fun x hx ↦ by
    change b.base (a.base x) ∈ W'' at hx
    rwa [hab] at hx
  refine ⟨W', h₁, show b.base (a.base x) ∈ W'' by rwa [hab], modRes t _ h₂, ?_⟩
  change f.val.app _ (modRes t _ h₂) = modRes (N := Q') s _ _
  rw [modHom_modRes, ht, modRes_res]

end Local

section FreeMk

variable (M : SheafOfModules.{u} Y.ringSheaf) {I : Type u}

/-- The morphism `𝒪^I ⟶ M` sending the `i`-th generator to a global section `s i`. -/
def freeMkTop (s : I → M.val.obj (op ⊤)) : SheafOfModules.free I ⟶ M :=
  M.freeHomEquiv.symm fun i ↦ SheafOfModules.sectionOfTerminal isTerminalTop M (s i)

@[simp]
lemma generatorSection_freeMkTop (s : I → M.val.obj (op ⊤)) (i : I) :
    generatorSection (freeMkTop M s) i = s i := by
  rw [generatorSection, freeMkTop, Equiv.apply_symm_apply, SheafOfModules.sectionOfTerminal_val,
    show isTerminalTop.from ⊤ = 𝟙 (⊤ : Opens Y.toPresheafedSpace) from
      isTerminalTop.hom_ext _ _, op_id, M.val.map_id]
  rfl

/-- If the germs at `y` of the images of the generators span the stalk, the morphism is
surjective on the stalk at `y`. -/
lemma surjective_stalk_of_span_germ_eq_top {N : SheafOfModules.{u} Y.ringSheaf}
    (g : SheafOfModules.free I ⟶ N) (y : Y)
    (h : Submodule.span (Y.presheaf.stalk y)
      (Set.range fun i ↦ germTop N y (generatorSection g i)) = ⊤) :
    Function.Surjective ((Y.stalkFunctor y).map g) := by
  rw [← LinearMap.range_eq_top (f := ((Y.stalkFunctor y).map g).hom), eq_top_iff, ← h,
    Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine ⟨germTop _ y (generatorSection (𝟙 _) i), ?_⟩
  change (Y.stalkFunctor y).map g _ = _
  rw [stalkFunctor_map_germTop, ← generatorSection_comp, Category.id_comp]

/-- **Lifting generators**: if `π : M ⟶ C` is surjective on global sections and `τ : 𝒪^I ⟶ C` is
an epimorphism with `I` finite, then there is `σ : 𝒪^I ⟶ M` with `σ ≫ π` surjective on all
stalks. -/
lemma exists_surjective_stalk_comp_of_surjective_app_top {C : SheafOfModules.{u} Y.ringSheaf}
    (π : M ⟶ C) (hπ : Function.Surjective (π.val.app (op ⊤))) [Finite I]
    (τ : SheafOfModules.free I ⟶ C) [Epi τ] :
    ∃ σ : SheafOfModules.free I ⟶ M,
      ∀ y : Y, Function.Surjective ((Y.stalkFunctor y).map (σ ≫ π)) := by
  choose s hs using fun i ↦ hπ (generatorSection τ i)
  refine ⟨freeMkTop M s, fun y ↦ surjective_stalk_of_span_germ_eq_top _ y ?_⟩
  have hgen : ∀ i, generatorSection (freeMkTop M s ≫ π) i = generatorSection τ i := fun i ↦ by
    rw [generatorSection_comp, generatorSection_freeMkTop]
    exact hs i
  simp_rw [hgen]
  exact span_germ_eq_top τ y

/-- **On a one-point space**, a sheaf of finite type is generated by finitely many global
sections at the point. -/
lemma exists_surjective_stalk_of_subsingleton [Subsingleton Y] [M.IsFiniteType] (y : Y) :
    ∃ (J : Type u) (_ : Finite J) (σ : SheafOfModules.free J ⟶ M),
      Function.Surjective ((Y.stalkFunctor y).map σ) := by
  classical
  haveI := finite_stalk_of_isFiniteType M y
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := Y.presheaf.stalk y)
    (M := (Y.stalkFunctor y).obj M)
  have htop (W : Opens Y.toPresheafedSpace) (hW : y ∈ W) : ⊤ ≤ W := fun x _ ↦ by
    rwa [Subsingleton.elim (α := Y) x y]
  choose W hyW t ht using fun m : S ↦ TopCat.Presheaf.exists_germ_eq M.val.presheaf m.1
  refine ⟨S, inferInstance, freeMkTop M fun m ↦ modRes (t m) ⊤ (htop _ (hyW m)), ?_⟩
  refine surjective_stalk_of_span_germ_eq_top _ y (eq_top_iff.2 ?_)
  rw [← hS, Submodule.span_le]
  intro m hm
  refine Submodule.subset_span ⟨⟨m, hm⟩, ?_⟩
  change germTop M y (generatorSection (freeMkTop M _) _) = m
  rw [generatorSection_freeMkTop]
  exact (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE (htop _ (hyW ⟨m, hm⟩))) y trivial
    _).trans (ht ⟨m, hm⟩)

end FreeMk

section Twist

variable {ι : Type} {V : ι → Opens Y.toPresheafedSpace} (c : ModCocycle V)

/-- Stalk surjectivity is invariant under isomorphisms of the target. -/
lemma surjective_stalk_comp_iso_iff {F : SheafOfModules.{u} Y.ringSheaf} (g : F ⟶ P)
    (e : P ≅ Q) (y : Y) :
    Function.Surjective ((Y.stalkFunctor y).map (g ≫ e.hom)) ↔
      Function.Surjective ((Y.stalkFunctor y).map g) := by
  have he : Function.Bijective ((Y.stalkFunctor y).map e.hom) :=
    ConcreteCategory.bijective_of_isIso ((Y.stalkFunctor y).map e.hom)
  rw [Functor.map_comp]
  constructor
  · intro h x
    obtain ⟨a, ha⟩ := h ((Y.stalkFunctor y).map e.hom x)
    exact ⟨a, he.1 ha⟩
  · intro h
    exact he.2.comp h

/-- Stalk surjectivity is invariant under isomorphisms of the source. -/
lemma surjective_stalk_iso_comp_iff {F F' : SheafOfModules.{u} Y.ringSheaf} (e : F' ≅ F)
    (g : F ⟶ P) (y : Y) :
    Function.Surjective ((Y.stalkFunctor y).map (e.hom ≫ g)) ↔
      Function.Surjective ((Y.stalkFunctor y).map g) := by
  have he : Function.Bijective ((Y.stalkFunctor y).map e.hom) :=
    ConcreteCategory.bijective_of_isIso ((Y.stalkFunctor y).map e.hom)
  rw [Functor.map_comp]
  constructor
  · intro h x
    obtain ⟨a, ha⟩ := h x
    exact ⟨_, ha⟩
  · intro h
    exact h.comp he.2

/-- **Stalk surjectivity is invariant under twisting**, at points of a member of the cover. -/
lemma surjective_stalk_modTwistMap_iff (hV : ⨆ i, V i = ⊤) {i : ι} {y : Y} (hy : y ∈ V i)
    (g : P ⟶ Q) :
    Function.Surjective ((Y.stalkFunctor y).map (modTwistMap c g)) ↔
      Function.Surjective ((Y.stalkFunctor y).map g) := by
  haveI : (modTwistFunctor c).IsEquivalence := (modTwistEquivalence c hV).isEquivalence_functor
  haveI : (modTwistFunctor c).Additive := Functor.additive_of_preserves_binary_products _
  rw [← subsingleton_stalk_cokernel_iff, ← subsingleton_stalk_cokernel_iff]
  have e : cokernel ((modTwistFunctor c).map g) ≅ modTwist (cokernel g) c :=
    (PreservesCokernel.iso (modTwistFunctor c) g).symm
  rw [← subsingleton_stalk_modTwist_iff (cokernel g) c hy]
  exact ((Y.stalkFunctor y).mapIso e).toLinearEquiv.toEquiv.subsingleton_congr

end Twist

section Predicates

variable {Q' : SheafOfModules.{u} Y.ringSheaf}

/-- `ψ(P(W)) ⊆ x · Q(W)` for all `W ≤ O`. -/
def RangeLESMul : Prop :=
  ∀ (W : Opens Y.toPresheafedSpace) (hW : W ≤ O) (s : P.val.obj (op W)),
    ∃ q : Q.val.obj (op W), ψ.val.app (op W) s = TopCat.Presheaf.restrictOpen x W hW • q

/-- `ψ(s) = 0` implies `x · s = 0`, for `s ∈ P(W)`, `W ≤ O`. -/
def SMulKerEqZero : Prop :=
  ∀ (W : Opens Y.toPresheafedSpace) (hW : W ≤ O) (s : P.val.obj (op W)),
    ψ.val.app (op W) s = 0 → TopCat.Presheaf.restrictOpen x W hW • s = 0

/-- `x · Q(W) ⊆ ψ(P(W))` for all `W ≤ O`. -/
def SMulLERange : Prop :=
  ∀ (W : Opens Y.toPresheafedSpace) (hW : W ≤ O) (q : Q.val.obj (op W)),
    ∃ s : P.val.obj (op W), ψ.val.app (op W) s = TopCat.Presheaf.restrictOpen x W hW • q

variable {ψ x}

lemma RangeLESMul.comp_iso (h : RangeLESMul ψ x) (e : Q ≅ Q') : RangeLESMul (ψ ≫ e.hom) x := by
  intro W hW s
  obtain ⟨q, hq⟩ := h W hW s
  exact ⟨e.hom.val.app (op W) q, by
    rw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply, hq,
      modHom_smul]⟩

lemma SMulKerEqZero.comp_iso (h : SMulKerEqZero ψ x) (e : Q ≅ Q') :
    SMulKerEqZero (ψ ≫ e.hom) x := by
  intro W hW s hs
  refine h W hW s ?_
  have := congrArg (e.inv.val.app (op W)) hs
  rw [map_zero, SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    ← ModuleCat.comp_apply, ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val,
    e.hom_inv_id] at this
  exact this

lemma SMulLERange.comp_iso (h : SMulLERange ψ x) (e : Q ≅ Q') : SMulLERange (ψ ≫ e.hom) x := by
  intro W hW q
  obtain ⟨s, hs⟩ := h W hW (e.inv.val.app (op W) q)
  refine ⟨s, ?_⟩
  rw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply, hs,
    modHom_smul, ← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, e.inv_hom_id]
  rfl

/-- The chart trivialisation of a twist commutes with twisted morphisms. -/
lemma modTwistSectionsEquiv_modTwistMap {ι : Type} {V : ι → Opens Y.toPresheafedSpace}
    (c : ModCocycle V) (i : ι) {W : Opens Y.toPresheafedSpace} (hW : W ≤ V i)
    (ψ : P ⟶ Q) (s : (modTwist P c).val.obj (op W)) :
    modTwistSectionsEquiv c i hW ((modTwistMap c ψ).val.app (op W) s) =
      ψ.val.app (op W) (modTwistSectionsEquiv c i hW s) := by
  rw [modTwistSectionsEquiv_apply, modTwistSectionsEquiv_apply, modTwistComp_modTwistMap_app,
    modHom_modRes]

/-- The condition `ψ(P(W)) ⊆ x · Q(W)` passes to twists, over an open inside a member of the
cover. -/
lemma RangeLESMul.modTwistMap (h : RangeLESMul ψ x) {ι : Type}
    {V : ι → Opens Y.toPresheafedSpace} (c : ModCocycle V) (i : ι) (hO : O ≤ V i) :
    RangeLESMul (modTwistMap c ψ) x := by
  intro W hW s
  obtain ⟨q, hq⟩ := h W hW (modTwistSectionsEquiv c i (hW.trans hO) s)
  refine ⟨(modTwistSectionsEquiv c i (hW.trans hO)).symm q,
    (modTwistSectionsEquiv c i (hW.trans hO)).injective ?_⟩
  rw [modTwistSectionsEquiv_modTwistMap, hq, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]

end Predicates

end AlgebraicGeometry.LocallyRingedSpace

end
