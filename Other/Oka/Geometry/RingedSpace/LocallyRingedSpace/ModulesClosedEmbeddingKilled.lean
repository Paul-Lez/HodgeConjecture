/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesClosedEmbedding
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.CohomologyModule
public import Other.Oka.Topology.Sheaves.Cohomology.BaseChange

/-!
# Sheaves of modules killed by the ideal of a closed embedding

Let `f : X ⟶ Y` be a morphism of locally ringed spaces whose underlying map is a closed embedding
and whose stalk maps are surjective. Write `I_y = f.pushforwardStalkIdeal y ⊆ 𝒪_{Y,y}` for the
kernel of `𝒪_{Y,y} → (f_* 𝒪_X)_y`, the stalk at `y` of the ideal sheaf of `X`. Then:

- `I_{f x}` is the kernel of the stalk map `𝒪_{Y,f x} → 𝒪_{X,x}`
  (`AlgebraicGeometry.LocallyRingedSpace.Hom.pushforwardStalkIdeal_eq_ker`), and `I_y = 𝒪_{Y,y}`
  for `y ∉ f(X)` (`AlgebraicGeometry.LocallyRingedSpace.Hom.pushforwardStalkIdeal_eq_top`).
- **A sheaf of `𝒪_Y`-modules `A` is of the form `f_* G` if and only if each stalk `A_y` is killed
  by `I_y`**, and then `A ≅ f_* f^* A` via the unit of `f^* ⊣ f_*`
  (`AlgebraicGeometry.LocallyRingedSpace.Hom.isIso_pullbackModulesAdj_unit_app_iff`,
  `AlgebraicGeometry.LocallyRingedSpace.Hom.unitIsoOfSMulEqZero`).
- Cohomology is unchanged by `f_*`: `Hᵠ(X, G) ≃ Hᵠ(Y, f_* G)`, semilinearly along
  `Γ(f) : Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`
  (`AlgebraicGeometry.LocallyRingedSpace.Hom.pushforwardModulesHAddEquiv`,
  `AlgebraicGeometry.LocallyRingedSpace.Hom.pushforwardModulesHAddEquiv_smul`); hence
  `Hᵠ(Y, A) ≃ Hᵠ(X, f^* A)` for `A` killed by the ideal
  (`AlgebraicGeometry.LocallyRingedSpace.Hom.HAddEquivOfSMulEqZero`).

To verify the hypothesis in practice we record how germs of sections act on stalks:
`AlgebraicGeometry.LocallyRingedSpace.germ_smul_eq_zero_of_forall` (a local section killing all
sections of `A` near `y` kills `A_y`) and
`AlgebraicGeometry.LocallyRingedSpace.Γgerm_smul_eq_zero_of_modulesSMul_eq_zero` (the same for a
global section `r` with `modulesSMul A r = 0`).
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Limits Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

/-- If every element of a family `g` kills a module, so does the ideal spanned by the family. -/
lemma smul_eq_zero_of_mem_span {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type*} (g : ι → R) (hg : ∀ j (m : M), g j • m = 0) {r : R}
    (hr : r ∈ Ideal.span (Set.range g)) (m : M) : r • m = 0 := by
  have : Ideal.span (Set.range g) ≤ Module.annihilator R M := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact Module.mem_annihilator.2 (hg j)
  exact Module.mem_annihilator.1 (this hr) m

section Germ

variable {Y : LocallyRingedSpace.{u}} (A : SheafOfModules.{u} Y.ringSheaf)

/-- **A local section killing all nearby sections kills the stalk**: if `r ∈ 𝒪_Y(U)` satisfies
`r|_V • t = 0` for all `V ≤ U` and `t ∈ A(V)`, then the germ of `r` at `y ∈ U` kills `A_y`. -/
lemma germ_smul_eq_zero_of_forall {U : Opens Y} (r : Y.presheaf.obj (op U))
    (hr : ∀ (V : Opens Y) (hVU : V ≤ U) (t : A.val.obj (op V)),
      (show Y.ringSheaf.obj.obj (op V) from Y.presheaf.map (homOfLE hVU).op r) • t = 0)
    (y : Y) (hy : y ∈ U) (m : (Y.stalkFunctor y).obj A) :
    Y.presheaf.germ U y hy r • m = 0 := by
  obtain ⟨V, hV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq A.val.presheaf m
  have hle : U ⊓ V ≤ U := inf_le_left
  rw [← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hle) y ⟨hy, hV⟩ r]
  erw [← TopCat.Presheaf.germ_res_apply A.val.presheaf (homOfLE (inf_le_right : U ⊓ V ≤ V)) y
    ⟨hy, hV⟩ t]
  erw [← PresheafOfModules.germ_smul]
  refine (congrArg _ (hr (U ⊓ V) hle _)).trans (map_zero _)

/-- **A global section acting by zero kills every stalk**: if multiplication by `r ∈ Γ(Y, 𝒪_Y)`
is the zero endomorphism of `A`, the germ of `r` at every point kills the stalk of `A`. -/
lemma Γgerm_smul_eq_zero_of_modulesSMul_eq_zero (r : Y.presheaf.obj (op ⊤))
    (hr : modulesSMul A r = 0) (y : Y) (m : (Y.stalkFunctor y).obj A) :
    Y.presheaf.Γgerm y r • m = 0 := by
  refine germ_smul_eq_zero_of_forall A r (fun V hV t ↦ ?_) y trivial m
  exact congrArg (fun φ : A ⟶ A ↦ φ.val.app (op V) t) hr

end Germ

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)

/-- A germ at `y` in the ideal of the image of `f` is the germ of a section over a neighbourhood
of `y` killed by `f^♯`. -/
lemma Hom.exists_germ_eq_of_mem_pushforwardStalkIdeal (y : Y) (r : Y.presheaf.stalk y)
    (hr : r ∈ f.pushforwardStalkIdeal y) :
    ∃ (W : Opens Y) (hy : y ∈ W) (s : Y.presheaf.obj (op W)),
      f.c.app (op W) s = 0 ∧ Y.presheaf.germ W y hy s = r := by
  obtain ⟨W, hyW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf r
  have hr' : TopCat.Presheaf.germ (f.base _* X.presheaf) W y hyW (f.c.app (op W) s) =
      TopCat.Presheaf.germ (f.base _* X.presheaf) W y hyW 0 := by
    refine Eq.trans ?_ (map_zero _).symm
    rw [Hom.pushforwardStalkIdeal, RingHom.mem_ker] at hr
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hr
    exact hr
  obtain ⟨W', hW', iW, iW', hWe⟩ := TopCat.Presheaf.germ_eq _ y hyW hyW _ _ hr'
  refine ⟨W', hW', Y.presheaf.map iW.op s, ?_, TopCat.Presheaf.germ_res_apply _ _ _ _ _⟩
  have hnat := congrArg (fun φ ↦ φ s) (congrArg CommRingCat.Hom.hom (f.c.naturality iW.op))
  exact hnat.trans (hWe.trans (map_zero _))

/-- The germ of a section killed by `f^♯` lies in the ideal of the image of `f`. -/
lemma Hom.germ_mem_pushforwardStalkIdeal {W : Opens Y} (y : Y) (hy : y ∈ W)
    (s : Y.presheaf.obj (op W)) (hs : f.c.app (op W) s = 0) :
    Y.presheaf.germ W y hy s ∈ f.pushforwardStalkIdeal y := by
  rw [Hom.pushforwardStalkIdeal, RingHom.mem_ker]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact (congrArg _ hs).trans (map_zero _)

/-- **Base change of the ideal of the image**: for a commutative square `f' ≫ g = g' ≫ f`, the
stalk map of `g` carries the ideal of the image of `f` at `g y'` into the ideal of the image of
`f'` at `y'`. -/
lemma Hom.map_pushforwardStalkIdeal_le {X' Y' : LocallyRingedSpace.{u}} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (h : f' ≫ g = g' ≫ f) (y' : Y') :
    Ideal.map (g.stalkMap y').hom (f.pushforwardStalkIdeal (g.base y')) ≤
      f'.pushforwardStalkIdeal y' := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  obtain ⟨W, hW, s, hs, rfl⟩ := f.exists_germ_eq_of_mem_pushforwardStalkIdeal _ r hr
  rw [Ideal.mem_comap]
  erw [LocallyRingedSpace.stalkMap_germ_apply g W y' hW s]
  refine f'.germ_mem_pushforwardStalkIdeal y' hW _ ?_
  have key : ∀ φ ψ : X' ⟶ Y, φ = ψ → ψ.c.app (op W) s = 0 → φ.c.app (op W) s = 0 := by
    rintro _ _ rfl h
    exact h
  refine key (f' ≫ g) (g' ≫ f) h ?_
  change g'.c.app _ (f.c.app (op W) s) = 0
  rw [hs]
  exact map_zero (g'.c.app _).hom

/-- The ideal of the image, at a point `f x`, is contained in the kernel of the stalk map. -/
lemma Hom.pushforwardStalkIdeal_le_ker (x : X) :
    f.pushforwardStalkIdeal (f.base x) ≤ RingHom.ker (f.stalkMap x).hom := by
  intro r hr
  rw [RingHom.mem_ker]
  rw [Hom.pushforwardStalkIdeal, RingHom.mem_ker] at hr
  change (TopCat.Presheaf.stalkPushforward CommRingCat.{u} f.base X.presheaf x)
    (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (f.base x)).map f.c) r) = 0
  exact (congrArg _ hr).trans (map_zero _)

/-- For `f` inducing, the ideal of the image at `f x` is the kernel of the stalk map
`𝒪_{Y,f x} → 𝒪_{X,x}`. -/
lemma Hom.pushforwardStalkIdeal_eq_ker (hf : IsInducing f.base) (x : X) :
    f.pushforwardStalkIdeal (f.base x) = RingHom.ker (f.stalkMap x).hom :=
  le_antisymm (f.pushforwardStalkIdeal_le_ker x)
    fun r hr ↦ f.mem_pushforwardStalkIdeal_of_mem_ker hf x r hr

/-- **Off the closed image of `f` the ideal of the image is the unit ideal.** -/
lemma Hom.pushforwardStalkIdeal_eq_top (hcl : IsClosed (Set.range f.base)) (y : Y)
    (hy : y ∉ Set.range f.base) : f.pushforwardStalkIdeal y = ⊤ := by
  rw [Ideal.eq_top_iff_one, Hom.pushforwardStalkIdeal, RingHom.mem_ker]
  set U : Opens Y := ⟨(Set.range f.base)ᶜ, hcl.isOpen_compl⟩
  have hyU : y ∈ U := hy
  have hbot : (Opens.map f.base).obj U = ⊥ := by
    ext x
    simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, Opens.coe_bot,
      Set.mem_empty_iff_false, iff_false]
    exact fun hx ↦ hx ⟨x, rfl⟩
  have hsub : Subsingleton (X.presheaf.obj (op ((Opens.map f.base).obj U))) := by
    rw [hbot]
    exact CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEmpty)
  rw [← map_one (TopCat.Presheaf.germ Y.presheaf U y hyU).hom,
    ← TopCat.Presheaf.germ_res_apply Y.presheaf (𝟙 U) y hyU 1]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact (congrArg _ (@Subsingleton.elim _ hsub _ 0)).trans (map_zero _)

/-- **Sheaves killed by the ideal of a closed embedding are pushforwards**: if `f` is a closed
embedding with surjective stalk maps and each stalk `A_y` is killed by the ideal
`f.pushforwardStalkIdeal y` of the image, the unit `A ⟶ f_* f^* A` is an isomorphism. -/
theorem Hom.isIso_pullbackModulesAdj_unit_app_of_smul_eq_zero (hf : IsClosedEmbedding f.base)
    (hs : ∀ x, Function.Surjective (f.stalkMap x)) (A : SheafOfModules.{u} Y.ringSheaf)
    (hA : ∀ y, ∀ r ∈ f.pushforwardStalkIdeal y, ∀ m : (Y.stalkFunctor y).obj A, r • m = 0) :
    IsIso (f.pullbackModulesAdj.unit.app A) := by
  refine f.isIso_pullbackModulesAdj_unit_app hf hs A (fun y hy ↦ ⟨fun a b ↦ ?_⟩)
    (fun x r hr m ↦ ?_)
  · have h1 : (1 : Y.presheaf.stalk y) ∈ f.pushforwardStalkIdeal y := by
      rw [f.pushforwardStalkIdeal_eq_top hf.isClosed_range y hy]
      trivial
    rw [← one_smul (Y.presheaf.stalk y) a, ← one_smul (Y.presheaf.stalk y) b,
      hA y 1 h1 a, hA y 1 h1 b]
  · exact hA (f.base x) r (by rwa [f.pushforwardStalkIdeal_eq_ker hf.isInducing x]) m

/-- Conversely, if the unit `A ⟶ f_* f^* A` is an isomorphism, then each stalk `A_y` is killed by
the ideal of the image. -/
theorem Hom.smul_eq_zero_of_isIso_pullbackModulesAdj_unit_app
    (A : SheafOfModules.{u} Y.ringSheaf) [IsIso (f.pullbackModulesAdj.unit.app A)] (y : Y)
    (r : Y.presheaf.stalk y) (hr : r ∈ f.pushforwardStalkIdeal y)
    (m : (Y.stalkFunctor y).obj A) : r • m = 0 := by
  let e := ((Y.stalkFunctor y).mapIso (asIso (f.pullbackModulesAdj.unit.app A))).toLinearEquiv
  refine e.injective ((e.map_smul r m).trans ?_)
  exact (f.smul_eq_zero_of_mem_pushforwardStalkIdeal _ y r hr _).trans e.map_zero.symm

/-- **Characterisation of pushforwards along closed embeddings**: for `f` a closed embedding
with surjective stalk maps, the unit `A ⟶ f_* f^* A` is an isomorphism if and only if every stalk
`A_y` is killed by the ideal of the image. -/
theorem Hom.isIso_pullbackModulesAdj_unit_app_iff (hf : IsClosedEmbedding f.base)
    (hs : ∀ x, Function.Surjective (f.stalkMap x)) (A : SheafOfModules.{u} Y.ringSheaf) :
    IsIso (f.pullbackModulesAdj.unit.app A) ↔
      ∀ y, ∀ r ∈ f.pushforwardStalkIdeal y, ∀ m : (Y.stalkFunctor y).obj A, r • m = 0 :=
  ⟨fun _ ↦ f.smul_eq_zero_of_isIso_pullbackModulesAdj_unit_app A,
    f.isIso_pullbackModulesAdj_unit_app_of_smul_eq_zero hf hs A⟩

/-- The isomorphism `A ≅ f_* f^* A` for a sheaf `A` killed by the ideal of the image of a closed
embedding with surjective stalk maps. -/
def Hom.unitIsoOfSMulEqZero (hf : IsClosedEmbedding f.base)
    (hs : ∀ x, Function.Surjective (f.stalkMap x)) (A : SheafOfModules.{u} Y.ringSheaf)
    (hA : ∀ y, ∀ r ∈ f.pushforwardStalkIdeal y, ∀ m : (Y.stalkFunctor y).obj A, r • m = 0) :
    A ≅ (SheafOfModules.pushforward.{u} f.toRingSheafHom).obj (f.pullbackModules.obj A) :=
  @asIso _ _ _ _ (f.pullbackModulesAdj.unit.app A)
    (f.isIso_pullbackModulesAdj_unit_app_of_smul_eq_zero hf hs A hA)

/-- The isomorphism `A ≅ f_* f^* A` is the unit of `f^* ⊣ f_*`. -/
@[simp]
lemma Hom.unitIsoOfSMulEqZero_hom (hf : IsClosedEmbedding f.base)
    (hs : ∀ x, Function.Surjective (f.stalkMap x)) (A : SheafOfModules.{u} Y.ringSheaf)
    (hA : ∀ y, ∀ r ∈ f.pushforwardStalkIdeal y, ∀ m : (Y.stalkFunctor y).obj A, r • m = 0) :
    (f.unitIsoOfSMulEqZero hf hs A hA).hom = f.pullbackModulesAdj.unit.app A :=
  rfl

/-- A global section of `𝒪_Y` pulling back to zero on `X` acts by zero on every pushforward. -/
lemma modulesSMul_pushforward_eq_zero (G : SheafOfModules.{u} X.ringSheaf)
    (r : Y.presheaf.obj (op ⊤)) (hr : f.globalSectionsRingHom r = 0) :
    modulesSMul ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj G) r = 0 := by
  rw [← pushforward_map_modulesSMul, hr, modulesSMul_zero]
  ext U m
  rfl

section Cohomology

/-- **Cohomology is unchanged by pushforward along a closed embedding**:
`Hᵠ(X, G) ≃ Hᵠ(Y, f_* G)` for a sheaf of `𝒪_X`-modules `G`. -/
def Hom.pushforwardModulesHAddEquiv (hf : IsClosedEmbedding f.base)
    (G : SheafOfModules.{u} X.ringSheaf) (q : ℕ) :
    H G q ≃+ H ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj G) q :=
  TopCat.Sheaf.H.pushforwardClosedEmbeddingAddEquiv hf G.toAb q

/-- `Hᵠ(X, G) ≃ Hᵠ(Y, f_* G)` is natural in `G`. -/
lemma Hom.pushforwardModulesHAddEquiv_map (hf : IsClosedEmbedding f.base)
    {G G' : SheafOfModules.{u} X.ringSheaf} (φ : G ⟶ G') {q : ℕ} (x : H G q) :
    f.pushforwardModulesHAddEquiv hf G' q (H.map φ q x) =
      H.map ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map φ) q
        (f.pushforwardModulesHAddEquiv hf G q x) :=
  TopCat.Sheaf.H.pushforwardClosedEmbeddingAddEquiv_map hf ((modulesToAb X).map φ) x

/-- `Hᵠ(X, G) ≃ Hᵠ(Y, f_* G)` is semilinear along `Γ(f) : Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`. -/
lemma Hom.pushforwardModulesHAddEquiv_smul (hf : IsClosedEmbedding f.base)
    (G : SheafOfModules.{u} X.ringSheaf) {q : ℕ} (r : Y.presheaf.obj (op ⊤)) (x : H G q) :
    f.pushforwardModulesHAddEquiv hf G q (f.globalSectionsRingHom r • x) =
      r • f.pushforwardModulesHAddEquiv hf G q x := by
  rw [H.smul_def, H.smul_def, pushforwardModulesHAddEquiv_map, pushforward_map_modulesSMul]

/-- For a sheaf `A` killed by the ideal of the image of a closed embedding `f` with surjective
stalk maps, `Hᵠ(Y, A) ≃ Hᵠ(X, f^* A)`. -/
def Hom.HAddEquivOfSMulEqZero (hf : IsClosedEmbedding f.base)
    (hs : ∀ x, Function.Surjective (f.stalkMap x)) (A : SheafOfModules.{u} Y.ringSheaf)
    (hA : ∀ y, ∀ r ∈ f.pushforwardStalkIdeal y, ∀ m : (Y.stalkFunctor y).obj A, r • m = 0)
    (q : ℕ) : H A q ≃+ H (f.pullbackModules.obj A) q :=
  (TopCat.Sheaf.H.addEquivOfIso
    ((modulesToAb Y).mapIso (f.unitIsoOfSMulEqZero hf hs A hA)) q).trans
    (f.pushforwardModulesHAddEquiv hf _ q).symm

end Cohomology

end AlgebraicGeometry.LocallyRingedSpace

end
