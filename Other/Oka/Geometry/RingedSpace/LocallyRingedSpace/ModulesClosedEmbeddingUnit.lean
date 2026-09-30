/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesClosedEmbeddingKilled
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesStalkSurjective

/-!
# The unit `A ⟶ f_* f^* A` along a closed embedding

Let `f : X ⟶ Y` be a morphism of locally ringed spaces whose underlying map is a closed embedding
and whose stalk maps are surjective, and let `I_y = f.pushforwardStalkIdeal y` be the stalk at `y`
of the ideal of the image. For a sheaf of `𝒪_Y`-modules `A`, the unit `η : A ⟶ f_* f^* A` is
stalkwise the quotient map `A_y → A_y / I_y A_y`. We record:

- `AlgebraicGeometry.LocallyRingedSpace.Hom.epi_pullbackModulesAdj_unit_app`: `η` is an
  epimorphism;
- `AlgebraicGeometry.LocallyRingedSpace.Hom.mem_smul_top_of_stalkFunctor_map_unit_eq_zero`: the
  kernel of `η` on stalks at `y` is contained in `I_y • A_y`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Limits Topology

universe u

noncomputable section

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
  (M : ModuleCat.{u} R)

include hf in
/-- For a surjective ring map `f : R → S`, the kernel of `M → S ⊗_R M`, `m ↦ 1 ⊗ m` is contained
in `(ker f) • M`. -/
lemma mem_smul_top_of_extendRestrictScalarsAdj_unit_app_eq_zero (m : M)
    (hm : (extendRestrictScalarsAdj f).unit.app M m = 0) :
    m ∈ RingHom.ker f • (⊤ : Submodule R M) := by
  let N : Submodule R M := RingHom.ker f • ⊤
  let Q : ModuleCat.{u} R := ModuleCat.of R (M ⧸ N)
  let π : M ⟶ Q := ModuleCat.ofHom N.mkQ
  have hQ : ∀ r ∈ RingHom.ker f, ∀ q : Q, r • q = 0 := by
    intro r hr q
    obtain ⟨m, rfl⟩ := N.mkQ_surjective q
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  have hb := bijective_extendRestrictScalarsAdj_unit_app_of_surjective f hf Q hQ
  have hnat := ConcreteCategory.congr_hom ((extendRestrictScalarsAdj f).unit.naturality π) m
  have h0 : π m = 0 := by
    refine hb.1 (?_ : _ = (extendRestrictScalarsAdj f).unit.app Q 0)
    rw [map_zero]
    refine hnat.trans ?_
    rw [ConcreteCategory.comp_apply, hm, map_zero]
  exact (Submodule.Quotient.mk_eq_zero N).1 h0

end ModuleCat

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)

/-- Under `(f_* f^* A)_{f x} ≅ (f^* A)_x ≅ 𝒪_{X,x} ⊗ A_{f x}`, the stalk at `f x` of the unit
`A ⟶ f_* f^* A` is `a ↦ 1 ⊗ a`. -/
lemma Hom.pullbackModulesStalkIso_stalkPushforwardModules_unit
    (A : SheafOfModules.{u} Y.ringSheaf) (x : X) (a : (Y.stalkFunctor (f.base x)).obj A) :
    (f.pullbackModulesStalkIso x).hom.app A (f.stalkPushforwardModules (f.pullbackModules.obj A) x
      ((Y.stalkFunctor (f.base x)).map (f.pullbackModulesAdj.unit.app A) a)) =
    (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app _ a := by
  obtain ⟨U, hU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq A.val.presheaf a
  erw [PresheafOfModules.stalkFunctor_map_germ]
  have h1 := f.stalkPushforwardModules_germ (f.pullbackModules.obj A) x U hU
    ((f.pullbackModulesAdj.unit.app A).val.app (op U) t)
  exact (congrArg ((f.pullbackModulesStalkIso x).hom.app A) h1).trans
    (f.pullbackModulesStalkIso_hom_app_germ_unit A U x hU t)

variable (hf : IsClosedEmbedding f.base) (hs : ∀ x, Function.Surjective (f.stalkMap x))
  (A : SheafOfModules.{u} Y.ringSheaf)

include hf hs in
/-- For `f` a closed embedding with surjective stalk maps, the unit `A ⟶ f_* f^* A` is an
epimorphism. -/
theorem Hom.epi_pullbackModulesAdj_unit_app : Epi (f.pullbackModulesAdj.unit.app A) := by
  refine epi_of_forall_surjective_stalk _ fun y ↦ ?_
  by_cases hy : y ∈ Set.range f.base
  · obtain ⟨x, rfl⟩ := hy
    let e := (f.pullbackModulesStalkIso x).hom.app A
    have he : Function.Bijective e := (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
    have hes := he.comp (f.bijective_stalkPushforwardModules hf.isInducing
      (f.pullbackModules.obj A) x)
    intro t
    obtain ⟨a, ha⟩ := ModuleCat.surjective_extendRestrictScalarsAdj_unit_app_of_surjective _
      (hs x) _ (e (f.stalkPushforwardModules _ x t))
    exact ⟨a, hes.1 ((f.pullbackModulesStalkIso_stalkPushforwardModules_unit A x a).trans ha)⟩
  · have h2 := f.subsingleton_stalk_pushforward hf.isClosed_range y hy (f.pullbackModules.obj A)
    exact fun t ↦ ⟨0, @Subsingleton.elim _ h2 _ _⟩

include hf hs in
/-- For `f` a closed embedding with surjective stalk maps, an element of `A_y` killed by the unit
`A ⟶ f_* f^* A` lies in `I_y • A_y`, where `I_y = f.pushforwardStalkIdeal y`. -/
theorem Hom.mem_smul_top_of_stalkFunctor_map_unit_eq_zero (y : Y)
    (m : (Y.stalkFunctor y).obj A)
    (hm : (Y.stalkFunctor y).map (f.pullbackModulesAdj.unit.app A) m = 0) :
    m ∈ f.pushforwardStalkIdeal y •
      (⊤ : Submodule (Y.presheaf.stalk y) ((Y.stalkFunctor y).obj A)) := by
  by_cases hy : y ∈ Set.range f.base
  · obtain ⟨x, rfl⟩ := hy
    rw [f.pushforwardStalkIdeal_eq_ker hf.isInducing x]
    refine ModuleCat.mem_smul_top_of_extendRestrictScalarsAdj_unit_app_eq_zero _ (hs x) _ m ?_
    refine (f.pullbackModulesStalkIso_stalkPushforwardModules_unit A x m).symm.trans ?_
    have h0 : f.stalkPushforwardModules (f.pullbackModules.obj A) x 0 = 0 :=
      map_zero (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.base
        (f.pullbackModules.obj A).val.presheaf x).hom
    rw [hm]
    exact (congrArg _ h0).trans (map_zero _)
  · rw [f.pushforwardStalkIdeal_eq_top hf.isClosed_range y hy, Submodule.top_smul]
    exact Submodule.mem_top

end AlgebraicGeometry.LocallyRingedSpace

end
