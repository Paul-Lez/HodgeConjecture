/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.RingTheory.Filtration
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesStalkKernel
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesStalkNakayama

/-!
# A uniform Artin–Rees bound on a compact locally ringed space

Let `Y` be a compact locally ringed space with noetherian stalks, `ψ : M ⟶ B` a morphism of
coherent sheaves and `I_y ⊆ 𝒪_{Y,y}` ideals such that `I_yᴺ` kills `(ker ψ)_y` for all `y`.
Suppose the submodules `I_yⁿ M_y` are the stalkwise kernels of morphisms `ηₙ : M ⟶ Pₙ` to
coherent sheaves. Then `I_yⁿ M_y ∩ ker ψ_y = 0` for all `y` and all `n ≫ 0`
(`AlgebraicGeometry.LocallyRingedSpace.exists_forall_pow_smul_top_inf_ker_eq_bot`).

At a single point this is the Artin–Rees lemma (`Ideal.exists_pow_inf_eq_pow_smul`). The
condition at `y` is the vanishing of the stalk at `y` of the coherent sheaf
`ker (ker ψ ⟶ M ⟶ Pₙ)`, so it spreads to a neighbourhood, and compactness gives a uniform bound.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace

variable {Y : LocallyRingedSpace.{u}} {M B : SheafOfModules.{u} Y.ringSheaf} (ψ : M ⟶ B)
  {P : ℕ → SheafOfModules.{u} Y.ringSheaf} (η : ∀ n, M ⟶ P n)
  (I : ∀ y : Y, Ideal (Y.presheaf.stalk y))

/-- The stalk of `ker (ker ψ ⟶ M ⟶ P)` vanishes at `y` if and only if the kernels of `ψ` and of
`M ⟶ P` meet trivially at `y`. -/
lemma subsingleton_stalk_kernel_comp_iff {P : SheafOfModules.{u} Y.ringSheaf} (η : M ⟶ P)
    (y : Y) :
    Subsingleton ((Y.stalkFunctor y).obj (kernel (kernel.ι ψ ≫ η))) ↔
      LinearMap.ker ((Y.stalkFunctor y).map η).hom ⊓ LinearMap.ker ((Y.stalkFunctor y).map ψ).hom
        = ⊥ := by
  constructor
  · intro hsub
    refine eq_bot_iff.2 fun m ⟨hm₁, hm₂⟩ ↦ ?_
    obtain ⟨c, rfl⟩ := exists_stalkFunctor_map_kernelι_eq ψ y m hm₂
    obtain ⟨l, rfl⟩ := exists_stalkFunctor_map_kernelι_eq (kernel.ι ψ ≫ η) y c (by
      rw [Functor.map_comp, ConcreteCategory.comp_apply]
      exact hm₁)
    rw [Submodule.mem_bot, Subsingleton.elim l 0]
    simp
  · intro h
    refine ⟨fun a b ↦ ?_⟩
    have h0 : ∀ l : (Y.stalkFunctor y).obj (kernel (kernel.ι ψ ≫ η)), l = 0 := by
      intro l
      have e : (Y.stalkFunctor y).map (kernel.ι (kernel.ι ψ ≫ η) ≫ kernel.ι ψ) l =
          (Y.stalkFunctor y).map (kernel.ι ψ)
            ((Y.stalkFunctor y).map (kernel.ι (kernel.ι ψ ≫ η)) l) :=
        congrArg (fun φ : (Y.stalkFunctor y).obj (kernel (kernel.ι ψ ≫ η)) ⟶
            (Y.stalkFunctor y).obj M ↦ φ l)
          ((Y.stalkFunctor y).map_comp (kernel.ι (kernel.ι ψ ≫ η)) (kernel.ι ψ))
      have h1 := (congrArg ((Y.stalkFunctor y).map η) e).symm.trans
        (stalkFunctor_map_map_eq_zero (kernel.ι (kernel.ι ψ ≫ η) ≫ kernel.ι ψ) η
          ((Category.assoc _ _ _).trans (kernel.condition _)) y l)
      have h2 := stalkFunctor_map_map_eq_zero _ _ (kernel.condition ψ) y
        ((Y.stalkFunctor y).map (kernel.ι (kernel.ι ψ ≫ η)) l)
      have h3 := (eq_bot_iff.1 h) ⟨h1, h2⟩
      rw [Submodule.mem_bot] at h3
      refine injective_stalk_of_mono (kernel.ι _) y (injective_stalk_of_mono (kernel.ι ψ) y ?_)
      exact h3.trans ((congrArg _ (map_zero _)).trans (map_zero _)).symm
    rw [h0 a, h0 b]

/-- **Uniform Artin–Rees.** On a compact locally ringed space with noetherian stalks, if `I_yᴺ`
kills the stalks of `ker ψ` and `I_yⁿ M_y` is the kernel of the stalk of `ηₙ : M ⟶ Pₙ` for
coherent `Pₙ`, then `I_yⁿ M_y ∩ ker ψ_y = 0` for all `y` and all large `n`. -/
theorem exists_forall_pow_smul_top_inf_ker_eq_bot [CompactSpace Y]
    [∀ y : Y, IsNoetherianRing (Y.presheaf.stalk y)] [M.IsCoherent] [B.IsCoherent]
    [∀ n, (P n).IsCoherent]
    (hη : ∀ n y m, (Y.stalkFunctor y).map (η n) m = 0 ↔
      m ∈ I y ^ n • (⊤ : Submodule (Y.presheaf.stalk y) ((Y.stalkFunctor y).obj M)))
    (N : ℕ) (hN : ∀ y, I y ^ N ≤
      Module.annihilator (Y.presheaf.stalk y) ((Y.stalkFunctor y).obj (kernel ψ))) :
    ∃ k, ∀ n ≥ k, ∀ y, I y ^ n • ⊤ ⊓ LinearMap.ker ((Y.stalkFunctor y).map ψ).hom = ⊥ := by
  classical
  haveI : (kernel ψ).IsCoherent := SheafOfModules.IsCoherent.kernel ψ
  have hker : ∀ n y, LinearMap.ker ((Y.stalkFunctor y).map (η n)).hom = I y ^ n • ⊤ :=
    fun n y ↦ Submodule.ext fun m ↦ hη n y m
  have hKN : ∀ y, I y ^ N • LinearMap.ker ((Y.stalkFunctor y).map ψ).hom = ⊥ := by
    intro y
    refine eq_bot_iff.2 (Submodule.smul_le.2 fun a ha m hm ↦ ?_)
    obtain ⟨c, rfl⟩ := exists_stalkFunctor_map_kernelι_eq ψ y m hm
    rw [Submodule.mem_bot, ← map_smul, Module.mem_annihilator.1 (hN y ha) c, map_zero]
  have hAR : ∀ y, ∃ n₀, ∀ n ≥ n₀,
      I y ^ n • ⊤ ⊓ LinearMap.ker ((Y.stalkFunctor y).map ψ).hom = ⊥ := by
    intro y
    haveI := SheafOfModules.IsCoherent.isFiniteType M
    haveI := finite_stalk_of_isFiniteType M y
    obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (I y)
      (LinearMap.ker ((Y.stalkFunctor y).map ψ).hom)
    refine ⟨c + N, fun n hn ↦ ?_⟩
    rw [hc n (by omega), eq_bot_iff, ← hKN y]
    exact Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) inf_le_right
  have hloc : ∀ y, ∃ U : Opens Y, y ∈ U ∧ ∃ n₀, ∀ z ∈ U, ∀ n ≥ n₀,
      I z ^ n • ⊤ ⊓ LinearMap.ker ((Y.stalkFunctor z).map ψ).hom = ⊥ := by
    intro y
    obtain ⟨n₀, hn₀⟩ := hAR y
    haveI : (kernel (kernel.ι ψ ≫ η n₀)).IsCoherent := SheafOfModules.IsCoherent.kernel _
    haveI := SheafOfModules.IsCoherent.isFiniteType (kernel (kernel.ι ψ ≫ η n₀))
    obtain ⟨U, hyU, hU⟩ := exists_nhds_subsingleton_stalk (kernel (kernel.ι ψ ≫ η n₀)) y
      ((subsingleton_stalk_kernel_comp_iff ψ (η n₀) y).2 (by rw [hker]; exact hn₀ n₀ le_rfl))
    refine ⟨U, hyU, n₀, fun z hz n hn ↦ ?_⟩
    have h := (subsingleton_stalk_kernel_comp_iff ψ (η n₀) z).1 (hU z hz)
    rw [hker] at h
    rw [eq_bot_iff, ← h]
    exact inf_le_inf_right _ (Submodule.smul_mono_left (Ideal.pow_le_pow_right hn))
  choose U hyU n₀ hn₀ using hloc
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (U y : Set Y))
    (fun y ↦ (U y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyU y⟩)
  refine ⟨s.sup n₀, fun n hn y ↦ ?_⟩
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
  exact hn₀ z y hyz n ((Finset.le_sup hz).trans hn)

end AlgebraicGeometry.LocallyRingedSpace

end
