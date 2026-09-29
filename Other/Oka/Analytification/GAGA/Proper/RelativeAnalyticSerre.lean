/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.Proper.GAGA2
public import Other.Oka.Analytification.GAGA.Proper.RelativeAnalyticSerreAcyclic

/-!
# The analytic relative Serre theorem and GAGA for proper schemes

We prove the analytic relative Serre theorem `ComplexAnalytic.RelativeAnalyticSerre`
(`ComplexAnalytic.relativeAnalyticSerre`): for morphisms `π : Y' ⟶ Y` and `j : Y' ⟶ ℙᴺ` of
schemes locally of finite type over `ℂ` such that `(π, j) : Y' ⟶ Y ×_ℂ ℙᴺ` is a closed immersion,
with `Y` quasi-compact, and coherent `G` on `Y'`, the analytification of `G(m)` is `π^an`-acyclic
and the base change morphism `(π_* G(m))^an ⟶ (π^an)_* G(m)^an` is an isomorphism for `m ≫ 0`.

Both statements are local on `Y`: they hold over each affine open `V ⊆ Y` for `m ≫ 0`
(`ComplexAnalytic.exists_bijective_bcStalk_twistAlong`,
`ComplexAnalytic.exists_HVanishesOn_twistAlong`), and finitely many affine opens cover `Y`.

Consequently GAGA-1 and GAGA-2 hold for proper schemes over `ℂ` (`ComplexAnalytic.gaga₁_proper`,
`ComplexAnalytic.gaga₂_proper`).
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite Topology

universe u

noncomputable section

namespace ComplexAnalytic

variable {Y : SchemeLFTℂ.{u}} {V : Y.obj.left.Opens} (hV : IsAffineOpen V)

lemma exists_affineSpecι_base_eq (y : analytification.obj Y)
    (hy : (analytificationπLRS Y).base y ∈ V) :
    ∃ v, (analytification.map (Y.affineSpecι hV)).toLRSHom.base v = y := by
  have h : y ∈ Set.range (analytification.map (Y.affineSpecι hV)).toLRSHom.base := by
    rw [range_analytification_map]
    change (analytificationπLRS Y).base y ∈ Set.range hV.fromSpec.base
    rw [hV.range_fromSpec]
    exact hy
  exact h

/-- **The analytic relative Serre theorem.** -/
theorem relativeAnalyticSerre : RelativeAnalyticSerre.{u} := by
  intro Y Y' π N j hY hι G hG
  haveI := hι
  have hloc : ∀ y : Y.obj.left, ∃ (V : Y.obj.left.Opens) (hV : IsAffineOpen V) (m₀ : ℤ), y ∈ V ∧
      ∀ m : ℤ, m₀ ≤ m →
        (∀ v, Function.Bijective (bcStalk π (twistAlong j G m)
          ((analytification.map (Y.affineSpecι hV)).toLRSHom.base v))) ∧
        ∀ (v : analytification.obj (Y.affineSpec hV)) (O : (analytification.obj Y).Opens),
          (analytification.map (Y.affineSpecι hV)).toLRSHom.base v ∈ O →
            ∃ V' ≤ O, (analytification.map (Y.affineSpecι hV)).toLRSHom.base v ∈ V' ∧
              HVanishesOn ((analytificationModules Y').obj (twistAlong j G m))
                ((Opens.map (analytification.map π).toLRSHom.base).obj V') := by
    intro y
    obtain ⟨V, hV, hyV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : Y.obj.left.Opens) from trivial)
    obtain ⟨m₁, h₁⟩ := exists_bijective_bcStalk_twistAlong π j G hV
    obtain ⟨m₂, h₂⟩ := exists_HVanishesOn_twistAlong π j G hV
    exact ⟨V, hV, max m₁ m₂, hyV, fun m hm ↦ ⟨h₁ m (le_of_max_le_left hm),
      h₂ m (le_of_max_le_right hm)⟩⟩
  choose V hV m₀ hyV hm₀ using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (V y : Set Y.obj.left))
    (fun y ↦ (V y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyV y⟩)
  refine ⟨∑ y ∈ t, |m₀ y|, fun m hm ↦ ?_⟩
  have hcov : ∀ y' : analytification.obj Y, ∃ y ∈ t, ∃ v,
      (analytification.map (Y.affineSpecι (hV y))).toLRSHom.base v = y' ∧ m₀ y ≤ m := by
    intro y'
    obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ ((analytificationπLRS Y).base y')))
    obtain ⟨v, hv⟩ := exists_affineSpecι_base_eq (hV y) y' hy
    exact ⟨y, hyt, v, hv, (le_abs_self _).trans
      ((Finset.single_le_sum (fun y _ ↦ abs_nonneg (m₀ y)) hyt).trans hm)⟩
  refine ⟨TopCat.Sheaf.isPushforwardAcyclic_of_forall_exists _ fun O y' hy' ↦ ?_,
    (isIso_analytificationPushforwardBaseChange_iff _ _).2 fun y' ↦ ?_⟩
  · obtain ⟨y, -, v, rfl, hmy⟩ := hcov y'
    exact ((hm₀ y m hmy).2 v O hy')
  · obtain ⟨y, -, v, rfl, hmy⟩ := hcov y'
    exact (hm₀ y m hmy).1 v

/-- **Serre's GAGA-1 for proper schemes**: for a proper scheme `X` over `ℂ` and a coherent sheaf
`F` on `X`, the comparison map `Hᵠ(X, F) → Hᵠ(X^an, F^an)` is bijective for all `q`. -/
theorem gaga₁_proper {X : SchemeLFTℂ.{u}} (hX : IsProperℂ X)
    (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent] (q : ℕ) :
    Function.Bijective (gagaMap X F q) :=
  gaga₁_of_isProperℂ hX relativeAnalyticSerre F q

/-- **Serre's GAGA-2 for proper schemes**: for a proper scheme `X` over `ℂ`, analytification is
fully faithful on coherent sheaves. -/
theorem gaga₂_proper {X : SchemeLFTℂ.{u}} (hX : IsProperℂ X)
    (F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent]
    [G.IsCoherent] :
    Function.Bijective ((analytificationModules X).map : (F ⟶ G) → _) :=
  gaga₂_of_isProperℂ hX relativeAnalyticSerre F G

end ComplexAnalytic

end
