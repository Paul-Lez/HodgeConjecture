/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.SupportRelativeCohomologySheaf

/-!
# Detecting nonzero support-relative cohomology germs

Sheafification preserves stalks, so a relative cohomology class has zero germ precisely
when its restriction to some smaller neighborhood is zero.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite TopCat.Presheaf

namespace AlgebraicTopology.Singular

variable (X : TopCat.{0}) (S : Set X) (n : ℕ)

set_option backward.isDefEq.respectTransparency false in
/-- A sheafified germ vanishes exactly when an actual neighborhood restriction vanishes. -/
theorem supportRelativeCohomologyGerm_eq_zero_iff
    (U : Opens X) (x : X) (hx : x ∈ U)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (U : Set X) S) n) :
    supportRelativeCohomologyGerm X S n U x hx a = 0 ↔
      ∃ (W : Opens X) (hWU : W ≤ U), x ∈ W ∧
        relativeCohomologyMap ℚ n
          (neighborhoodSupportInclusionPairMap
            (W := (W : Set X)) (V := (U : Set X)) hWU S) a = 0 := by
  constructor
  · intro h
    let F := supportRelativeCohomologyPresheaf X S n
    let f := (stalkFunctor AddCommGrpCat x).map (supportRelativeCohomologyToSheaf X S n)
    have : IsIso f := stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat F
    have hg : F.germ U x hx a = F.germ U x hx 0 := by
      apply (ConcreteCategory.bijective_of_isIso f).1
      simpa only [f, F, stalkFunctor_map_germ_apply, map_zero,
        supportRelativeCohomologyGerm] using h
    obtain ⟨W, hxW, iU, _, he⟩ := F.germ_eq x hx hx a 0 hg
    refine ⟨W, leOfHom iU, hxW, ?_⟩
    change (supportRelativeCohomologyPresheaf X S n).map
      (homOfLE (leOfHom iU)).op a = 0
    simpa only [F, show iU = homOfLE (leOfHom iU) from Subsingleton.elim _ _,
      map_zero] using he
  · rintro ⟨W, hWU, hxW, he⟩
    rw [← supportRelativeCohomologyGerm_restrict X S n hWU x hxW, he]
    simp only [supportRelativeCohomologyGerm, map_zero]

/-- A class that stays nonzero on every smaller neighborhood has nonzero sheaf germ. -/
theorem supportRelativeCohomologyGerm_ne_zero_of_restrict_ne_zero
    (U : Opens X) (x : X) (hx : x ∈ U)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (U : Set X) S) n)
    (h : ∀ (W : Opens X) (hWU : W ≤ U), x ∈ W →
      relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap
          (W := (W : Set X)) (V := (U : Set X)) hWU S) a ≠ 0) :
    supportRelativeCohomologyGerm X S n U x hx a ≠ 0 := by
  intro hz
  obtain ⟨W, hWU, hxW, he⟩ :=
    (supportRelativeCohomologyGerm_eq_zero_iff X S n U x hx a).mp hz
  exact h W hWU hxW he

end AlgebraicTopology.Singular
