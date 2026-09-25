/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.InvertibleSheafRationalSection

/-!
# The coefficient of a section with respect to a generating section

If `g : Γ(L, U)` generates the sheaf of modules `L` on the open `U`
(`AlgebraicGeometry.Scheme.Modules.Generates`), then every section `t : Γ(L, W)` of `L` over an
arbitrary open `W` has a unique *coefficient* `hg.coeff W t : Γ(S, W ⊓ U)` characterised by

```
hg.coeff W t • g|_{W ⊓ U} = t|_{W ⊓ U}.
```

This file records the coefficient and the four identities that make it a morphism of sheaves of
modules from `L` to the sheaf `W ↦ Γ(S, W ⊓ U)`: `coeff_res` (compatibility with restriction),
`coeff_smul` (semilinearity), `coeff_add` (additivity) and `coeff_self` (`hg.coeff U g = 1`).
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}} {L : S.Modules} {U : S.Opens} {g : Γ(L, U)}

/-- The coefficient of a section of `L` with respect to a generating section `g`. -/
def Generates.coeff (hg : Generates g) (W : S.Opens) (t : Γ(L, W)) : Γ(S, W ⊓ U) :=
  (Equiv.ofBijective _ (hg (W ⊓ U) inf_le_right)).symm (resSection L inf_le_left t)

lemma Generates.coeff_smul_eq (hg : Generates g) (W : S.Opens) (t : Γ(L, W)) :
    hg.coeff W t • resSection L inf_le_right g = resSection L inf_le_left t :=
  (Equiv.ofBijective _ (hg (W ⊓ U) inf_le_right)).apply_symm_apply _

lemma Generates.coeff_eq (hg : Generates g) (W : S.Opens) (t : Γ(L, W))
    (c : Γ(S, W ⊓ U)) (hc : c • resSection L inf_le_right g = resSection L inf_le_left t) :
    c = hg.coeff W t :=
  (hg (W ⊓ U) inf_le_right).injective (by
    show c • resSection L inf_le_right g = hg.coeff W t • resSection L inf_le_right g
    rw [hc, hg.coeff_smul_eq])

lemma Generates.coeff_self (hg : Generates g) : hg.coeff U g = 1 := by
  refine (hg.coeff_eq U g 1 ?_).symm
  rw [one_smul]

lemma Generates.coeff_res (hg : Generates g) {W W' : S.Opens} (h : W' ≤ W) (t : Γ(L, W)) :
    hg.coeff W' (resSection L h t) =
      S.presheaf.map (homOfLE (inf_le_inf_right U h)).op (hg.coeff W t) := by
  refine (hg.coeff_eq W' _ _ ?_).symm
  have h2 := congrArg (Scheme.Modules.resSection L (inf_le_inf_right U h)) (hg.coeff_smul_eq W t)
  rw [resSection_smul] at h2
  simp only [resSection_resSection] at h2 ⊢
  exact h2

lemma Generates.coeff_smul (hg : Generates g) (W : S.Opens) (r : Γ(S, W)) (t : Γ(L, W)) :
    hg.coeff W (r • t) =
      S.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op r • hg.coeff W t := by
  refine (hg.coeff_eq W _ _ ?_).symm
  rw [smul_eq_mul, mul_smul, hg.coeff_smul_eq, ← resSection_smul]

lemma Generates.coeff_add (hg : Generates g) (W : S.Opens) (t t' : Γ(L, W)) :
    hg.coeff W (t + t') = hg.coeff W t + hg.coeff W t' := by
  refine (hg.coeff_eq W _ _ ?_).symm
  rw [add_smul, hg.coeff_smul_eq, hg.coeff_smul_eq]
  simp

end AlgebraicGeometry.Scheme.Modules
