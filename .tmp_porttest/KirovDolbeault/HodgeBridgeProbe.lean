module

public import KirovDolbeault.TraceResidue

@[expose] public noncomputable section

/-!
# Compatibility probe for the Hodge-conjecture residue detector

This scratch module records the smallest part of the vendored development that
is useful for detecting the explicit elliptic Cech representative.  It is kept
outside the production import graph while the bridge is evaluated.
-/

open Complex Metric

namespace Jacobians.Dolbeault

/-- Functions holomorphic on a punctured neighbourhood of `c` form a complex
submodule.  This is the natural domain on which the contour definition of
`resAt` is genuinely linear. -/
def puncturedHolomorphicSubmodule (c : ℂ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | HoloPunctured f c}
  zero_mem' := by
    refine ⟨1, by norm_num, ?_⟩
    intro z hz
    exact differentiableAt_const (c := (0 : ℂ))
  add_mem' := by
    rintro f g ⟨ρf, hρf, hf⟩ ⟨ρg, hρg, hg⟩
    refine ⟨min ρf ρg, lt_min hρf hρg, ?_⟩
    intro z hz
    exact (hf z ⟨mem_ball.mpr <| lt_of_lt_of_le (mem_ball.mp hz.1)
      (min_le_left _ _), hz.2⟩).add
      (hg z ⟨mem_ball.mpr <| lt_of_lt_of_le (mem_ball.mp hz.1)
        (min_le_right _ _), hz.2⟩)
  smul_mem' := by
    rintro a f ⟨ρ, hρ, hf⟩
    refine ⟨ρ, hρ, ?_⟩
    intro z hz
    exact (hf z hz).const_smul a

/-- The vendored contour residue, bundled as a complex-linear functional on
punctured-holomorphic functions. -/
def puncturedResidue (c : ℂ) :
    puncturedHolomorphicSubmodule c →ₗ[ℂ] ℂ where
  toFun f := resAt f.1 c
  map_add' f g := resAt_add f.2 g.2
  map_smul' a f := resAt_smul a f.2

/-- The local value needed by the elliptic representative: `-du/u` has
residue `-1` at the origin. -/
theorem puncturedResidue_neg_inv :
    resAt (fun z : ℂ => -(z⁻¹)) 0 = -1 := by
  have h := resAt_const_mul_sub_inv (-1 : ℂ) 0
  simpa using h

/-- A coefficient extending holomorphically across the centre contributes no
residue. -/
theorem puncturedResidue_eq_zero_of_analyticAt {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) : resAt f c = 0 :=
  Jacobians.TraceResidue.resAt_eq_zero_of_analyticAt hf

end Jacobians.Dolbeault
