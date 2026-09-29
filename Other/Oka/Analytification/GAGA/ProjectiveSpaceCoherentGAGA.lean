/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.DescendingInduction
public import Other.Oka.Analytification.GAGA.ProjectiveSpaceTwistGAGA
public import Other.Oka.Analytification.GAGA.ProjectiveSpaceVanishing
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.TheoremA

/-!
# GAGA for coherent sheaves on `ℙⁿ`

For every coherent sheaf `F` on `ℙⁿ = ℙⁿ_ℂ` and every `q`, the comparison map
`Hᵠ(ℙⁿ, F) → Hᵠ(ℙⁿ_an, F^an)` is bijective (`ComplexAnalytic.gaga_projectiveSpace`).

The proof is Serre's descending induction (`ComplexAnalytic.gagaMap_bijective_of_descending`)
for the class of coherent sheaves and `N = n`:
* both `Hᵠ(ℙⁿ, F)` and `Hᵠ(ℙⁿ_an, F^an)` vanish for `q > n`;
* by Theorem A, `F` is a quotient `0 → K → ⊕_I O(-m) → F → 0` with `K` coherent, and the
  comparison map is bijective on `⊕_I O(-m)` by GAGA for `O(-m)` and additivity.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic

/-- **GAGA for coherent sheaves on `ℙⁿ`**: for coherent `F` on `ℙⁿ_ℂ`, the comparison map
`Hᵠ(ℙⁿ, F) → Hᵠ(ℙⁿ_an, F^an)` is bijective for all `q`. -/
theorem gaga_projectiveSpace (n : ℕ)
    (F : SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf)
    [F.IsCoherent] (q : ℕ) :
    Function.Bijective (gagaMap (projectiveSpace.{u} n) F q) := by
  refine gagaMap_bijective_of_descending (X := projectiveSpace.{u} n) n
    (fun G ↦ G.IsCoherent) ?_ ?_ F inferInstance q
  · intro G hG q hq
    refine ⟨⟨fun a b ↦ ?_⟩, projectiveSpaceAn.subsingleton_H_analytificationModules_of_lt G q hq⟩
    exact (ProjectiveSpace.locallyRingedSpaceH_complex_eq_zero_of_le_of_isCoherent (hF := hG)
      G q hq a).trans (ProjectiveSpace.locallyRingedSpaceH_complex_eq_zero_of_le_of_isCoherent
        (hF := hG) G q hq b).symm
  · intro G hG
    obtain ⟨m₀, h⟩ := @ProjectiveSpace.exists_epi_twist_free_isCoherent_kernel n (ULift.{u} ℂ) _
      G inferInstance hG
    obtain ⟨I, hI, π, hπ, -, hK⟩ := h m₀ le_rfl
    refine ⟨ShortComplex.mk (C := SheafOfModules.{u}
        (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf)
      (kernel.ι π) π (kernel.condition π), ?_, hK, ⟨Iso.refl _⟩, fun q ↦ ?_⟩
    · have : Mono (kernel.ι π) := inferInstance
      exact @ShortComplex.ShortExact.mk _ _ _ _
        (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π)) this hπ
    · exact (gagaMap_bijective_iff_of_iso (ProjectiveSpace.twistFreeIso I _).symm q).1
        (gagaMap_bijective_sigma _ q fun _ ↦ bijective_gagaMap_twistingSheaf n _ q)

end ComplexAnalytic

end
