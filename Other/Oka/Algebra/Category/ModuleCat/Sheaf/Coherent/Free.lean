/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Stability

/-!
# A finite free sheaf of modules over a coherent sheaf of rings is coherent

If the unit sheaf `𝒪` is coherent as a sheaf of modules over itself; for a ringed space, the
statement that the structure sheaf is coherent; then so is `𝒪^n` for every finite `n`. This is
the sheaf-theoretic form of "a coherent ring is a coherent module over itself in every finite
rank", and it is the step that lets a *presentation* by finite free sheaves be pushed through
the stability results of `Other/Oka/Algebra/Category/ModuleCat/Sheaf/Coherent/Stability.lean`:
`SheafOfModules.IsCoherent.cokernel` needs its target coherent, and for a presentation the
target is a finite free sheaf.

## The proof is an induction, and the step is the biproduct

`SheafOfModules.freeSumIso` (Mathlib) identifies `free (I ⊕ K)` with the coproduct of `free I`
and `free K`, which in an additive category is the biproduct, so `free (Option α)` is
`free α ⊞ free PUnit` and `free PUnit` is the unit (`SheafOfModules.freePUnitIso`). The induction
is then `Finite.induction_empty_option`, with `SheafOfModules.IsCoherent.biprod` as the step and
`SheafOfModules.isZero_free_of_isEmpty` as the base.

Note where the hypothesis enters: **only in the `Option` step, and only through
`free PUnit ≅ unit R`**. Nothing else in the induction knows what `R` is.

## Main results

- `SheafOfModules.IsCoherent.free`: **a finite free sheaf of modules over a coherent sheaf of
  rings is coherent.**
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] [HasPullbacks C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **Free sheaves of modules on equivalent index types are isomorphic**, `free` being a
functor of the index type. -/
noncomputable def freeCongr {I K : Type u} (e : I ≃ K) : free (R := R) I ≅ free (R := R) K :=
  (freeFunctor (R := R)).mapIso e.toIso

/-- **The free sheaf of modules on a sum of index types is the biproduct.**

`SheafOfModules.freeSumIso` says it is the coproduct; in an additive category the coproduct is
the biproduct, and the biproduct is the form the coherence argument consumes, because
restriction to `Over X` commutes with it (`SheafOfModules.overBiprodIso`). -/
noncomputable def freeSumBiprodIso (I K : Type u) :
    free (R := R) (I ⊕ K) ≅ free (R := R) I ⊞ free (R := R) K :=
  (freeSumIso I K).symm ≪≫ (biprod.isoCoprod _ _).symm

/-- **A finite free sheaf of modules over a coherent sheaf of rings is coherent.**

The hypothesis is that the sheaf of rings is coherent as a module over itself, which for the
structure sheaf of a complex analytic space is Oka's theorem
(`ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf`).

`SheafOfModules.free` is written out in full throughout the proof: declaring a lemma named
`IsCoherent.free` opens `SheafOfModules.IsCoherent` inside its own body, where `free` resolves
to the lemma being declared. The same trap is recorded on
`SheafOfModules.IsCoherent.cokernel`. -/
theorem IsCoherent.free [(unit R).IsCoherent] (I : Type u) [Finite I] :
    (free (R := R) I).IsCoherent := by
  have hequiv : ∀ {α β : Type u}, α ≃ β → (SheafOfModules.free (R := R) α).IsCoherent →
      (SheafOfModules.free (R := R) β).IsCoherent := by
    intro α β e h
    haveI := h
    exact IsCoherent.of_iso (M := SheafOfModules.free (R := R) α)
      (SheafOfModules.freeCongr (R := R) e)
  have hempty : (SheafOfModules.free (R := R) PEmpty.{u + 1}).IsCoherent := by
    constructor
    · exact inferInstance
    intro X K _ φ
    haveI : HasBinaryProducts (Over X) := Over.ConstructProducts.over_binaryProduct_of_pullback
    have hz : IsZero ((SheafOfModules.free (R := R) PEmpty.{u + 1}).over X) :=
      (SheafOfModules.isZero_free_of_isEmpty (R := R.over X) PEmpty.{u + 1}).of_iso
        (SheafOfModules.overFreeIso _ X).symm
    obtain rfl := hz.eq_zero_of_tgt φ
    exact IsFiniteType.of_iso (M := SheafOfModules.free (R := R.over X) K) kernelZeroIsoSource.symm
  have hoption : ∀ {α : Type u} [Fintype α],
      (SheafOfModules.free (R := R) α).IsCoherent →
        (SheafOfModules.free (R := R) (Option α)).IsCoherent := by
    intro α _ h
    haveI := h
    haveI : (SheafOfModules.free (R := R) PUnit.{u + 1}).IsCoherent :=
      IsCoherent.of_iso (M := SheafOfModules.unit R) (SheafOfModules.freePUnitIso (R := R)).symm
    haveI : (SheafOfModules.free (R := R) α ⊞
        SheafOfModules.free (R := R) PUnit.{u + 1}).IsFiniteType :=
      IsFiniteType.of_iso (M := SheafOfModules.free (R := R) (α ⊕ PUnit.{u + 1}))
        (SheafOfModules.freeSumBiprodIso _ _)
    haveI : (SheafOfModules.free (R := R) α ⊞
        SheafOfModules.free (R := R) PUnit.{u + 1}).IsCoherent := IsCoherent.biprod
    exact IsCoherent.of_iso
      (M := SheafOfModules.free (R := R) α ⊞ SheafOfModules.free (R := R) PUnit.{u + 1})
      ((SheafOfModules.freeSumBiprodIso _ _).symm ≪≫
        (SheafOfModules.freeCongr (R := R) (Equiv.optionEquivSumPUnit α)).symm)
  exact Finite.induction_empty_option (P := fun α ↦ (SheafOfModules.free (R := R) α).IsCoherent)
    hequiv hempty hoption I

omit [HasPullbacks C] [HasBinaryProducts C] in
/-- A free rank-one sheaf is coherent when the unit sheaf is coherent. -/
theorem IsCoherent.freePUnit [(unit R).IsCoherent] :
    SheafOfModules.IsCoherent.{u, u, u}
      (SheafOfModules.free (R := R) PUnit.{u + 1}) :=
  IsCoherent.of_iso (M := SheafOfModules.unit R)
    (SheafOfModules.freePUnitIso (R := R)).symm

end SheafOfModules
