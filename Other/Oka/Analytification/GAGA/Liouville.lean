/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Analysis.Complex.Liouville
public import Other.Oka.AnalyticSpace.Evaluation

/-!
# Liouville's theorem for global sections on `ℂⁿ`

A global section of the structure sheaf of `ℂⁿ` is a holomorphic function on `ℂⁿ`; if its values
form a bounded set, it is the constant section with its value at any point
(`ComplexAnalytic.AnalyticSpace.complexAffineSpace_eq_algebraMap_of_bounded`). This is Mathlib's
`Differentiable.apply_eq_apply_of_bounded`, read through `ComplexAnalytic.eval_complexAffineSpace`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace ComplexAnalytic

namespace AnalyticSpace

variable {n : ℕ}

/-- The value of a global section of `𝒪_{ℂⁿ}` at `z` is the value at `z` of the extension by zero
of the underlying holomorphic function. -/
lemma eval_complexAffineSpace_eq_toGlobalFun
    (s : (AnalyticSpace.complexAffineSpace.{u} n).presheaf.obj (op ⊤))
    (z : AnalyticSpace.complexAffineSpace.{u} n) :
    (AnalyticSpace.complexAffineSpace.{u} n).eval (U := ⊤) z trivial s =
      OkaRing.toGlobalFun (⊤ : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ)) s z :=
  (eval_complexAffineSpace z s).trans (OkaRing.toGlobalFun_apply (U := ⊤) s trivial).symm

/-- A global section of `𝒪_{ℂⁿ}` is, after extension by zero, a differentiable function on
`ℂⁿ`. -/
lemma differentiable_toGlobalFun
    (s : (AnalyticSpace.complexAffineSpace.{u} n).presheaf.obj (op ⊤)) :
    Differentiable ℂ
      (OkaRing.toGlobalFun (⊤ : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ)) s) := fun x ↦
  ((okaAnalytic_iff (U := (⊤ : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ))) _).1
    (show OkaAnalytic _ from s.2) x trivial).differentiableAt

/-- **Liouville's theorem on `ℂⁿ`**: a global section of `𝒪_{ℂⁿ}` with bounded values is the
constant section with its value at any point `z₀`. -/
theorem complexAffineSpace_eq_algebraMap_of_bounded
    (s : (AnalyticSpace.complexAffineSpace.{u} n).presheaf.obj (op ⊤))
    (hs : Bornology.IsBounded (Set.range fun z : AnalyticSpace.complexAffineSpace.{u} n ↦
      (AnalyticSpace.complexAffineSpace.{u} n).eval (U := ⊤) z trivial s))
    (z₀ : AnalyticSpace.complexAffineSpace.{u} n) :
    s = (AnalyticSpace.complexAffineSpace.{u} n).algebraMap
      ((AnalyticSpace.complexAffineSpace.{u} n).eval (U := ⊤) z₀ trivial s) := by
  set f := OkaRing.toGlobalFun (⊤ : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ)) s
  have hfe : ∀ z, (AnalyticSpace.complexAffineSpace.{u} n).eval (U := ⊤) z trivial s = f z :=
    eval_complexAffineSpace_eq_toGlobalFun s
  have hb : Bornology.IsBounded (Set.range f) := by
    have : (Set.range fun z : AnalyticSpace.complexAffineSpace.{u} n ↦
        (AnalyticSpace.complexAffineSpace.{u} n).eval (U := ⊤) z trivial s) = Set.range f :=
      congrArg Set.range (funext hfe)
    exact this ▸ hs
  have hconst := (differentiable_toGlobalFun s).apply_eq_apply_of_bounded hb
  rw [hfe z₀]
  refine OkaRing.ext (funext fun p ↦ ?_)
  exact (OkaRing.toGlobalFun_apply (U := ⊤) s (x := p.1) trivial).symm.trans (hconst p.1 z₀)

/-- A global section of `𝒪_{ℂⁿ}` all of whose values vanish is zero. -/
theorem complexAffineSpace_eq_zero_of_eval_eq_zero
    (s : (AnalyticSpace.complexAffineSpace.{u} n).presheaf.obj (op ⊤))
    (hs : ∀ z : AnalyticSpace.complexAffineSpace.{u} n,
      (AnalyticSpace.complexAffineSpace.{u} n).eval (U := ⊤) z trivial s = 0) : s = 0 := by
  refine OkaRing.ext (funext fun p ↦ ?_)
  exact (OkaRing.toGlobalFun_apply (U := ⊤) s (x := p.1) trivial).symm.trans
    ((eval_complexAffineSpace_eq_toGlobalFun s p.1).symm.trans (hs p.1))

end AnalyticSpace

end ComplexAnalytic

end
