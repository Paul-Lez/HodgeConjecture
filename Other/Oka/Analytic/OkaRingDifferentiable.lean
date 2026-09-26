/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Other.Oka.StructureSheaf

/-!
# Holomorphic functions on open subsets of `ℂⁿ` are complex differentiable

`OkaRing.differentiableOn_toGlobalFun`: the extension by zero of an element of `OkaRing U` is
complex differentiable on `U`. This is the bridge from `OkaRing` to the `DifferentiableOn`
vocabulary of Mathlib's complex analysis.
-/

@[expose] public section

open TopologicalSpace

variable {ι : Type*} [Fintype ι]

/-- Elements of `OkaRing U` are holomorphic on `U`. -/
lemma OkaRing.differentiableOn_toGlobalFun {U : Opens (ι → ℂ)} (f : OkaRing U) :
    DifferentiableOn ℂ (f.toGlobalFun _) U := fun x hx ↦
  ((okaAnalytic_iff _).1 f.2 x hx).differentiableAt.differentiableWithinAt

end
