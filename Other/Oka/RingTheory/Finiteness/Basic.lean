/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness of a module whose scalar ring is replaced by an isomorphic one

Material for `Mathlib/RingTheory/Finiteness/Basic.lean`; see `README.md` on the mirror tree.

`Module.Finite.of_ringEquiv` is the case of `Module.Finite.of_restrictScalars_finite` in which
the two scalar rings are isomorphic and **the carrier does not change**: one additive monoid `N`
carries a module structure over each of `A` and `B`, a ring isomorphism `e : A ≃+* B` identifies
the two actions, and finiteness transfers. Its proof is `of_restrictScalars_finite` at the algebra
structure `e` defines, and the whole content is that the `IsScalarTower` that lemma wants is the
hypothesis `a • n = e a • n` rewritten.

**It is not `Module.Finite.equiv`**, which moves along an isomorphism of *modules* over a fixed
ring. Here the module is one type with one addition and only the ring acting on it changes.

## Where this shape comes from

Every comparison of two spellings of the same sheaf-theoretic object: the sections of a sheaf of
modules over an open `U` of a scheme `X` are a `Γ(X, U)`-module, and after restricting along an
open immersion `f` the *same* type is a `Γ(V, U)`-module for the source `V`, with the two actions
matched by the isomorphism `f.appIso U` rather than by any map of carriers. See
`AlgebraicGeometry.Scheme.Modules.module_finite_sections_of_restrict`, which is the first consumer.

## Main results

- `Module.Finite.of_ringEquiv`
-/

@[expose] public section

namespace Module.Finite

/-- **Finiteness transfers along a ring isomorphism identifying two actions on one carrier.**

`N` is a module over both `A` and `B`, `e : A ≃+* B` is a ring isomorphism, and `he` says the
two actions agree along it. Then `B`-finiteness follows from `A`-finiteness.

Only `he` is used, and only through the `IsScalarTower` for the algebra structure `e` puts on
`B` over `A`; `Module.Finite.of_restrictScalars_finite` does the rest.

**`CommSemiring B` is a constraint of the route rather than of the statement.** Nothing in the
conclusion wants `B` commutative, and `Module.Finite.of_restrictScalars_finite` asks only for
`Semiring`; but `RingHom.toAlgebra`, which is how the algebra structure below is built, does ;
with `[Semiring B]` the `letI` fails with

```
Type mismatch: RingHom.toAlgebra ?m has type @Algebra ?A ?B ?_ CommSemiring.toSemiring
  but is expected to have type @Algebra A B _ _
```

so the weaker binder is rejected by the proof and not by the theorem. A different construction of
the algebra structure would presumably weaken it. -/
theorem of_ringEquiv {A B N : Type*} [CommSemiring A] [CommSemiring B] [AddCommMonoid N]
    [Module A N] [Module B N] (e : A ≃+* B) (he : ∀ (a : A) (n : N), a • n = e a • n)
    [Module.Finite A N] : Module.Finite B N := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  haveI : IsScalarTower A B N := ⟨fun a b n ↦ by
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [he a (b • n), mul_smul]⟩
  exact Module.Finite.of_restrictScalars_finite A B N

end Module.Finite
