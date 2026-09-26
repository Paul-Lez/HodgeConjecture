/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace

/-!
# Missing general lemmas on the `Γ`-`Spec` adjunction

Material for `Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean`; see `README.md` on the mirror
tree. Nothing here is complex-analytic.

Mathlib packages the naturality of `AlgebraicGeometry.LocallyRingedSpace.toΓSpec` inside the
natural transformation `AlgebraicGeometry.identityToΓSpec`, whose components are the `toΓSpec`
maps. Reading naturality off it means unfolding `Γ.rightOp` and `Spec.toLocallyRingedSpace`,
which is exactly the step a caller does not want to repeat, so the square is restated here in
the vocabulary of `toΓSpec` and `Spec.locallyRingedSpaceMap`.

It also records the `Γ`-`Spec` adjunction in the form a caller carrying an *algebra structure*
wants. An `R`-algebra structure on a locally ringed space `X` is a ring map
`α : R →+* Γ(X, 𝒪_X)`, and the adjunction says such a thing is the same as a morphism
`X ⟶ Spec R`. Mathlib's `AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction` says so with the
ring on the opposite side and wrapped in `CommRingCat.ofHom`;
`AlgebraicGeometry.LocallyRingedSpace.toSpecOfAlgMap` is the same map with `α` as an ordinary
`RingHom`, together with the two facts that make it usable ; that it turns
`AlgebraicGeometry.LocallyRingedSpace.comapAlgMap` into precomposition, and that it is a
bijection.

**Why that is worth naming.** It is what lets a family of algebra structures on the members of an
open cover be glued: as morphisms to `Spec R` they glue by
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.existsUnique_glueMorphisms`, and the glued
morphism is a structure on the whole space. Without it, gluing the structures means gluing
sections one constant at a time and checking the ring axioms of the result by hand.

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.toSpecOfAlgMap`: an `R`-algebra structure on `X`, as a
  morphism `X ⟶ Spec R`.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.toΓSpec_naturality`: the canonical map to the spectrum
  of the global sections is natural.
- `AlgebraicGeometry.LocallyRingedSpace.comp_toSpecOfAlgMap`: pulling an algebra structure back
  along a morphism is precomposing the corresponding map to `Spec R` with it.
- `AlgebraicGeometry.LocallyRingedSpace.toSpecOfAlgMap_injective` and
  `AlgebraicGeometry.LocallyRingedSpace.exists_toSpecOfAlgMap_eq`: the correspondence is a
  bijection.
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

/-- **The canonical map to the spectrum of the global sections is natural.**

This is `AlgebraicGeometry.identityToΓSpec.naturality` with both functors evaluated, so that the
statement mentions only `toΓSpec` and `Spec.locallyRingedSpaceMap`. The two sides are
definitionally equal to the components of that naturality square; nothing is proved here beyond
the change of spelling. -/
theorem toΓSpec_naturality {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    f ≫ Y.toΓSpec = X.toΓSpec ≫ Spec.locallyRingedSpaceMap (Γ.map f.op) :=
  identityToΓSpec.naturality f

section AlgMap

variable {R : Type u} [CommRing R] {X Y : LocallyRingedSpace.{u}}

/-- **An `R`-algebra structure on `X`, as a morphism `X ⟶ Spec R`.**

This is the image of `α` under `AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction`'s hom
equivalence ; `toSpecOfAlgMap_eq_homEquiv` says so, by `rfl` ; restated so that the argument is a
`RingHom` rather than a morphism of `CommRingCat` in the opposite category. The restatement is
what makes the two lemmas below expressible without unfolding `Γ.rightOp` at every use. -/
noncomputable def toSpecOfAlgMap (X : LocallyRingedSpace.{u}) (α : R →+* X.presheaf.obj (op ⊤)) :
    X ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of R) :=
  X.toΓSpec ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom α)

/-- `AlgebraicGeometry.LocallyRingedSpace.toSpecOfAlgMap` is the adjunction's hom equivalence,
on the nose. -/
theorem toSpecOfAlgMap_eq_homEquiv (X : LocallyRingedSpace.{u}) (α : R →+* X.presheaf.obj (op ⊤)) :
    toSpecOfAlgMap X α =
      ΓSpec.locallyRingedSpaceAdjunction.homEquiv X (op (CommRingCat.of R))
        (op (CommRingCat.ofHom α)) := rfl

/-- **Pulling an algebra structure back along a morphism is precomposing the corresponding map to
`Spec R` with it.**

This is the half of the correspondence that does the work: it turns a statement about
`AlgebraicGeometry.LocallyRingedSpace.comapAlgMap` ; which is where an algebra structure on a
subspace comes from ; into one about composition of morphisms, where the gluing machinery lives.
The proof is `AlgebraicGeometry.LocallyRingedSpace.toΓSpec_naturality`, which is why that lemma
is in this file. -/
theorem comp_toSpecOfAlgMap (f : X ⟶ Y) (α : R →+* Y.presheaf.obj (op ⊤)) :
    f ≫ toSpecOfAlgMap Y α = toSpecOfAlgMap X (comapAlgMap f α) := by
  rw [toSpecOfAlgMap, toSpecOfAlgMap, ← Category.assoc, toΓSpec_naturality, Category.assoc,
    ← Spec.locallyRingedSpaceMap_comp]
  rfl

/-- **Different algebra structures give different maps to `Spec R`.** -/
theorem toSpecOfAlgMap_injective (X : LocallyRingedSpace.{u}) :
    Function.Injective (toSpecOfAlgMap (R := R) X) := by
  intro α α' h
  rw [toSpecOfAlgMap_eq_homEquiv, toSpecOfAlgMap_eq_homEquiv] at h
  have := (ΓSpec.locallyRingedSpaceAdjunction.homEquiv X (op (CommRingCat.of R))).injective h
  exact congrArg (fun m : CommRingCat.of R ⟶ _ ↦ m.hom) (Quiver.Hom.op_inj this)

/-- **Every map to `Spec R` comes from an algebra structure.**

Stated existentially rather than as an inverse map because that is the form a caller wants: a
morphism produced by gluing is not built from a structure, and this is what turns it back into
one. -/
theorem exists_toSpecOfAlgMap_eq (X : LocallyRingedSpace.{u})
    (g : X ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of R)) :
    ∃ α : R →+* X.presheaf.obj (op ⊤), toSpecOfAlgMap X α = g := by
  refine ⟨((ΓSpec.locallyRingedSpaceAdjunction.homEquiv X (op (CommRingCat.of R))).symm g).unop.hom,
    ?_⟩
  rw [toSpecOfAlgMap_eq_homEquiv]
  exact (ΓSpec.locallyRingedSpaceAdjunction.homEquiv X (op (CommRingCat.of R))).apply_symm_apply g

end AlgMap

end AlgebraicGeometry.LocallyRingedSpace

end
