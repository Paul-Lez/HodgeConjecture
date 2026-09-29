/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Finite generation of an ideal transported along a ring isomorphism

Material for `Mathlib/RingTheory/Finiteness/Ideal.lean`, which is where `Ideal.FG` lives and
where its forward companion `Ideal.FG.map` ; the lemma this proof applies to `e.symm` ; is
stated; see `README.md` on the mirror tree. Upstreaming it adds nothing: that file's transitive
closure is **1067** Mathlib modules, the import above is the target itself, and the cost is
**0**, measured with `python3 scripts/import_cost.py Other/Oka/RingTheory/Finiteness/Ideal.lean`.

**This file was `Other/Oka/RingTheory/Ideal/Maps.lean` until taxis #935**, proposing
`Mathlib/RingTheory/Ideal/Maps.lean`, whose `Ideal.comap_symm` and `Ideal.map_symm` are the
neighbouring API for the *operation*. That path cost **39** on a closure of 1028, all of it
`Mathlib.RingTheory.Finiteness.Ideal`, because `Ideal.FG` is not in scope there ; while the file
that has `Ideal.FG` already imports `Mathlib.RingTheory.Ideal.Maps` and so has both halves.
**Split by destination, not by subject**: the operation is `Ideal.map`, and the destination is
where the predicate being transported lives.

Mathlib has `Ideal.FG.map` in the forward direction, and `Submodule.fg_map_iff` for
`Submodule.map` along an injective *linear* map; `Ideal.map` along a ring homomorphism is a
different operation, and nothing transports `Ideal.FG` backwards along a `RingEquiv`. The proof
below is the forward lemma applied to `e.symm`.

## Main results

- `Ideal.FG.of_map_ringEquiv`: finite generation of an ideal can be checked after transporting it
  along a ring isomorphism.
-/

@[expose] public section

/-- Finite generation of an ideal can be checked after transporting it along a ring
isomorphism. -/
theorem Ideal.FG.of_map_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    {I : Ideal A} (h : (I.map (e : A →+* B)).FG) : I.FG := by
  have h2 := h.map (e.symm : B →+* A)
  rwa [Ideal.map_map, show (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A from
    RingHom.ext e.symm_apply_apply, Ideal.map_id] at h2

end
