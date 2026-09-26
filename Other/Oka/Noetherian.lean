/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.ChangeOfCoordinates
public import Other.Oka.OkaLemma
public import Other.Oka.RingTheory.Finiteness.Ideal

/-!
# The Rückert basis theorem

The ring `LocalOkaRing (Fin n)` of germs at the origin of holomorphic functions in `n` complex
variables is a Noetherian ring. Together with `LocalOkaRing.instIsLocalRing` of
`Other/Oka/LocalOkaRing.lean` this makes it a Noetherian local ring.

The proof is the classical one, by induction on `n`. In no variables every nonzero germ is its
own constant term, so the ring is a field. For the inductive step, let `I` be a nonzero ideal of
`R := LocalOkaRing (Fin (n + 1))` and let `f ∈ I` be nonzero. After a linear change of
coordinates ; `LocalOkaRing.exists_congr_localweierstrass_preparation`, which is where all the
analysis is hidden ; the germ `f` is a unit times `LocalOkaRing.fromPolynomial g` for a
Weierstrass polynomial `g` of some degree `d` over `S := LocalOkaRing (Fin n)`. The Weierstrass
division theorem then says that `R ⧸ (fromPolynomial g)` is generated as an `S`-module by the
`d` powers of the last variable, so it is a Noetherian `S`-module by induction, hence a
Noetherian `R`-module; consequently the image of `I` in it is finitely generated, and adjoining
`fromPolynomial g` to any lift of those generators generates `I`.

## Main results

- `LocalOkaRing.module_finite_quotient_fromPolynomial`: the quotient of the germs in `n + 1`
  variables by a Weierstrass polynomial is a finite module over the germs in `n` variables.
- `LocalOkaRing.fg_of_fromPolynomial_mem`: an ideal containing a Weierstrass polynomial is
  finitely generated.
- `LocalOkaRing.isNoetherianRing_fin` and `LocalOkaRing.instIsNoetherianRing`: the Rückert
  basis theorem, `IsNoetherianRing (LocalOkaRing (Fin n))` and, transported along a relabelling
  of the variables, `IsNoetherianRing (LocalOkaRing ι)` for any finite `ι`.

## References

- [Hans Grauert and Reinhold Remmert, *Analytische Stellenalgebren*][grauert-remmert1971], §I
- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
- [Hans Grauert and Reinhold Remmert, *Theory of Stein spaces*][grauert-remmert1979], Chapter II
-/

@[expose] public section

open Polynomial

namespace LocalOkaRing

/-! ### The base case: germs in no variables -/

section IsEmpty

variable {ι : Type*} [IsEmpty ι]

/-- The ring of germs in no variables is Noetherian, being a field. -/
theorem isNoetherianRing_of_isEmpty : IsNoetherianRing (LocalOkaRing ι) := by
  refine (isNoetherianRing_iff_ideal_fg _).mpr fun I ↦ ?_
  rcases eq_or_ne I ⊥ with rfl | hI
  · exact Submodule.fg_bot
  · obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    rw [Ideal.eq_top_of_isUnit_mem I hxI (isUnit_iff_ne_zero.mpr hx0)]
    exact ⟨{1}, by simp⟩

end IsEmpty

/-! ### The inductive step -/

section Step

variable {n : ℕ}

/-- The quotient of the germs in `n + 1` variables by a Weierstrass polynomial of degree `d` is
generated, as a module over the germs in `n` variables, by the images of
`1, X, …, X ^ (d - 1)`; in particular it is a finite module.

This is the module-theoretic content of the Weierstrass division theorem: division by `g`
writes every germ as a multiple of `g` plus a polynomial of degree less than `d`. -/
theorem module_finite_quotient_fromPolynomial {g : (LocalOkaRing (Fin n))[X]}
    (hg : IsLocalWeierstrassPolynomial
      (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) g)) :
    Module.Finite (LocalOkaRing (Fin n))
      (LocalOkaRing (Fin (n + 1)) ⧸ Ideal.span {LocalOkaRing.fromPolynomial g}) := by
  have hgm : g.Monic := Polynomial.monic_of_injective Subtype.val_injective hg.monic
  have hgdeg : g.degree = (g.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hgm.ne_zero
  haveI : Module.Finite (LocalOkaRing (Fin n))
      ((LocalOkaRing (Fin n))[X]_(g.natDegree)) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv _ _).symm
  refine Module.Finite.of_surjective
    (((Submodule.mkQ (Ideal.span {LocalOkaRing.fromPolynomial g})).restrictScalars
      (LocalOkaRing (Fin n))).comp (polyIncl (d := g.natDegree))) ?_
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    obtain ⟨a, b, hb, hy⟩ := localweierstrass_division g hg y
    refine ⟨⟨b, Polynomial.mem_degreeLT.mpr (hgdeg ▸ hb)⟩, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      Submodule.mkQ_apply, polyIncl_apply]
    refine (Submodule.Quotient.eq _).mpr ?_
    have hsub : LocalOkaRing.fromPolynomial b - y = -(a * LocalOkaRing.fromPolynomial g) := by
      rw [hy]; ring
    rw [hsub]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

/-- An ideal of the germs in `n + 1` variables containing a Weierstrass polynomial is finitely
generated, provided the germs in `n` variables form a Noetherian ring. -/
theorem fg_of_fromPolynomial_mem [IsNoetherianRing (LocalOkaRing (Fin n))]
    {I : Ideal (LocalOkaRing (Fin (n + 1)))} {g : (LocalOkaRing (Fin n))[X]}
    (hg : IsLocalWeierstrassPolynomial
      (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) g))
    (hgI : LocalOkaRing.fromPolynomial g ∈ I) : I.FG := by
  haveI := module_finite_quotient_fromPolynomial hg
  haveI : IsNoetherian (LocalOkaRing (Fin n))
      (LocalOkaRing (Fin (n + 1)) ⧸ Ideal.span {LocalOkaRing.fromPolynomial g}) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : IsNoetherian (LocalOkaRing (Fin (n + 1)))
      (LocalOkaRing (Fin (n + 1)) ⧸ Ideal.span {LocalOkaRing.fromPolynomial g}) :=
    isNoetherian_of_tower (LocalOkaRing (Fin n)) inferInstance
  refine Submodule.fg_of_fg_map_of_fg_inf_ker
    (Submodule.mkQ (Ideal.span {LocalOkaRing.fromPolynomial g})) (IsNoetherian.noetherian _) ?_
  rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem I).mpr hgI)]
  exact Submodule.fg_span_singleton _

end Step

/-! ### The Rückert basis theorem -/

/-- **The Rückert basis theorem** for the standard variables: the ring of germs at the origin of
holomorphic functions in `n` complex variables is Noetherian.

See `LocalOkaRing.instIsNoetherianRing` for the version with an arbitrary finite set of
variables, which is the one registered as an instance. -/
theorem isNoetherianRing_fin : ∀ n : ℕ, IsNoetherianRing (LocalOkaRing (Fin n))
  | 0 => isNoetherianRing_of_isEmpty
  | (n + 1) => by
    haveI := isNoetherianRing_fin n
    refine (isNoetherianRing_iff_ideal_fg _).mpr fun I ↦ ?_
    rcases eq_or_ne I ⊥ with rfl | hI
    · exact Submodule.fg_bot
    obtain ⟨f, hfI, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    -- move `I` to coordinates in which `f` is a unit times a Weierstrass polynomial `g`
    obtain ⟨φ, u, hu, g, hg, hfeq⟩ := exists_congr_localweierstrass_preparation hf0
    refine Ideal.FG.of_map_ringEquiv (congr φ).toRingEquiv (fg_of_fromPolynomial_mem hg ?_)
    -- the transported ideal contains `g`, since it contains `congr φ f = g * u` and `u` is a unit
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hgv : LocalOkaRing.fromPolynomial g = (congr φ).toRingEquiv f * v := by
      rw [show (congr φ).toRingEquiv f = LocalOkaRing.fromPolynomial g * u from hfeq,
        mul_assoc, hv, mul_one]
    rw [hgv]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hfI)

/-- **The Rückert basis theorem**: the ring of germs at the origin of holomorphic functions in
finitely many complex variables is Noetherian. Together with `LocalOkaRing.instIsLocalRing` it
is therefore a Noetherian local ring. -/
instance instIsNoetherianRing {ι : Type*} [Finite ι] : IsNoetherianRing (LocalOkaRing ι) := by
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  haveI := isNoetherianRing_fin n
  exact isNoetherianRing_of_surjective _ _ (congrEquiv e.symm).toRingEquiv.toRingHom
    (congrEquiv e.symm).surjective

end LocalOkaRing

end
