/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic

import HodgeConjecture.Lemmas.AlgebraicGeometry.CycleComponentDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothComplexCoordinates
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Dimension bounds for smooth complex schemes

This file proves the dimension-theoretic consequences of smooth complex coordinates that do not
require a catenary dimension formula.  The commutative-algebra core is that a quasi-finite algebra
does not increase Krull dimension, and a flat quasi-finite algebra preserves the height of every
prime ideal.  Applying these results to an étale coordinate map bounds the Krull dimension of a
standard-smooth complex algebra of relative dimension `d` by `d`.

For a smooth complex scheme, the affine coordinate neighborhoods therefore give the global bound
`height x + coheight x ≤ d`.  The reverse inequality, and hence equality, is the catenary
dimension formula.  It is not a consequence of the currently available Mathlib API and is not
assumed here.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Contraction of prime ideals is strictly monotone for a quasi-finite algebra. -/
lemma QuasiFinite.strictMono_primeSpectrumComap [QuasiFinite R S] :
    StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro P Q hPQ
  have hle : P.asIdeal.under R ≤ Q.asIdeal.under R := Ideal.comap_mono hPQ.le
  refine lt_of_le_of_ne hle ?_
  intro heq
  have heq' : P.asIdeal.under R = Q.asIdeal.under R := by
    simpa [Ideal.under] using congrArg PrimeSpectrum.asIdeal heq
  have hPQeq : P.asIdeal = Q.asIdeal :=
    QuasiFinite.eq_of_le_of_under_eq (R := R) P.asIdeal Q.asIdeal hPQ.le heq'
  exact hPQ.ne (PrimeSpectrum.ext hPQeq)

/-- A quasi-finite algebra cannot have larger Krull dimension than its base. -/
lemma QuasiFinite.ringKrullDim_le [QuasiFinite R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  rw [ringKrullDim, ringKrullDim]
  exact Order.krullDim_le_of_strictMono _ QuasiFinite.strictMono_primeSpectrumComap

/-- A flat quasi-finite algebra preserves the height of every prime under contraction. -/
lemma QuasiFinite.height_eq_height_under [QuasiFinite R S] [Module.Flat R S]
    (P : Ideal S) [P.IsPrime] :
    P.height = (P.under R).height := by
  calc
    P.height = Order.height (⟨P, inferInstance⟩ : PrimeSpectrum S) :=
      by
        exact PrimeSpectrum.height_eq_orderHeight
          (⟨P, inferInstance⟩ : PrimeSpectrum S)
    _ = Order.height
        (PrimeSpectrum.comap (algebraMap R S) (⟨P, inferInstance⟩ : PrimeSpectrum S)) := by
      apply Order.height_eq_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
        QuasiFinite.strictMono_primeSpectrumComap
      intro Q p hp
      have hp' : p.asIdeal < Q.asIdeal.under R := by
        have hp'' : p.asIdeal <
            (PrimeSpectrum.comap (algebraMap R S) Q).asIdeal := hp
        simpa only [PrimeSpectrum.comap_asIdeal] using hp''
      obtain ⟨Q', hQ'Q, hQ'prime, hQ'over⟩ :=
        Q.asIdeal.exists_ideal_lt_liesOver_of_lt
          (R := R) (p := p.asIdeal) (q := Q.asIdeal.under R) hp'
      refine ⟨⟨Q', hQ'prime⟩, hQ'Q, ?_⟩
      apply PrimeSpectrum.ext
      simpa [Ideal.under] using hQ'over.over.symm
    _ = (P.under R).height := by
      rw [show (P.under R) =
        (PrimeSpectrum.comap (algebraMap R S)
          (⟨P, inferInstance⟩ : PrimeSpectrum S)).asIdeal from rfl]
      exact (PrimeSpectrum.height_eq_orderHeight
        (PrimeSpectrum.comap (algebraMap R S)
          (⟨P, inferInstance⟩ : PrimeSpectrum S))).symm

end Algebra

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The contraction of a maximal ideal along a finite-type map from a Jacobson ring is maximal. -/
lemma FiniteType.isMaximal_comap_of_isJacobsonRing [IsJacobsonRing R] {f : R →+* S}
    (hf : f.FiniteType) (P : Ideal S) [P.IsMaximal] : (P.comap f).IsMaximal := by
  let K := S ⧸ P
  let q : S →+* K := Ideal.Quotient.mk P
  let : Field K := Ideal.Quotient.field P
  have hft : (q.comp f).FiniteType := hf.comp_surjective Ideal.Quotient.mk_surjective
  have hfin : (q.comp f).Finite :=
    RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hft
  have hmax : ((⊥ : Ideal K).comap (q.comp f)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (q.comp f) hfin.to_isIntegral ⊥
  change (((⊥ : Ideal K).comap q).comap f).IsMaximal at hmax
  have hq : (⊥ : Ideal K).comap q = P := by
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  rw [hq] at hmax
  exact hmax

/-- A standard-smooth algebra of relative dimension `d` has Krull dimension at most the
dimension of the base plus `d`. -/
lemma IsStandardSmoothOfRelativeDimension.ringKrullDim_le_add {f : R →+* S} {d : ℕ}
    [IsNoetherianRing R]
    (hf : f.IsStandardSmoothOfRelativeDimension d) :
    ringKrullDim S ≤ ringKrullDim R + d := by
  obtain ⟨g, _, hg⟩ := hf.exists_etale_mvPolynomial
  let : Algebra (MvPolynomial (Fin d) R) S := g.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin d) R) S :=
    RingHom.etale_algebraMap.mp hg
  calc
    ringKrullDim S ≤ ringKrullDim (MvPolynomial (Fin d) R) :=
      Algebra.QuasiFinite.ringKrullDim_le
    _ = ringKrullDim R + d := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_fin]

/-- A standard-smooth complex algebra of relative dimension `d` has Krull dimension at most
`d`. -/
lemma IsStandardSmoothOfRelativeDimension.ringKrullDim_le_complex {S : Type*} [CommRing S]
    {f : ℂ →+* S} {d : ℕ} (hf : f.IsStandardSmoothOfRelativeDimension d) :
    ringKrullDim S ≤ d := by
  simpa only [ringKrullDim_eq_zero_of_field, WithBot.coe_zero, zero_add] using
    hf.ringKrullDim_le_add

end RingHom

namespace MvPolynomial

/-- Every maximal ideal of a polynomial ring in `d` variables over a field has height `d`. -/
lemma height_eq_fin_of_isMaximal (K : Type*) [Field K] (d : ℕ)
    (P : Ideal (MvPolynomial (Fin d) K)) [P.IsMaximal] : P.height = d := by
  induction d with
  | zero =>
      have hle : (↑P.height : WithBot ℕ∞) ≤
          ringKrullDim (MvPolynomial (Fin 0) K) :=
        Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field, Nat.card_fin, Nat.cast_zero, add_zero] at hle
      exact le_antisymm (WithBot.coe_le_coe.mp hle) bot_le
  | succ n ih =>
      let e : MvPolynomial (Fin (n + 1)) K ≃+* Polynomial (MvPolynomial (Fin n) K) :=
        (MvPolynomial.finSuccEquiv K n).toRingEquiv
      let Q : Ideal (Polynomial (MvPolynomial (Fin n) K)) := P.map e
      let : Q.IsMaximal := Ideal.map_isMaximal_of_equiv e
      have hunder : (Q.under (MvPolynomial (Fin n) K)).IsMaximal := by
        change (Q.comap (Polynomial.C : MvPolynomial (Fin n) K →+*
          Polynomial (MvPolynomial (Fin n) K))).IsMaximal
        exact Polynomial.isMaximal_comap_C_of_isJacobsonRing
          (R := MvPolynomial (Fin n) K) Q
      calc
        P.height = Q.height := (RingEquiv.height_map e P).symm
        _ = (Q.under (MvPolynomial (Fin n) K)).height + 1 :=
          Polynomial.height_eq_height_add_one _ Q
        _ = n + 1 := by rw [ih (Q.under (MvPolynomial (Fin n) K))]

end MvPolynomial

namespace RingHom

/-- A nonzero standard-smooth complex algebra of relative dimension `d` has Krull dimension
exactly `d`.

This global equality does not by itself give the pointwise catenary dimension formula. -/
lemma IsStandardSmoothOfRelativeDimension.ringKrullDim_eq_complex {S : Type*} [CommRing S]
    [Nontrivial S] {f : ℂ →+* S} {d : ℕ}
    (hf : f.IsStandardSmoothOfRelativeDimension d) : ringKrullDim S = d := by
  obtain ⟨g, _, hg⟩ := hf.exists_etale_mvPolynomial
  let : Algebra (MvPolynomial (Fin d) ℂ) S := g.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin d) ℂ) S :=
    RingHom.etale_algebraMap.mp hg
  obtain ⟨P, hP⟩ := Ideal.exists_maximal S
  let : P.IsMaximal := hP
  have hfiniteType : (algebraMap (MvPolynomial (Fin d) ℂ) S).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have hunder : (P.under (MvPolynomial (Fin d) ℂ)).IsMaximal :=
    hfiniteType.isMaximal_comap_of_isJacobsonRing P
  have hheight : P.height = d := by
    rw [Algebra.QuasiFinite.height_eq_height_under (R := MvPolynomial (Fin d) ℂ)]
    exact MvPolynomial.height_eq_fin_of_isMaximal ℂ d
      (P.under (MvPolynomial (Fin d) ℂ))
  apply le_antisymm hf.ringKrullDim_le_complex
  change (↑(d : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim S
  have hlower : (↑P.height : WithBot ℕ∞) ≤ ringKrullDim S :=
    Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  rw [← hheight]
  exact hlower

end RingHom

namespace AlgebraicGeometry

variable {X : Scheme}

/-- The order-theoretic Krull dimension of an affine open is the ring-theoretic Krull dimension
of its ring of sections. -/
lemma orderKrullDim_affineOpen_eq_ringKrullDim (U : X.Opens) (hU : IsAffineOpen U) :
    Order.krullDim U = ringKrullDim Γ(X, U) := by
  calc
    Order.krullDim U = topologicalKrullDim U :=
      (Scheme.topologicalKrullDim_eq_orderKrullDim U.toScheme).symm
    _ = topologicalKrullDim (PrimeSpectrum Γ(X, U)) :=
      hU.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
    _ = ringKrullDim Γ(X, U) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _

/-- If every point has an open neighborhood of Krull dimension at most `d`, then the whole scheme
has Krull dimension at most `d`.

The proof puts each finite specialization chain in a neighborhood of its least element.  Every
other element of the chain is a generization of that point, so it remains in the open set. -/
lemma Scheme.orderKrullDim_le_of_exists_open_orderKrullDim_le (X : Scheme) (d : ℕ)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Order.krullDim U ≤ d) :
    Order.krullDim X ≤ d := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
      rw [Order.krullDim_eq_bot]
      exact bot_le
  | inr hX =>
      let : Nonempty X := hX
      rw [Order.krullDim_eq_iSup_length]
      apply WithBot.coe_le_coe.mpr
      apply iSup_le
      intro l
      obtain ⟨U, hhead, hU⟩ := h l.head
      have hmem (i : Fin (l.length + 1)) : l i ∈ U := by
        have hle : l.head ≤ l i := l.monotone (Fin.zero_le i)
        rw [Scheme.le_iff_specializes] at hle
        exact hle.mem_open U.isOpen hhead
      have hlt (a b : U.toScheme) (hab : U.ι.base a < U.ι.base b) : a < b := by
        rw [lt_iff_le_not_ge]
        constructor
        · rw [Scheme.le_iff_specializes]
          apply U.isOpenEmbedding.isInducing.specializes_iff.mp
          rw [← Scheme.le_iff_specializes]
          exact hab.le
        · intro hback
          apply (not_le_of_gt hab)
          rw [Scheme.le_iff_specializes] at hback ⊢
          exact U.isOpenEmbedding.isInducing.specializes_iff.mpr hback
      let lU : LTSeries U :=
        { length := l.length
          toFun := fun i ↦ ⟨l i, hmem i⟩
          step := fun i ↦ by
            simpa only [Set.mem_ofPred_eq] using
              hlt (⟨l i.castSucc, hmem i.castSucc⟩ : U.toScheme)
                (⟨l i.succ, hmem i.succ⟩ : U.toScheme) (l.step i) }
      have hlength : (l.length : WithBot ℕ∞) ≤ Order.krullDim U :=
        Order.le_krullDim_iff.mpr ⟨lU, rfl⟩
      exact WithBot.coe_le_coe.mp (hlength.trans hU)

variable {f : X ⟶ Spec ↧ℂ} {d : ℕ}

/-- A smooth complex scheme of relative dimension `d` has order-theoretic Krull dimension at
most `d`. -/
lemma SmoothOfRelativeDimension.orderKrullDim_le_complex
    [SmoothOfRelativeDimension d f] : Order.krullDim X ≤ d := by
  apply Scheme.orderKrullDim_le_of_exists_open_orderKrullDim_le X d
  intro x
  obtain ⟨U, hU, hxU, hsmooth⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension
      (d := d) f x
  refine ⟨U, hxU, ?_⟩
  rw [orderKrullDim_affineOpen_eq_ringKrullDim U hU]
  exact (complexRestrictionMap_isStandardSmoothOfRelativeDimension
    (d := d) f hsmooth).ringKrullDim_le_complex

/-- At every point of a smooth complex scheme of relative dimension `d`, the sum of the
order-theoretic dimension and codimension is at most `d`. -/
lemma SmoothOfRelativeDimension.height_add_coheight_le_complex
    [SmoothOfRelativeDimension d f] (x : X) :
    Order.height x + Order.coheight x ≤ d := by
  let : Nonempty X := ⟨x⟩
  have hpoint :
      (↑(Order.height x + Order.coheight x) : WithBot ℕ∞) ≤ Order.krullDim X := by
    rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.mpr (le_iSup (fun y : X ↦
      Order.height y + Order.coheight y) x)
  exact WithBot.coe_le_coe.mp
    (hpoint.trans (SmoothOfRelativeDimension.orderKrullDim_le_complex
      (f := f) (d := d)))

/-- If a point of a smooth complex `d`-fold has coheight `p`, its height is at most `d - p`.
This is the direction of the dimension formula that does not require catenarity. -/
lemma SmoothOfRelativeDimension.height_le_sub_of_coheight_eq
    [SmoothOfRelativeDimension d f] (x : X) {p : ℕ} (hx : Order.coheight x = p) :
    Order.height x ≤ d - p := by
  apply ENat.le_sub_of_add_le_right (by simp)
  rw [← hx]
  exact SmoothOfRelativeDimension.height_add_coheight_le_complex
    (f := f) (d := d) x

/-- Every point of a smooth complex scheme of relative dimension `d` has coheight at most `d`. -/
lemma SmoothOfRelativeDimension.coheight_le_complex
    [SmoothOfRelativeDimension d f] (x : X) : Order.coheight x ≤ d := by
  calc
    Order.coheight x ≤ Order.height x + Order.coheight x := le_add_left le_rfl
    _ ≤ d := SmoothOfRelativeDimension.height_add_coheight_le_complex
      (f := f) (d := d) x

/-- A smooth complex scheme of relative dimension `d` has no point of coheight `p` when
`d < p`. -/
lemma SmoothOfRelativeDimension.coheight_ne_of_lt
    [SmoothOfRelativeDimension d f] (x : X) {p : ℕ} (hp : d < p) :
    Order.coheight x ≠ p := by
  intro hx
  have hle : (p : ℕ∞) ≤ d := by
    rw [← hx]
    exact SmoothOfRelativeDimension.coheight_le_complex (f := f) (d := d) x
  exact (not_le_of_gt (by exact_mod_cast hp)) hle

end AlgebraicGeometry
