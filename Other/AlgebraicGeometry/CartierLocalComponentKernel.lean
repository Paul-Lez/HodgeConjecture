/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicGeometry.CartierLocalIdeal
public import Other.AlgebraicGeometry.Cycle.Component.RegularImmersion
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Component ideal in ambient stalks

The reduced cycle component is defined by the vanishing ideal of the closure of its generic
point.  On an affine open containing that point, this identifies the kernel of the component
section map with the corresponding prime ideal.  Localization then identifies the same ideal in
every ambient stalk on the component.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Order

namespace AlgebraicGeometry

variable (X : Over (Spec ↧ℂ))

attribute [local instance] isNoetherian_of_isProjective

private lemma cycleComponent_affine_app_ker_eq_prime
    (x : X.left) (U : X.left.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U) :
    RingHom.ker ((cycleComponentι X.left x).app U).hom =
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
  let c : cycleComponent X.left x ⟶ X.left := cycleComponentι X.left x
  let I := Scheme.IdealSheafData.vanishingIdeal
    (X := X.left) ⟨closure {x}, isClosed_closure⟩
  let xu : U.toScheme := ⟨x, hxU⟩
  let P : Ideal Γ(X.left, U) := (hU.primeIdealOf xu).asIdeal
  have hsingleton : hU.fromSpec ⁻¹' ({x} : Set X.left) =
      ({hU.primeIdealOf xu} : Set (Spec Γ(X.left, U))) := by
    ext Q
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun hQ ↦ hU.fromSpec.isOpenEmbedding.injective
      (hQ.trans (hU.fromSpec_primeIdealOf xu).symm), ?_⟩
    rintro rfl
    exact hU.fromSpec_primeIdealOf xu
  have hpreimage : hU.fromSpec ⁻¹' closure {x} =
      closure {hU.primeIdealOf xu} := by
    have hclosure := congrArg
      (fun T : Set (Spec Γ(X.left, U)) ↦ closure T) hsingleton
    exact (hU.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      hU.fromSpec.continuous ({x} : Set X.left)).trans hclosure
  have hI : I.ideal ⟨U, hU⟩ = P := by
    change PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' closure {x}) = P
    erw [hpreimage, PrimeSpectrum.vanishingIdeal_closure,
      PrimeSpectrum.vanishingIdeal_singleton]
  have hker : RingHom.ker ((c.app U).hom) = P := by
    rw [← Scheme.Hom.ker_apply c ⟨U, hU⟩]
    calc
      c.ker.ideal ⟨U, hU⟩ = I.ideal ⟨U, hU⟩ := by
        rw [show c = I.subschemeι from rfl]
        exact congrArg (fun J : X.left.IdealSheafData ↦ J.ideal ⟨U, hU⟩)
          I.ker_subschemeι
      _ = P := hI
  simpa [c, P, xu] using hker

private lemma ker_localRingHom_of_surjective
    {A B : Type*} [CommRing A] [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q) (Q : Ideal B) [Q.IsPrime] :
    RingHom.ker (Localization.localRingHom (Q.comap q) Q q rfl) =
      (RingHom.ker q).map (algebraMap A (Localization.AtPrime (Q.comap q))) := by
  simpa [Localization.localRingHom] using
    (IsLocalization.ker_map (Localization.AtPrime Q) q
      (Ideal.map_primeCompl_comap_of_surjective q hq Q))

private lemma ker_of_ringEquiv_square
    {R L C K : Type*} [CommRing R] [CommRing L] [CommRing C] [CommRing K]
    (f : R →+* C) (g : L →+* K) (eR : R ≃+* L) (eC : C ≃+* K)
    (h : g.comp (eR : R →+* L) = (eC : C →+* K).comp f) :
    RingHom.ker f = Ideal.comap eR (RingHom.ker g) := by
  ext r
  change f r = 0 ↔ g (eR r) = 0
  have he := congrArg (fun k : R →+* K => k r) h
  simp only [RingHom.coe_comp, Function.comp_apply] at he
  constructor
  · intro hr
    rw [hr] at he
    simpa using he
  · intro hr
    apply eC.injective
    have hr' : g ((eR : R →+* L) r) = 0 := hr
    have hh : (eC : C →+* K) (f r) = 0 := by rw [← he, hr']
    simpa using hh

private lemma comap_map_of_localization_equiv
    {A R L : Type*} [CommRing A] [CommRing R] [CommRing L]
    (P : Ideal A) (aR : A →+* R) (aL : A →+* L) (eR : R ≃+* L)
    (h : (eR : R →+* L).comp aR = aL) :
    Ideal.comap eR (P.map aL) = P.map aR := by
  rw [← h, ← Ideal.map_map]
  exact Ideal.comap_map_of_bijective eR eR.bijective

/-- The stalk kernel of a reduced component is the localization of its generic affine prime.

This is the algebraic input used to transport generic principal ideal generation to all smooth
component points on the resulting principal open.
-/
theorem cycleComponent_stalkMap_ker_eq_prime_map
    (x : X.left) (U : X.left.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U)
    (z : cycleComponent X.left x)
    (hzU : cycleComponentι X.left x z ∈ U) :
    RingHom.ker ((cycleComponentι X.left x).stalkMap z).hom =
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.map
        (X.left.presheaf.germ U (cycleComponentι X.left x z) hzU).hom := by
  let c : cycleComponent X.left x ⟶ X.left := cycleComponentι X.left x
  let W : (cycleComponent X.left x).Opens := c ⁻¹ᵁ U
  let hW : IsAffineOpen W := hU.preimage c
  let hzW : z ∈ W := hzU
  let q := (c.appLE U W le_rfl).hom
  let Py : Ideal Γ(X.left, U) := (hU.primeIdealOf ⟨c z, hzU⟩).asIdeal
  let Q : Ideal Γ(cycleComponent X.left x, W) :=
    (hW.primeIdealOf ⟨z, hzW⟩).asIdeal
  let _ : Algebra (Γ(X.left, U)) (X.left.presheaf.stalk (c z)) :=
    TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨c z, hzU⟩
  let _ : Algebra (Γ(cycleComponent X.left x, W))
      ((cycleComponent X.left x).presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk (cycleComponent X.left x).presheaf ⟨z, hzW⟩
  let _ := hU.isLocalization_stalk ⟨c z, hzU⟩
  let _ := hW.isLocalization_stalk ⟨z, hzW⟩
  have hq : Function.Surjective q := by
    simpa [q, W, c, Scheme.Hom.appLE_eq_app] using c.app_surjective U hU
  have hPQ : Py = Q.comap q := by
    have h := (IsAffineOpen.comap_primeIdealOf_appLE (f := c) U hU W hW le_rfl
      (x := z) hzW).symm
    exact congrArg (fun p : PrimeSpectrum _ ↦ p.asIdeal) h
  let eR :
      X.left.presheaf.stalk (c z) ≃+*
        Localization.AtPrime Py :=
    (IsLocalization.algEquiv Py.primeCompl
      (X.left.presheaf.stalk (c z)) (Localization.AtPrime Py)).toRingEquiv
  let eC :
      (cycleComponent X.left x).presheaf.stalk z ≃+*
        Localization.AtPrime Q :=
    (IsLocalization.algEquiv Q.primeCompl
      ((cycleComponent X.left x).presheaf.stalk z) (Localization.AtPrime Q)).toRingEquiv
  let L : Localization.AtPrime Py →+* Localization.AtPrime Q :=
    Localization.localRingHom Py Q q hPQ
  have hLker : RingHom.ker L = (RingHom.ker q).map
      (algebraMap (Γ(X.left, U)) (Localization.AtPrime Py)) := by
    have hT : Submonoid.map q Py.primeCompl = Q.primeCompl := by
      ext b
      constructor
      · rintro ⟨a, ha, rfl⟩
        apply Ideal.mem_primeCompl_iff.mpr
        intro hqa
        apply Ideal.mem_primeCompl_iff.mp ha
        have haa : a ∈ Q.comap q := hqa
        rw [← hPQ] at haa
        exact haa
      · intro hb
        obtain ⟨a, rfl⟩ := hq b
        refine ⟨a, Ideal.mem_primeCompl_iff.mpr ?_, rfl⟩
        intro ha
        apply Ideal.mem_primeCompl_iff.mp hb
        have haa : a ∈ Q.comap q := by
          rw [← hPQ]
          exact ha
        exact haa
    simpa [L, Localization.localRingHom] using
      (IsLocalization.ker_map (Localization.AtPrime Q) q hT)
  have heRalg : (eR : _ →+* _).comp
      (X.left.presheaf.germ U (c z) hzU).hom =
      algebraMap (Γ(X.left, U)) (Localization.AtPrime Py) := by
    ext a
    change (IsLocalization.algEquiv Py.primeCompl
        (X.left.presheaf.stalk (c z)) (Localization.AtPrime Py))
        ((algebraMap (Γ(X.left, U))
          (X.left.presheaf.stalk (c z))) a) = _
    exact (IsLocalization.algEquiv Py.primeCompl
      (X.left.presheaf.stalk (c z)) (Localization.AtPrime Py)).commutes a
  have hqker : RingHom.ker q =
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    simpa [q, c, W, Scheme.Hom.appLE_eq_app] using
      cycleComponent_affine_app_ker_eq_prime X x U hU hxU
  have hkernel_equiv : RingHom.ker ((c.stalkMap z).hom) =
      Ideal.comap eR (RingHom.ker L) := by
    apply ker_of_ringEquiv_square (f := (c.stalkMap z).hom) (g := L) eR eC
    -- The affine stalk comparison is exactly the arrow comparison above.
    let hs := IsAffineOpen.arrowStalkMapIso c U hU W hW le_rfl (x := z) hzW
    change L.comp (eR : _ →+* _) = (eC : _ →+* _).comp (c.stalkMap z).hom
    have hsq := Arrow.Hom.w hs.hom
    dsimp [hs, IsAffineOpen.arrowStalkMapIso, Arrow.isoMk'] at hsq
    change (eR.toCommRingCatIso.hom ≫ CommRingCat.ofHom L) =
      (CommRingCat.ofHom (c.stalkMap z).hom ≫ eC.toCommRingCatIso.hom) at hsq
    have hsq' := congrArg CommRingCat.Hom.hom hsq
    simpa only [CommRingCat.hom_comp, CommRingCat.ofHom_hom, CommRingCat.hom_ofHom,
      RingEquiv.toCommRingCatIso_hom] using hsq'
  rw [hkernel_equiv, hLker, hqker]
  exact comap_map_of_localization_equiv _ _ _ eR heRalg

namespace Scheme.CartierData.LocalForm

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [IsProjective X.hom]
  (c : Scheme.CartierData X.left) {i : c.ι} (x : X.left)

/-- On the principal open where the generic affine ideal is generated by the local equation, the
equation generates the kernel of the reduced component stalk map at every component point. -/
theorem span_germ_equation_eq_component_stalkMap_ker_of_away
    (f : c.LocalForm i x) (s : Γ(X.left, f.opens))
    (_hs : s ∉ (f.isAffineOpen.primeIdealOf ⟨x, f.mem⟩).asIdeal)
    (hEq :
      (f.isAffineOpen.primeIdealOf ⟨x, f.mem⟩).asIdeal.map
          (algebraMap (Γ(X.left, f.opens)) (Localization.Away s)) =
        (Ideal.span {f.equation}).map
          (algebraMap (Γ(X.left, f.opens)) (Localization.Away s)))
    (z : cycleComponent X.left x)
    (hz : cycleComponentι X.left x z ∈ f.opens)
    (hzs : cycleComponentι X.left x z ∈ X.left.basicOpen s) :
    Ideal.span {X.left.presheaf.germ f.opens (cycleComponentι X.left x z) hz f.equation} =
      RingHom.ker ((cycleComponentι X.left x).stalkMap z).hom := by
  let A := Γ(X.left, f.opens)
  let R := X.left.presheaf.stalk (cycleComponentι X.left x z)
  let P : Ideal A := (f.isAffineOpen.primeIdealOf ⟨x, f.mem⟩).asIdeal
  let _ : Algebra A R :=
    TopCat.Presheaf.algebra_section_stalk X.left.presheaf
      ⟨cycleComponentι X.left x z, hz⟩
  let _ := f.isAffineOpen.isLocalization_stalk
    ⟨cycleComponentι X.left x z, hz⟩
  have hunit : IsUnit
      (X.left.presheaf.germ f.opens (cycleComponentι X.left x z) hz s) :=
    (Scheme.mem_basicOpen _ s (cycleComponentι X.left x z) hz).mp hzs
  let l : Localization.Away s →+* R :=
    IsLocalization.Away.lift s hunit
  have hl : l.comp (algebraMap A (Localization.Away s)) =
      (X.left.presheaf.germ f.opens (cycleComponentι X.left x z) hz).hom := by
    exact IsLocalization.Away.lift_comp s hunit
  have hEqR : P.map
      (X.left.presheaf.germ f.opens (cycleComponentι X.left x z) hz).hom =
      (Ideal.span {f.equation}).map
        (X.left.presheaf.germ f.opens (cycleComponentι X.left x z) hz).hom := by
    have h := congrArg (fun J : Ideal (Localization.Away s) ↦ J.map l) hEq
    simpa [A, P, Ideal.map_map, hl] using h
  have hker := cycleComponent_stalkMap_ker_eq_prime_map X x f.opens
    f.isAffineOpen f.mem z hz
  have hker' : P.map
      (X.left.presheaf.germ f.opens (cycleComponentι X.left x z) hz).hom =
      RingHom.ker ((cycleComponentι X.left x).stalkMap z).hom := by
    simpa [P] using hker.symm
  rw [← hker', hEqR, Ideal.map_span]
  simp

end Scheme.CartierData.LocalForm

end AlgebraicGeometry
