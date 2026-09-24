/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License").
-/
module

public import Other.AlgebraicGeometry.PointJetDetection

/-!
# First jets and algebraic section germs

The selected analytic chart only depends on the germ of a regular section.  This
file records that compatibility explicitly, including sections presented on
different Zariski opens.
-/

@[expose] public noncomputable section
open CategoryTheory Topology TopologicalSpace Opposite
open IsLocalRing
open scoped Manifold
namespace RingEquiv

lemma mem_maximalIdeal_pow_iff
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (x : R) (n : ℕ) :
    x ∈ (maximalIdeal R) ^ n ↔ e x ∈ (maximalIdeal S) ^ n := by
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e, ← Ideal.map_pow,
    Ideal.apply_mem_of_equiv_iff]

end RingEquiv

namespace AlgebraicGeometry.ComplexPoint
open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

namespace Affine

open AlgebraicGeometry.ComplexPoint.Affine

lemma ambientSection_germ_stalkIso (z : ComplexPoint X)
    (a : localSectionRing X d (localEtaleCoordinates X d z)) :
    let D := localEtaleCoordinates X d z
    let hzD : z.underlying ∈ D.neighborhood := D.mem
    let z' := (openHomeomorph X D.neighborhood).symm ⟨z, hzD⟩
    let y : D.neighborhood := z'.underlying
    let i := (D.neighborhood.stalkIso y).commRingCatIsoToRingEquiv
    i (D.neighborhood.toScheme.presheaf.germ ⊤ z'.underlying (by trivial) a) =
      X.left.presheaf.germ D.ambientCoordinateOpen y.1 (by
        simpa only [LocalEtaleCoordinates.ambientCoordinateOpen,
          Scheme.Opens.ι_image_top] using y.2) (ambientSection X d D a) := by
  dsimp
  let D := localEtaleCoordinates X d z
  let hzD : z.underlying ∈ D.neighborhood := D.mem
  let z' := (openHomeomorph X D.neighborhood).symm ⟨z, hzD⟩
  let y : D.neighborhood := z'.underlying
  have hz' : Point.map (openInclusion X D.neighborhood) z' = z := by
    change (openHomeomorph X D.neighborhood z').1 = z
    exact congrArg Subtype.val
      ((openHomeomorph X D.neighborhood).apply_symm_apply ⟨z, hzD⟩)
  let i := (D.neighborhood.stalkIso y).commRingCatIsoToRingEquiv
  have h := Scheme.Opens.germ_stalkIso_hom D.neighborhood y (V := ⊤) trivial
  have h' := congrArg (fun f => f.hom a) h
  have haeq : ambientSection X d D a = (a : Γ(X.left, D.ambientCoordinateOpen)) := by
    simp [ambientSection, Scheme.Opens.ι_appIso,
      LocalEtaleCoordinates.ambientCoordinateOpen]
    exact CommRingCat.id_apply _ _
  have hgoal : i (D.neighborhood.toScheme.presheaf.germ ⊤ y (by trivial) a) =
      X.left.presheaf.germ D.ambientCoordinateOpen y.1 (by
        simpa only [LocalEtaleCoordinates.ambientCoordinateOpen,
          Scheme.Opens.ι_image_top] using y.2)
        (ambientSection X d D a) := by
    rw [haeq]
    convert h' using 1 <;> rfl
  exact hgoal

end Affine

lemma regularPointJet_eq_of_germ_eq
    (V W : X.left.Opens) (z : ComplexPoint X)
    (hzV : z.underlying ∈ V) (hzW : z.underlying ∈ W)
    (s : Γ(X.left, V)) (t : Γ(X.left, W))
    (h : X.left.presheaf.germ V z.underlying hzV s =
      X.left.presheaf.germ W z.underlying hzW t) :
    regularPointJet X d V z hzV s = regularPointJet X d W z hzW t := by
  obtain ⟨Y, hzY, hYV, hYW, hst⟩ :=
    X.left.presheaf.germ_eq z.underlying hzV hzW s t h
  let e := localChart X d z
  let p := e z
  have hp : p ∈ e.target := e.map_source (mem_localChart_source X d z)
  have heq :
      (fun w ↦ Point.evaluate V s (e.symm w)) =ᶠ[𝓝 p]
        (fun w ↦ Point.evaluate W t (e.symm w)) := by
    have hleft : e.symm p = z := e.left_inv (mem_localChart_source X d z)
    have hyY : e.symm p ∈ Point.overOpen Y := by
      rw [hleft]
      exact hzY
    have hYVle : Y ≤ V := fun y hy => (hYV ⟨y, hy⟩).property
    have hYWle : Y ≤ W := fun y hy => (hYW ⟨y, hy⟩).property
    have hYVeq : hYV = homOfLE hYVle := Subsingleton.elim _ _
    have hYWeq : hYW = homOfLE hYWle := Subsingleton.elim _ _
    have hnhds : e.symm ⁻¹' (Point.overOpen Y) ∈ 𝓝 p :=
      e.continuousAt_symm hp ((isOpen_overOpen Y).mem_nhds hyY)
    filter_upwards [hnhds] with w hw
    have hyY' : (e.symm w).underlying ∈ Y := hw
    rw [Point.evaluate_res hYVle s (e.symm w) hyY',
      Point.evaluate_res hYWle t (e.symm w) hyY']
    simpa only [hYVeq, hYWeq] using
      congrArg (fun q => Point.evaluate Y q (e.symm w)) hst
  change fderiv ℂ (fun w ↦ Point.evaluate V s (e.symm w)) p =
    fderiv ℂ (fun w ↦ Point.evaluate W t (e.symm w)) p
  exact heq.fderiv_eq

namespace Affine

open AlgebraicGeometry.ComplexPoint.Affine

theorem regularPointJet_ne_zero_of_germ_mem_maximalIdeal_of_not_mem_square
    (V : X.left.Opens) (z : ComplexPoint X)
    (hzV : z.underlying ∈ V) (s : Γ(X.left, V))
    (hs : X.left.presheaf.germ V z.underlying hzV s ∈
      maximalIdeal (X.left.presheaf.stalk z.underlying))
    (hs2 : X.left.presheaf.germ V z.underlying hzV s ∉
      (maximalIdeal (X.left.presheaf.stalk z.underlying)) ^ 2) :
    regularPointJet X d V z hzV s ≠ 0 := by
  let g := X.left.presheaf.germ V z.underlying hzV s
  have hg : g ∈ maximalIdeal (X.left.presheaf.stalk z.underlying) := hs
  have hg2 : g ∉ (maximalIdeal (X.left.presheaf.stalk z.underlying)) ^ 2 := hs2
  let D := ComplexPoint.localEtaleCoordinates X d z
  let hz : z.underlying ∈ D.neighborhood := D.mem
  let z' := (ComplexPoint.openHomeomorph X D.neighborhood).symm ⟨z, hz⟩
  let S := D.neighborhood.toScheme.presheaf.stalk z'.underlying
  let A := localSectionRing X d D
  let _ : Algebra ℂ (localSectionRing X d D) :=
    (D.coordinateRingHomOnOpen.comp MvPolynomial.C).toAlgebra
  let y : D.neighborhood := z'.underlying
  have hz' : Point.map (openInclusion X D.neighborhood) z' = z := by
    change (openHomeomorph X D.neighborhood z').1 = z
    exact congrArg Subtype.val
      ((openHomeomorph X D.neighborhood).apply_symm_apply ⟨z, hz⟩)
  have hy : y.1 = z.underlying := congrArg Point.underlying hz'
  let e : Inseparable z.underlying y.1 := .of_eq hy.symm
  let j := (X.left.presheaf.stalkCongr e).commRingCatIsoToRingEquiv
  let i0 := (D.neighborhood.stalkIso y).commRingCatIsoToRingEquiv
  let gy : X.left.presheaf.stalk y.1 := j g
  have hgy : gy ∈ maximalIdeal (X.left.presheaf.stalk y.1) := by
    have h := (RingEquiv.mem_maximalIdeal_pow_iff j g 1).mp
      (by simpa only [pow_one] using hg)
    simpa only [gy, pow_one] using h
  have hgy2 : gy ∉ (maximalIdeal (X.left.presheaf.stalk y.1)) ^ 2 := by
    intro h
    apply hg2
    change j g ∈ (maximalIdeal (X.left.presheaf.stalk y.1)) ^ 2 at h
    have h' := (RingEquiv.mem_maximalIdeal_pow_iff j g 2).mpr h
    simpa only [gy] using h'
  let t : S := i0.symm gy
  have hta : t ∈ maximalIdeal S := by
    have h := (RingEquiv.mem_maximalIdeal_pow_iff i0 t 1).mpr (by simpa [t] using hgy)
    simpa only [pow_one] using h
  have hta2 : t ∉ (maximalIdeal S) ^ 2 := by
    intro ht
    apply hgy2
    have h := (RingEquiv.mem_maximalIdeal_pow_iff i0 t 2).mp ht
    simpa [t] using h
  let P := residuePrimeIdeal X d D z hz
  let _ : IsAffine D.neighborhood.toScheme := D.isAffine
  let _ : P.IsPrime := by
    change (residuePrimeIdeal X d D z hz).IsPrime
    rw [← residueAlgHom_ker_eq_residuePrimeIdeal X d D z hz]
    exact RingHom.ker_isPrime (residueAlgHom X d D z hz).toRingHom
  let _ : (RingHom.ker (residueAlgHom X d D z hz).toRingHom).IsPrime :=
    RingHom.ker_isPrime (residueAlgHom X d D z hz).toRingHom
  let hzU : z'.underlying ∈ (⊤ : D.neighborhood.toScheme.Opens) := trivial
  let _ : Algebra A S :=
    TopCat.Presheaf.algebra_section_stalk D.neighborhood.toScheme.presheaf
      ⟨z'.underlying, hzU⟩
  let hU := isAffineOpen_top D.neighborhood.toScheme
  let _ : IsLocalization.AtPrime S P := by
    change IsLocalization.AtPrime S
      (hU.primeIdealOf ⟨z'.underlying, hzU⟩).asIdeal
    simpa only [S, z'] using hU.isLocalization_stalk ⟨z'.underlying, hzU⟩
  obtain ⟨u, hu⟩ := IsLocalization.surj P.primeCompl t
  let a : A := u.1
  let b : A := u.2
  have hfrac : t * algebraMap A S b = algebraMap A S a := by
    simpa only [a, b] using hu
  have hbP : b ∉ P := u.2.property
  have hres : Function.Surjective (residueAlgHom X d D z hz) := by
    intro c
    exact ⟨algebraMap ℂ A c, (residueAlgHom X d D z hz).commutes c⟩
  let _ : P.IsMaximal := by
    change (residuePrimeIdeal X d D z hz).IsMaximal
    rw [← residueAlgHom_ker_eq_residuePrimeIdeal X d D z hz]
    exact RingHom.ker_isMaximal_of_surjective
      (residueAlgHom X d D z hz).toRingHom hres
  let _ : (RingHom.ker (residueAlgHom X d D z hz).toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (residueAlgHom X d D z hz).toRingHom hres
  have hba : IsUnit (algebraMap A S b) := IsLocalization.map_units S u.2
  have haS : algebraMap A S a ∈ maximalIdeal S := by
    rw [← hfrac]
    exact (maximalIdeal S).mul_mem_right _ hta
  have haP : a ∈ P := by
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff S P a).mp
    exact haS
  have haLoc : algebraMap A (Localization.AtPrime
      (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) a ∈
      maximalIdeal (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) := by
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom))
      (RingHom.ker (residueAlgHom X d D z hz).toRingHom) a).mpr
    rw [residueAlgHom_ker_eq_residuePrimeIdeal X d D z hz]
    exact haP
  have haS2 : algebraMap A S a ∉ (maximalIdeal S)^2 := by
    intro h
    apply hta2
    have hunit := IsLocalization.map_units S u.2
    have h' : t = algebraMap A S a * (↑hunit.unit⁻¹ : S) := by
      apply hunit.mul_right_cancel
      rw [hfrac, mul_assoc, hunit.val_inv_mul, mul_one]
    rw [h']
    exact (maximalIdeal S ^ 2).mul_mem_right _ h
  have haP2 : a ∉ P^2 := by
    intro h
    apply haS2
    have h' := IsLocalization.AtPrime.under_maximalIdeal_pow P S 2
    rw [← Ideal.mem_under, h']
    exact h
  have haLoc2 : algebraMap A (Localization.AtPrime
      (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) a ∉
      (maximalIdeal (Localization.AtPrime
        (RingHom.ker (residueAlgHom X d D z hz).toRingHom)))^2 := by
    intro h
    apply haP2
    have h' := IsLocalization.AtPrime.under_maximalIdeal_pow
      (RingHom.ker (residueAlgHom X d D z hz).toRingHom)
      (Localization.AtPrime (RingHom.ker (residueAlgHom X d D z hz).toRingHom)) 2
    have hq : a ∈ (RingHom.ker (residueAlgHom X d D z hz).toRingHom)^2 := by
      rw [← h']
      exact h
    change a ∈ (residuePrimeIdeal X d D z hz)^2
    rw [← residueAlgHom_ker_eq_residuePrimeIdeal X d D z hz]
    exact hq
  have hda := localizedPointJetDerivation_ne_zero_of_not_mem_square_coordinate
    X d z a haLoc haLoc2
  have hpa : pointJet X d D z hz a ≠ 0 := by
    let q := RingHom.ker (residueAlgHom X d D z hz).toRingHom
    let _ : q.IsPrime := RingHom.ker_isPrime (residueAlgHom X d D z hz).toRingHom
    let _ : IsCentralScalar ℂ (PointJet d) :=
      { op_smul_eq_smul := by
          intro c m
          ext i
          simp }
    let _ : CommRing (TrivSqZeroExt ℂ (PointJet d)) := inferInstance
    let _ : Algebra ℂ (TrivSqZeroExt ℂ (PointJet d)) := inferInstance
    let _ : Module (Localization.AtPrime q) (PointJet d) := by
      let u :=
        (TrivSqZeroExt.fstHom ℂ ℂ (PointJet d)).comp
          (localizedPointJetAlgHom X d D z hz)
      exact Module.compHom (PointJet d) u.toRingHom
    let _ : IsScalarTower ℂ (Localization.AtPrime q) (PointJet d) := by
      let u :=
        (TrivSqZeroExt.fstHom ℂ ℂ (PointJet d)).comp
          (localizedPointJetAlgHom X d D z hz)
      constructor
      intro c a v
      change u (c • a) • v = c • u a • v
      rw [map_smul]
      simp only [smul_eq_mul, smul_smul]
    have hg := localizedPointJetAlgHom_comp X d D z hz
    have hga := congrArg
      (fun k : localSectionRing X d D →+* TrivSqZeroExt ℂ (PointJet d) ↦ k a) hg
    have hga' := congrArg TrivSqZeroExt.snd hga
    change localizedPointJetDerivation X d D z hz
        (algebraMap (localSectionRing X d D) (Localization.AtPrime q) a) =
      pointJet X d D z hz a at hga'
    exact hga'.symm ▸ hda
  change regularPointJet X d D.ambientCoordinateOpen z
      (mem_ambientCoordinateOpen X d D z hz) (ambientSection X d D a) ≠ 0 at hpa
  have hfrac' := hfrac
  change t * (D.neighborhood.toScheme.presheaf.germ ⊤ z'.underlying hzU b) =
      D.neighborhood.toScheme.presheaf.germ ⊤ z'.underlying hzU a at hfrac'
  have hia := ambientSection_germ_stalkIso X d z a
  have hib := ambientSection_germ_stalkIso X d z b
  have hfracY := congrArg i0 hfrac'
  rw [map_mul] at hfracY
  have hit : i0 t = gy := by simp [t]
  rw [hit, hia, hib] at hfracY
  have hj_res : ∀ (T : X.left.Opens) (r : Γ(X.left, T))
      (hzT : z.underlying ∈ T),
      j (X.left.presheaf.germ T z.underlying hzT r) =
        X.left.presheaf.germ T y.1 (by simpa [hy] using hzT) r := by
    intro T r hzT
    change ((X.left.presheaf.stalkCongr e).hom.hom
      (X.left.presheaf.germ T z.underlying hzT r)) = _
    dsimp [e, TopCat.Presheaf.stalkCongr]
    have hsp := TopCat.Presheaf.germ_stalkSpecializes
      X.left.presheaf hzT (x := y.1) e.ge
    have hsp' := congrArg (fun f => f.hom r) hsp
    simpa only [ConcreteCategory.comp_apply] using hsp'
  have hjg : j g = X.left.presheaf.germ V y.1 (by simpa [hy] using hzV) s := by
    exact hj_res V s hzV
  have hfracZ :
      X.left.presheaf.germ V z.underlying hzV s *
          X.left.presheaf.germ D.ambientCoordinateOpen z.underlying
            (mem_ambientCoordinateOpen X d D z hz)
            (ambientSection X d D b) =
        X.left.presheaf.germ D.ambientCoordinateOpen z.underlying
          (mem_ambientCoordinateOpen X d D z hz)
          (ambientSection X d D a) := by
    have hprodY :
        X.left.presheaf.germ V y.1 (by simpa [hy] using hzV) s *
            X.left.presheaf.germ D.ambientCoordinateOpen y.1
              (by simpa [hy] using mem_ambientCoordinateOpen X d D z hz)
              (ambientSection X d D b) =
          X.left.presheaf.germ D.ambientCoordinateOpen y.1
            (by simpa [hy] using mem_ambientCoordinateOpen X d D z hz)
            (ambientSection X d D a) := by
      rw [← hjg]
      exact hfracY
    have hprodZ := congrArg j.symm hprodY
    rw [map_mul] at hprodZ
    rw [show j.symm (X.left.presheaf.germ V y.1
          (by simpa [hy] using hzV) s) =
          X.left.presheaf.germ V z.underlying hzV s by
          rw [← hjg]; simp [g]] at hprodZ
    rw [show j.symm (X.left.presheaf.germ D.ambientCoordinateOpen y.1
          (by simpa [hy] using mem_ambientCoordinateOpen X d D z hz)
          (ambientSection X d D b)) =
          X.left.presheaf.germ D.ambientCoordinateOpen z.underlying
            (mem_ambientCoordinateOpen X d D z hz)
            (ambientSection X d D b) by
          rw [← hj_res D.ambientCoordinateOpen (ambientSection X d D b)
            (mem_ambientCoordinateOpen X d D z hz)]; simp] at hprodZ
    rw [show j.symm (X.left.presheaf.germ D.ambientCoordinateOpen y.1
          (by simpa [hy] using mem_ambientCoordinateOpen X d D z hz)
          (ambientSection X d D a)) =
          X.left.presheaf.germ D.ambientCoordinateOpen z.underlying
            (mem_ambientCoordinateOpen X d D z hz)
            (ambientSection X d D a) by
          rw [← hj_res D.ambientCoordinateOpen (ambientSection X d D a)
            (mem_ambientCoordinateOpen X d D z hz)]; simp] at hprodZ
    exact hprodZ
  let U := D.ambientCoordinateOpen
  let W := V ⊓ U
  let hzU : z.underlying ∈ U := mem_ambientCoordinateOpen X d D z hz
  let hzW : z.underlying ∈ W := ⟨hzV, hzU⟩
  let sW : Γ(X.left, W) := X.left.presheaf.map (homOfLE inf_le_left).op s
  let aW : Γ(X.left, W) :=
    X.left.presheaf.map (homOfLE inf_le_right).op (ambientSection X d D a)
  let bW : Γ(X.left, W) :=
    X.left.presheaf.map (homOfLE inf_le_right).op (ambientSection X d D b)
  have hprodW : X.left.presheaf.germ W z.underlying hzW (sW * bW) =
      X.left.presheaf.germ W z.underlying hzW aW := by
    dsimp [sW, aW, bW]
    rw [map_mul]
    rw [X.left.presheaf.germ_res_apply,
      X.left.presheaf.germ_res_apply, X.left.presheaf.germ_res_apply]
    exact hfracZ
  have hsval : Point.evaluate V s z = 0 := by
    rw [Point.evaluate, dif_pos hzV]
    by_contra hne
    have hunitval : IsUnit (z.stalkHom
        (X.left.presheaf.germ V z.underlying hzV s)) := by
      rw [isUnit_iff_ne_zero]
      exact hne
    have hunitg : IsUnit g := (isUnit_map_iff z.stalkHom.hom _).mp hunitval
    exact (IsLocalRing.mem_maximalIdeal g).mp hg hunitg
  have hjetW : regularPointJet X d W z hzW (sW * bW) =
      regularPointJet X d U z hzU (ambientSection X d D a) := by
    apply regularPointJet_eq_of_germ_eq X d W U z hzW hzU (sW * bW)
      (ambientSection X d D a)
    exact hprodW.trans (X.left.presheaf.germ_res_apply (homOfLE inf_le_right)
      z.underlying hzW (ambientSection X d D a))
  have hjetmul := regularPointJet_mul X d W z hzW sW bW
  have hsWval : Point.evaluate W sW z = Point.evaluate V s z := by
    rw [Point.evaluate_res inf_le_left s z hzW]
  have hbWval : Point.evaluate W bW z = Point.evaluate U
      (ambientSection X d D b) z := by
    rw [Point.evaluate_res inf_le_right (ambientSection X d D b) z hzW]
  have hjetEq : regularPointJet X d U z hzU (ambientSection X d D a) =
      Point.evaluate U (ambientSection X d D b) z •
        regularPointJet X d W z hzW sW := by
    rw [← hjetW, hjetmul, hsWval, hbWval, hsval]
    have hzero' : (0 : ℂ) • regularPointJet X d W z hzW bW = 0 := by
      ext x
      simp
    rw [hzero', zero_add]
  have hjetWne : regularPointJet X d W z hzW sW ≠ 0 := by
    intro hzero
    apply hpa
    rw [hjetEq, hzero]
    ext x
    simp
  have hjetVeq : regularPointJet X d V z hzV s =
      regularPointJet X d W z hzW sW := by
    apply regularPointJet_eq_of_germ_eq X d V W z hzV hzW s sW
    exact (X.left.presheaf.germ_res_apply (homOfLE inf_le_left)
      z.underlying hzW s).symm
  rw [hjetVeq]
  exact hjetWne

end Affine

end AlgebraicGeometry.ComplexPoint
