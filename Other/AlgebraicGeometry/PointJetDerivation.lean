/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticSectionOfAlgebraic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Other.RingTheory.CotangentDetection

/-!
# Pointwise first jets of regular functions

This file records the first derivative of a regular function in the selected algebraic chart.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open Point
open scoped Manifold

variable (X : Over (Spec ↧ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

local instance pointJetTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology

abbrev PointJet := (Fin d → ℂ) →L[ℂ] ℂ

/-- The first jet of a regular section in the local chart at a complex point. -/
def regularPointJet (V : X.left.Opens) (z : ComplexPoint X)
    (_hz : z.underlying ∈ V) (s : Γ(X.left, V)) : PointJet d :=
  fderiv ℂ (fun w ↦ Point.evaluate V s ((localChart X d z).symm w))
    (localChart X d z z)

private lemma regularPointJet_analytic
    (V : X.left.Opens) (z : ComplexPoint X)
    (hz : z.underlying ∈ V) (s : Γ(X.left, V)) :
    AnalyticAt ℂ
      (fun w ↦ Point.evaluate V s ((localChart X d z).symm w))
      (localChart X d z z) := by
  apply analyticAt_localChart_symm_evaluate X d z
  · exact (localChart X d z).map_source (mem_localChart_source X d z)
  · rw [(localChart X d z).left_inv (mem_localChart_source X d z)]
    exact hz

lemma regularPointJet_add
    (V : X.left.Opens) (z : ComplexPoint X)
    (hz : z.underlying ∈ V) (s t : Γ(X.left, V)) :
    regularPointJet X d V z hz (s + t) =
      regularPointJet X d V z hz s + regularPointJet X d V z hz t := by
  have hs := regularPointJet_analytic X d V z hz s
  have ht := regularPointJet_analytic X d V z hz t
  let p := localChart X d z z
  have hp : p ∈ (localChart X d z).target :=
    (localChart X d z).map_source (mem_localChart_source X d z)
  have hleft : (localChart X d z).symm p = z := by
    exact (localChart X d z).left_inv (mem_localChart_source X d z)
  have hnhds : (localChart X d z).symm ⁻¹' (Point.overOpen V) ∈ 𝓝 p :=
    by
      have hV : (localChart X d z).symm p ∈ Point.overOpen V := by
        rw [hleft]
        change z.underlying ∈ V
        exact hz
      exact (localChart X d z).continuousAt_symm hp
        ((isOpen_overOpen V).mem_nhds hV)
  have heq :
      (fun w ↦ Point.evaluate V (s + t) ((localChart X d z).symm w)) =ᶠ[𝓝 p]
        (fun w ↦ Point.evaluate V s ((localChart X d z).symm w)) +
          (fun w ↦ Point.evaluate V t ((localChart X d z).symm w)) := by
    filter_upwards [hnhds] with w hw
    simp only [Pi.add_apply]
    rw [← Point.evaluationHom_apply V ⟨_, hw⟩]
    rw [← Point.evaluationHom_apply V ⟨_, hw⟩ s,
      ← Point.evaluationHom_apply V ⟨_, hw⟩ t]
    exact map_add (Point.evaluationHom V ⟨_, hw⟩).hom s t
  rw [regularPointJet, heq.fderiv_eq, fderiv_add hs.differentiableAt ht.differentiableAt]
  simp only [regularPointJet]

lemma regularPointJet_mul
    (V : X.left.Opens) (z : ComplexPoint X)
    (hz : z.underlying ∈ V) (s t : Γ(X.left, V)) :
    regularPointJet X d V z hz (s * t) =
      Point.evaluate V s z • regularPointJet X d V z hz t +
        Point.evaluate V t z • regularPointJet X d V z hz s := by
  have hs := regularPointJet_analytic X d V z hz s
  have ht := regularPointJet_analytic X d V z hz t
  let p := localChart X d z z
  have hp : p ∈ (localChart X d z).target :=
    (localChart X d z).map_source (mem_localChart_source X d z)
  have hleft : (localChart X d z).symm p = z := by
    exact (localChart X d z).left_inv (mem_localChart_source X d z)
  have hnhds : (localChart X d z).symm ⁻¹' (Point.overOpen V) ∈ 𝓝 p :=
    by
      have hV : (localChart X d z).symm p ∈ Point.overOpen V := by
        rw [hleft]
        change z.underlying ∈ V
        exact hz
      exact (localChart X d z).continuousAt_symm hp
        ((isOpen_overOpen V).mem_nhds hV)
  have heq :
      (fun w ↦ Point.evaluate V (s * t) ((localChart X d z).symm w)) =ᶠ[𝓝 p]
        (fun w ↦ Point.evaluate V s ((localChart X d z).symm w)) *
          (fun w ↦ Point.evaluate V t ((localChart X d z).symm w)) := by
    filter_upwards [hnhds] with w hw
    simp only [Pi.mul_apply]
    rw [← Point.evaluationHom_apply V ⟨_, hw⟩]
    rw [← Point.evaluationHom_apply V ⟨_, hw⟩ s,
      ← Point.evaluationHom_apply V ⟨_, hw⟩ t]
    exact map_mul (Point.evaluationHom V ⟨_, hw⟩).hom s t
  rw [regularPointJet, heq.fderiv_eq, fderiv_mul hs.differentiableAt ht.differentiableAt]
  rw [(localChart X d z).left_inv (mem_localChart_source X d z)]
  simp only [regularPointJet]


lemma regularPointJet_ambientCoordinateSection
    (z : ComplexPoint X) (i : Fin d) :
    let D := localEtaleCoordinates X d z
    let V := D.ambientCoordinateOpen
    let hz : z.underlying ∈ V := by
      change z ∈ Point.overOpen V
      have hmem := ComplexPoint.mem_localEtaleCoordinates X d z
      simpa only [V, D, LocalEtaleCoordinates.ambientCoordinateOpen,
        Scheme.Opens.ι_image_top] using hmem
    regularPointJet X d V z hz (D.ambientCoordinateSection i) =
      ContinuousLinearMap.proj i := by
  dsimp
  let D := localEtaleCoordinates X d z
  let V := D.ambientCoordinateOpen
  have hz : z.underlying ∈ V := by
    change z ∈ Point.overOpen V
    have hmem := ComplexPoint.mem_localEtaleCoordinates X d z
    simpa only [V, D, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using hmem
  let e := localChart X d z
  let p := e z
  have hp : p ∈ e.target := e.map_source (mem_localChart_source X d z)
  have heq :
      (fun w ↦ Point.evaluate V (D.ambientCoordinateSection i) (e.symm w)) =ᶠ[𝓝 p]
        (fun w ↦ w i) := by
    filter_upwards [e.open_target.mem_nhds hp] with w hw
    have hq : e.symm w ∈ e.source := e.map_target hw
    calc
      Point.evaluate V (D.ambientCoordinateSection i) (e.symm w) =
          e (e.symm w) i := by
            symm
            exact localChart_apply_component_eq_evaluate X d z (e.symm w) hq i
      _ = w i := by rw [e.right_inv hw]
  rw [regularPointJet, heq.fderiv_eq]
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) i).hasFDerivAt.fderiv

namespace Affine

variable {x : X.left} (D : LocalEtaleCoordinates X d x)

abbrev localSectionRing (D : LocalEtaleCoordinates X d x) := Γ(D.neighborhood.toScheme, ⊤)

noncomputable local instance coordinateRingComplexAlgebra :
    Algebra ℂ (localSectionRing X d D) :=
  (D.coordinateRingHomOnOpen.comp MvPolynomial.C).toAlgebra

noncomputable def ambientSection (a : localSectionRing X d D) :
    Γ(X.left, D.ambientCoordinateOpen) :=
  (D.neighborhood.ι.appIso ⊤).inv.hom a

lemma ambientSection_evaluate
    (z : ComplexPoint X) (hz : z.underlying ∈ D.neighborhood)
    (a : localSectionRing X d D) :
    Point.evaluate D.ambientCoordinateOpen (Affine.ambientSection X d D a) z =
      D.pointAlgHomHomeomorph
        ((ComplexPoint.openHomeomorph X D.neighborhood).symm ⟨z, hz⟩) a := by
  let z' := (ComplexPoint.openHomeomorph X D.neighborhood).symm ⟨z, hz⟩
  have hz' : Point.map (ComplexPoint.openInclusion X D.neighborhood) z' = z := by
    change (ComplexPoint.openHomeomorph X D.neighborhood z').1 = z
    exact congrArg Subtype.val
      ((ComplexPoint.openHomeomorph X D.neighborhood).apply_symm_apply ⟨z, hz⟩)
  have h := ComplexPoint.evaluate_openEquiv X D.neighborhood a z'
  rw [hz'] at h
  simpa only [ambientSection] using h.trans
      (D.pointAlgHomHomeomorph_apply z' a).symm

lemma mem_ambientCoordinateOpen
    (z : ComplexPoint X) (hz : z.underlying ∈ D.neighborhood) :
    z.underlying ∈ D.ambientCoordinateOpen := by
  simpa only [LocalEtaleCoordinates.ambientCoordinateOpen,
    Scheme.Opens.ι_image_top] using hz

def pointJet (z : ComplexPoint X)
    (hz : z.underlying ∈ D.neighborhood) (a : localSectionRing X d D) :
    PointJet d :=
  regularPointJet X d D.ambientCoordinateOpen z
    (mem_ambientCoordinateOpen X d D z hz) (ambientSection X d D a)

def residueAlgHom (z : ComplexPoint X)
    (hz : z.underlying ∈ D.neighborhood) :
    localSectionRing X d D →ₐ[ℂ] ℂ :=
  D.pointAlgHomHomeomorph
    ((ComplexPoint.openHomeomorph X D.neighborhood).symm ⟨z, hz⟩)

@[instance_reducible]
noncomputable def pointJetModule (z : ComplexPoint X)
    (hz : z.underlying ∈ D.neighborhood) :
    Module (localSectionRing X d D) (PointJet d) :=
  Module.compHom (PointJet d) (residueAlgHom X d D z hz).toRingHom

theorem pointJetScalarTower (z : ComplexPoint X)
    (hz : z.underlying ∈ D.neighborhood) :
    @IsScalarTower ℂ (localSectionRing X d D) (PointJet d) _
      ((pointJetModule X d D z hz).toDistribMulAction.toMulAction.toSMul) _ := by
  let : Module (localSectionRing X d D) (PointJet d) :=
    pointJetModule X d D z hz
  constructor
  intro c a v
  change (residueAlgHom X d D z hz (c • a)) • v =
    c • residueAlgHom X d D z hz a • v
  rw [map_smul]
  simp only [smul_eq_mul, smul_smul]

lemma pointJet_add
    (z : ComplexPoint X) (hz : z.underlying ∈ D.neighborhood)
    (a b : localSectionRing X d D) :
    pointJet X d D z hz (a + b) =
      pointJet X d D z hz a + pointJet X d D z hz b := by
  unfold pointJet
  rw [show ambientSection X d D (a + b) =
      ambientSection X d D a + ambientSection X d D b by
    exact (D.neighborhood.ι.appIso ⊤).inv.hom.map_add a b]
  exact regularPointJet_add X d D.ambientCoordinateOpen z
    (mem_ambientCoordinateOpen X d D z hz) _ _

lemma pointJet_mul
    (z : ComplexPoint X) (hz : z.underlying ∈ D.neighborhood)
    (a b : localSectionRing X d D) :
    pointJet X d D z hz (a * b) =
      (D.pointAlgHomHomeomorph
        ((ComplexPoint.openHomeomorph X D.neighborhood).symm ⟨z, hz⟩) a) •
          pointJet X d D z hz b +
        (D.pointAlgHomHomeomorph
          ((ComplexPoint.openHomeomorph X D.neighborhood).symm ⟨z, hz⟩) b) •
          pointJet X d D z hz a := by
  unfold pointJet
  rw [show ambientSection X d D (a * b) =
      ambientSection X d D a * ambientSection X d D b by
    exact (D.neighborhood.ι.appIso ⊤).inv.hom.map_mul a b]
  rw [regularPointJet_mul]
  rw [ambientSection_evaluate]
  rw [ambientSection_evaluate]

lemma pointJet_smul
    (z : ComplexPoint X) (hz : z.underlying ∈ D.neighborhood)
    (c : ℂ) (a : localSectionRing X d D) :
    pointJet X d D z hz (c • a) = c • pointJet X d D z hz a := by
  let V := D.ambientCoordinateOpen
  let e := localChart X d z
  let p := e z
  have hzV : z.underlying ∈ V := mem_ambientCoordinateOpen X d D z hz
  have hs := regularPointJet_analytic X d V z hzV
    (ambientSection X d D a)
  have hp : p ∈ e.target := e.map_source (mem_localChart_source X d z)
  have hleft : e.symm p = z := e.left_inv (mem_localChart_source X d z)
  have hnhds : e.symm ⁻¹' (Point.overOpen V) ∈ 𝓝 p := by
    have hV : e.symm p ∈ Point.overOpen V := by
      rw [hleft]
      change z.underlying ∈ V
      exact hzV
    exact e.continuousAt_symm hp ((isOpen_overOpen V).mem_nhds hV)
  have heq :
      (fun w ↦ Point.evaluate V (ambientSection X d D (c • a)) (e.symm w)) =ᶠ[𝓝 p]
        c • (fun w ↦ Point.evaluate V (ambientSection X d D a) (e.symm w)) := by
    filter_upwards [hnhds] with w hw
    have hw' : (e.symm w).underlying ∈ D.neighborhood := by
      change (e.symm w).underlying ∈ V at hw
      simpa only [V, LocalEtaleCoordinates.ambientCoordinateOpen,
        Scheme.Opens.ι_image_top] using hw
    change Point.evaluate V (ambientSection X d D (c • a)) (e.symm w) =
      c • Point.evaluate V (ambientSection X d D a) (e.symm w)
    rw [ambientSection_evaluate X d D (e.symm w) hw' (c • a)]
    rw [ambientSection_evaluate X d D (e.symm w) hw' a]
    have hy : e.symm w ∈ Point.overOpen D.neighborhood := hw'
    exact map_smul
      (D.pointAlgHomHomeomorph
        ((ComplexPoint.openHomeomorph X D.neighborhood).symm
          ⟨e.symm w, hy⟩)) c a
  unfold pointJet
  rw [regularPointJet, heq.fderiv_eq,
    fderiv_const_smul_field c]
  simp only [V, e, p]
  simp only [regularPointJet]
  rfl

def pointJetLinearMap (z : ComplexPoint X)
    (hz : z.underlying ∈ D.neighborhood) :
    localSectionRing X d D →ₗ[ℂ] PointJet d :=
  { toFun := pointJet X d D z hz
    map_add' := fun a b => pointJet_add X d D z hz a b
    map_smul' := fun c a => pointJet_smul X d D z hz c a }


noncomputable def pointJetDerivation (z : ComplexPoint X)
    (hz : z.underlying ∈ D.neighborhood) :
    @Derivation ℂ (localSectionRing X d D) (PointJet d) _ _ _ _
      (pointJetModule X d D z hz) _ := by
  letI : Module (localSectionRing X d D) (PointJet d) :=
    pointJetModule X d D z hz
  refine
    { toLinearMap := pointJetLinearMap X d D z hz
      map_one_eq_zero' := ?_
      leibniz' := ?_ }
  · let J := pointJet X d D z hz (1 : localSectionRing X d D)
    have h := pointJet_mul X d D z hz (1 : localSectionRing X d D) 1
    have h' : J + 0 = J + J := by
      simpa only [J, one_mul, map_one, one_smul, add_zero] using h
    exact (add_left_cancel h').symm
  · intro a b
    change pointJet X d D z hz (a * b) =
      (residueAlgHom X d D z hz a) • pointJet X d D z hz b +
        (residueAlgHom X d D z hz b) • pointJet X d D z hz a
    simpa only [residueAlgHom] using pointJet_mul X d D z hz a b

noncomputable def pointJetExtAlgHom (z : ComplexPoint X)
    (hz : z.underlying ∈ D.neighborhood) :
    letI : IsCentralScalar ℂ (PointJet d) :=
      { op_smul_eq_smul := by
          intro c m
          ext i
          simp }
    letI : CommRing (TrivSqZeroExt ℂ (PointJet d)) := inferInstance
    letI : Algebra ℂ (TrivSqZeroExt ℂ (PointJet d)) := inferInstance
    letI : Module (localSectionRing X d D) (PointJet d) :=
      pointJetModule X d D z hz
    letI : IsScalarTower ℂ (localSectionRing X d D) (PointJet d) :=
      pointJetScalarTower X d D z hz
    localSectionRing X d D →ₐ[ℂ] TrivSqZeroExt ℂ (PointJet d) := by
  letI : IsCentralScalar ℂ (PointJet d) :=
    { op_smul_eq_smul := by
        intro c m
        ext i
        simp }
  letI : CommRing (TrivSqZeroExt ℂ (PointJet d)) := inferInstance
  letI : Algebra ℂ (TrivSqZeroExt ℂ (PointJet d)) := inferInstance
  letI : Module (localSectionRing X d D) (PointJet d) :=
    pointJetModule X d D z hz
  letI : IsScalarTower ℂ (localSectionRing X d D) (PointJet d) :=
    pointJetScalarTower X d D z hz
  let u := residueAlgHom X d D z hz
  let δ := pointJetDerivation X d D z hz
  refine
    { toRingHom :=
        { toFun := fun a => ((u a, δ a) : TrivSqZeroExt ℂ (PointJet d))
          map_one' := by
            change (u 1, δ 1) = (1, 0)
            simp [δ, Derivation.map_one_eq_zero]
          map_mul' := by
            intro a b
            let x' : TrivSqZeroExt ℂ (PointJet d) := (u a, δ a)
            let y' : TrivSqZeroExt ℂ (PointJet d) := (u b, δ b)
            change (u (a * b), δ (a * b)) = x' * y'
            apply TrivSqZeroExt.ext
            · change u (a * b) = (x' * y').fst
              rw [TrivSqZeroExt.fst_mul]
              exact u.map_mul a b
            · change δ (a * b) = (x' * y').snd
              rw [TrivSqZeroExt.snd_mul]
              rw [δ.leibniz]
              change u a • δ b + u b • δ a = _
              simp [x', y']
          map_zero' := by
            change (u 0, δ 0) = (0, 0)
            simp [δ, Derivation.map_zero]
          map_add' := by
            intro a b
            change (u (a + b), δ (a + b)) = (u a + u b, δ a + δ b)
            congr 1
            · exact map_add u a b
            · exact δ.map_add a b }
      commutes' := by
        intro c
        change (u (algebraMap ℂ (localSectionRing X d D) c),
          δ (algebraMap ℂ (localSectionRing X d D) c)) = (c, 0)
        rw [u.commutes, δ.map_algebraMap]
        rfl }

/- The square-zero extension map extends to the local ring at the point.
The denominator condition is exactly that its residue coordinate is nonzero. -/
noncomputable def localizedPointJetAlgHom (z : ComplexPoint X)
    (hz : z.underlying ∈ D.neighborhood) :
    let q := RingHom.ker (residueAlgHom X d D z hz).toRingHom
    letI : q.IsPrime := RingHom.ker_isPrime (residueAlgHom X d D z hz).toRingHom
    Localization.AtPrime q →ₐ[ℂ] TrivSqZeroExt ℂ (PointJet d) := by
  let q := RingHom.ker (residueAlgHom X d D z hz).toRingHom
  letI : q.IsPrime := RingHom.ker_isPrime (residueAlgHom X d D z hz).toRingHom
  let f := pointJetExtAlgHom X d D z hz
  letI : Algebra (localSectionRing X d D) (TrivSqZeroExt ℂ (PointJet d)) :=
    f.toRingHom.toAlgebra
  letI : IsScalarTower ℂ (localSectionRing X d D)
      (TrivSqZeroExt ℂ (PointJet d)) := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    change algebraMap ℂ (TrivSqZeroExt ℂ (PointJet d)) c =
      f (algebraMap ℂ (localSectionRing X d D) c)
    apply TrivSqZeroExt.ext
    · simp [f]
    · rw [f.commutes]
  letI : IsLocalization q.primeCompl (Localization.AtPrime q) :=
    Localization.isLocalization
  let L : Localization.AtPrime q →+* TrivSqZeroExt ℂ (PointJet d) :=
    IsLocalization.lift (M := q.primeCompl) (S := Localization.AtPrime q)
      (g := f.toRingHom) (by
        intro s
        rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]
        intro hs
        apply s.2
        change (residueAlgHom X d D z hz) (s : localSectionRing X d D) = 0
        exact hs)
  letI : IsScalarTower ℂ (localSectionRing X d D)
      (Localization.AtPrime q) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    change algebraMap ℂ (Localization.AtPrime q) c =
      algebraMap (localSectionRing X d D) (Localization.AtPrime q)
        (D.coordinateRingHomOnOpen (MvPolynomial.C c))
    rfl
  refine { toRingHom := L, commutes' := ?_ }
  intro c
  change L (algebraMap ℂ (Localization.AtPrime q) c) =
    algebraMap ℂ (TrivSqZeroExt ℂ (PointJet d)) c
  calc
    L (algebraMap ℂ (Localization.AtPrime q) c) =
        L (algebraMap (localSectionRing X d D) (Localization.AtPrime q)
          (algebraMap ℂ (localSectionRing X d D) c)) := by
      exact congrArg L
        (IsScalarTower.algebraMap_apply ℂ (localSectionRing X d D)
          (Localization.AtPrime q) c).symm
    _ = f (algebraMap ℂ (localSectionRing X d D) c) := by
      rw [IsLocalization.lift_eq]
      rfl
    _ = algebraMap ℂ (TrivSqZeroExt ℂ (PointJet d)) c := f.commutes c

noncomputable def localizedPointJetDerivation (z : ComplexPoint X)
    (hz : z.underlying ∈ D.neighborhood) :
    let q := RingHom.ker (residueAlgHom X d D z hz).toRingHom
    letI : q.IsPrime := RingHom.ker_isPrime (residueAlgHom X d D z hz).toRingHom
    letI : IsCentralScalar ℂ (PointJet d) :=
      { op_smul_eq_smul := by
          intro c m
          ext i
          simp }
    letI : CommRing (TrivSqZeroExt ℂ (PointJet d)) := inferInstance
    letI : Algebra ℂ (TrivSqZeroExt ℂ (PointJet d)) := inferInstance
    letI : Module (Localization.AtPrime q) (PointJet d) := by
      let u :=
        (TrivSqZeroExt.fstHom ℂ ℂ (PointJet d)).comp
          (localizedPointJetAlgHom X d D z hz)
      exact Module.compHom (PointJet d) u.toRingHom
    letI : IsScalarTower ℂ (Localization.AtPrime q) (PointJet d) := by
      let u :=
        (TrivSqZeroExt.fstHom ℂ ℂ (PointJet d)).comp
          (localizedPointJetAlgHom X d D z hz)
      constructor
      intro c a v
      change u (c • a) • v = c • u a • v
      rw [map_smul]
      simp only [smul_eq_mul, smul_smul]
    @Derivation ℂ (Localization.AtPrime q) (PointJet d) _ _ _ _ _ _ := by
  let q := RingHom.ker (residueAlgHom X d D z hz).toRingHom
  letI : q.IsPrime := RingHom.ker_isPrime (residueAlgHom X d D z hz).toRingHom
  letI : IsCentralScalar ℂ (PointJet d) :=
    { op_smul_eq_smul := by
        intro c m
        ext i
        simp }
  letI : CommRing (TrivSqZeroExt ℂ (PointJet d)) := inferInstance
  letI : Algebra ℂ (TrivSqZeroExt ℂ (PointJet d)) := inferInstance
  let g := localizedPointJetAlgHom X d D z hz
  let u := (TrivSqZeroExt.fstHom ℂ ℂ (PointJet d)).comp g
  let δ : Localization.AtPrime q →ₗ[ℂ] PointJet d :=
    (TrivSqZeroExt.sndHom ℂ (PointJet d)).comp g.toLinearMap
  letI : Module (Localization.AtPrime q) (PointJet d) :=
    Module.compHom (PointJet d) u.toRingHom
  letI : IsScalarTower ℂ (Localization.AtPrime q) (PointJet d) := by
    constructor
    intro c a v
    change u (c • a) • v = c • u a • v
    rw [map_smul]
    simp only [smul_eq_mul, smul_smul]
  refine
    { toLinearMap := δ
      map_one_eq_zero' := ?_
      leibniz' := ?_ }
  · have h := congrArg TrivSqZeroExt.snd (g.map_one)
    change (g 1).snd = 0
    exact h
  · intro a b
    have h := congrArg TrivSqZeroExt.snd (g.map_mul a b)
    rw [TrivSqZeroExt.snd_mul] at h
    rw [op_smul_eq_smul] at h
    change δ (a * b) = u a • δ b + u b • δ a
    change (g (a * b)).snd = (g a).fst • (g b).snd + (g b).fst • (g a).snd
    change (g (a * b)).snd = (g a).fst • (g b).snd + (g b).fst • (g a).snd at h
    exact h

lemma localizedPointJetAlgHom_comp (z : ComplexPoint X)
    (hz : z.underlying ∈ D.neighborhood) :
    let q := RingHom.ker (residueAlgHom X d D z hz).toRingHom
    letI : q.IsPrime := RingHom.ker_isPrime (residueAlgHom X d D z hz).toRingHom
    (localizedPointJetAlgHom X d D z hz).toRingHom.comp
        (algebraMap (localSectionRing X d D) (Localization.AtPrime q)) =
      (pointJetExtAlgHom X d D z hz).toRingHom := by
  let q := RingHom.ker (residueAlgHom X d D z hz).toRingHom
  let : q.IsPrime := RingHom.ker_isPrime (residueAlgHom X d D z hz).toRingHom
  apply IsLocalization.lift_comp

lemma localizedPointJetDerivation_coordinate (z : ComplexPoint X) (i : Fin d) :
    let D := ComplexPoint.localEtaleCoordinates X d z
    let hz : z.underlying ∈ D.neighborhood := D.mem
    let q := RingHom.ker (residueAlgHom X d D z hz).toRingHom
    letI : q.IsPrime := RingHom.ker_isPrime (residueAlgHom X d D z hz).toRingHom
    letI : IsCentralScalar ℂ (PointJet d) :=
      { op_smul_eq_smul := by
          intro c m
          ext j
          simp }
    letI : CommRing (TrivSqZeroExt ℂ (PointJet d)) := inferInstance
    letI : Algebra ℂ (TrivSqZeroExt ℂ (PointJet d)) := inferInstance
    letI : Module (Localization.AtPrime q) (PointJet d) := by
      let u :=
        (TrivSqZeroExt.fstHom ℂ ℂ (PointJet d)).comp
          (localizedPointJetAlgHom X d D z hz)
      exact Module.compHom (PointJet d) u.toRingHom
    letI : IsScalarTower ℂ (Localization.AtPrime q) (PointJet d) := by
      let u :=
        (TrivSqZeroExt.fstHom ℂ ℂ (PointJet d)).comp
          (localizedPointJetAlgHom X d D z hz)
      constructor
      intro c a v
      change u (c • a) • v = c • u a • v
      rw [map_smul]
      simp only [smul_eq_mul, smul_smul]
    localizedPointJetDerivation X d D z hz
      (algebraMap (localSectionRing X d D) (Localization.AtPrime q)
        (D.coordinateRingHomOnOpen (MvPolynomial.X i))) =
      ContinuousLinearMap.proj i := by
  dsimp
  let D := ComplexPoint.localEtaleCoordinates X d z
  let hz : z.underlying ∈ D.neighborhood := D.mem
  let q := RingHom.ker (residueAlgHom X d D z hz).toRingHom
  let : q.IsPrime := RingHom.ker_isPrime (residueAlgHom X d D z hz).toRingHom
  let : IsCentralScalar ℂ (PointJet d) :=
    { op_smul_eq_smul := by
        intro c m
        ext j
        simp }
  let : CommRing (TrivSqZeroExt ℂ (PointJet d)) := inferInstance
  let : Algebra ℂ (TrivSqZeroExt ℂ (PointJet d)) := inferInstance
  let g := localizedPointJetAlgHom X d D z hz
  have hg := localizedPointJetAlgHom_comp X d D z hz
  have hxi := congrArg
    (fun k : localSectionRing X d D →+* TrivSqZeroExt ℂ (PointJet d) ↦
      k (D.coordinateRingHomOnOpen (MvPolynomial.X i))) hg
  let y : TrivSqZeroExt ℂ (PointJet d) :=
    g (algebraMap (localSectionRing X d D) (Localization.AtPrime q)
      (D.coordinateRingHomOnOpen (MvPolynomial.X i)))
  change TrivSqZeroExt.snd y = _
  have hy : y = pointJetExtAlgHom X d D z hz
      (D.coordinateRingHomOnOpen (MvPolynomial.X i)) := by
    change g (algebraMap (localSectionRing X d D) (Localization.AtPrime q)
      (D.coordinateRingHomOnOpen (MvPolynomial.X i))) = _ at hxi
    exact hxi
  rw [hy]
  change pointJet X d D z hz (D.coordinateRingHomOnOpen (MvPolynomial.X i)) = _
  exact regularPointJet_ambientCoordinateSection X d z i

end Affine

end AlgebraicGeometry.ComplexPoint
