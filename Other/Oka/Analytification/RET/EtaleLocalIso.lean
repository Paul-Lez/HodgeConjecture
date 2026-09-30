/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Other.Oka.Analytification.RET.SpecBridge
public import Other.Oka.Analytification.StandardEtaleLocalIsoBase
public import Other.Oka.Analytification.GAGA.OpenImmersion
public import Other.Oka.Analytification.GAGA.ClosedImmersion
public import Other.Oka.AnalyticSpace.LocalAtSource

/-!
# The analytification of an étale morphism is a local isomorphism

For a morphism `f : Y ⟶ X` of schemes locally of finite type over `ℂ` which is étale, the
analytification `f^an : Y^an ⟶ X^an` is a local isomorphism of complex analytic spaces
(`ComplexAnalytic.isLocalIso_analytification_map_of_etale`).

The proof reduces to the standard étale case, which is
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom`:

1. being a local isomorphism is local on the source, and the analytification of an open immersion
   is the inclusion of an open subspace, so it suffices that `(j ≫ f)^an` is a local isomorphism
   for open immersions `j` covering `Y`
   (`ComplexAnalytic.isLocalIso_analytification_map_of_forall_openImmersion`);
2. choosing affine opens `V ⊆ f⁻¹ U`, the question is about an étale morphism of affine schemes of
   finite type, i.e. `Spec` of an étale map of presented algebras;
3. such an algebra is standard étale locally on its spectrum
   (`Algebra.IsEtaleAt.exists_isStandardEtale`), and a standard étale algebra over a presented
   algebra is presented by `ComplexAnalytic.etalePresentation`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

/-! ### The structure map of the standard étale presentation -/

section StandardEtale

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (F G : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ)

/-- **`ComplexAnalytic.etalePresentedAlgebraEquivRing` is an isomorphism of algebras over the
base**: it carries the structure map `ComplexAnalytic.etalePresHom` to the structure map of
`StandardEtalePair.Ring`. -/
theorem etalePresentedAlgebraEquivRing_etalePresHom
    (P : StandardEtalePair (PresentedAlgebra.{u} n k g))
    (hF : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = P.f)
    (hG : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ G) = P.g)
    (r : PresentedAlgebra.{u} n k g) :
    etalePresentedAlgebraEquivRing.{u} g F G P hF hG ((etalePresHom.{u} g F G).toRingHom r) =
      algebraMap (PresentedAlgebra.{u} n k g) P.Ring r := by
  have key : (etalePresentedAlgebraEquivRing.{u} g F G P hF hG).toRingHom.comp
      (etalePresHom.{u} g F G).toRingHom = algebraMap (PresentedAlgebra.{u} n k g) P.Ring := by
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_))
    · have h1 : (etalePresHom.{u} g F G).toRingHom
          (Ideal.Quotient.mk _ (MvPolynomial.C c)) =
          algebraMap ℂ (PresentedAlgebra.{u} (n + 2) (k + 2) (etalePresentation.{u} g F G)) c := by
        change Ideal.Quotient.mk _ (MvPolynomial.rename _ (MvPolynomial.C c)) = _
        rw [MvPolynomial.rename_C]
        rfl
      change etalePresentedAlgebraEquivRing.{u} g F G P hF hG
        ((etalePresHom.{u} g F G).toRingHom (Ideal.Quotient.mk _ (MvPolynomial.C c))) = _
      rw [h1, AlgEquiv.commutes]
      change _ = algebraMap (PresentedAlgebra.{u} n k g) P.Ring
        (algebraMap ℂ (PresentedAlgebra.{u} n k g) c)
      rw [← IsScalarTower.algebraMap_apply]
    · have h1 : (etalePresHom.{u} g F G).toRingHom
          (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
          Ideal.Quotient.mk _ (MvPolynomial.rename (localisationIncl.{u} (n + 1))
            (MvPolynomial.rename (localisationIncl.{u} n) (MvPolynomial.X i))) := by
        change Ideal.Quotient.mk _ (MvPolynomial.rename _ (MvPolynomial.X i)) = _
        rw [MvPolynomial.rename_rename]
      change etalePresentedAlgebraEquivRing.{u} g F G P hF hG
        ((etalePresHom.{u} g F G).toRingHom (Ideal.Quotient.mk _ (MvPolynomial.X i))) = _
      rw [h1]
      change Ideal.Quotient.mk _ (biPolyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _
        (MvPolynomial.rename (localisationIncl.{u} (n + 1))
          (MvPolynomial.rename (localisationIncl.{u} n) (MvPolynomial.X i))))) = _
      rw [biPolyPresentedAlgebraEquiv_mk_rename, polyPresentedAlgebraEquiv_mk_rename]
      rfl
  exact RingHom.congr_fun key r

end StandardEtale

/-! ### Locality on the source -/

/-- **Being a local isomorphism after analytification is local on the source for open
immersions**: if every point of `Y` lies in the image of an open immersion `j : W ⟶ Y` with
`(j ≫ f)^an` a local isomorphism, then `f^an` is a local isomorphism. -/
theorem isLocalIso_analytification_map_of_forall_openImmersion {Y X : SchemeLFTℂ.{u}}
    (f : Y ⟶ X)
    (h : ∀ y : Y.obj.left, ∃ (W : SchemeLFTℂ.{u}) (j : W ⟶ Y), IsOpenImmersion j.hom.left ∧
      y ∈ Set.range j.hom.left.base ∧ IsLocalIso (analytification.map (j ≫ f))) :
    IsLocalIso (analytification.map f) := by
  choose W j hj hy hl using h
  let π : analytification.obj Y → Y.obj.left := fun p ↦ (analytificationπ Y).left.base p
  let V : analytification.obj Y → (analytification.obj Y).Opens := fun p ↦
    haveI := hj (π p)
    analytificationOpenImmersionPreimage (j (π p))
  have hV : IsOpenCover V := IsOpenCover.mk (eq_top_iff.2 fun p _ ↦ Opens.mem_iSup.2 ⟨p, by
    haveI := hj (π p)
    exact (mem_analytificationOpenImmersionPreimage_iff (j (π p)) p).2 (hy (π p))⟩)
  refine isLocalIso_of_isOpenCover_source _ V hV fun p ↦ ?_
  haveI := hj (π p)
  haveI := hl (π p)
  have e : (analytification.obj Y).ofRestrict (V p) ≫ analytification.map f =
      (analytificationOpenImmersionIso (j (π p))).inv ≫ analytification.map (j (π p) ≫ f) := by
    rw [Functor.map_comp, ← analytificationOpenImmersionIso_hom_ofRestrict (j (π p))]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  rw [e]
  haveI := isLocalIso_of_isIso (analytificationOpenImmersionIso (j (π p))).inv
  infer_instance

/-! ### The affine case -/

section Affine

variable {n k : ℕ} {g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ}

/-- **A standard étale algebra over a presented algebra analytifies to a local isomorphism**: if
`S` is isomorphic, as an algebra over `A = ℂ[x] ⧸ (g)`, to `StandardEtalePair.Ring`, then
`(Spec S ⟶ Spec A)^an` is a local isomorphism. -/
theorem isLocalIso_analytification_specHom_of_algEquiv {S : Type u} [CommRing S]
    [Algebra (PresentedAlgebra.{u} n k g) S] {φS : CommRingCat.of (ULift.{u} ℂ) ⟶ .of S}
    (hS : φS.hom.FiniteType)
    (h : CommRingCat.ofHom (uliftAlgMap.{u} (presentedAlgebraMap.{u} g)) ≫
      CommRingCat.ofHom (algebraMap (PresentedAlgebra.{u} n k g) S) = φS)
    (P : StandardEtalePair (PresentedAlgebra.{u} n k g))
    (e : S ≃ₐ[PresentedAlgebra.{u} n k g] P.Ring) :
    IsLocalIso (analytification.map (SchemeLFTℂ.specHom (finiteType_presentedAlgebraMap g) hS
      (CommRingCat.ofHom (algebraMap (PresentedAlgebra.{u} n k g) S)) h)) := by
  obtain ⟨F, hF⟩ := exists_lift_polyPresentedAlgebraEquiv.{u} g P.f
  obtain ⟨G, hG⟩ := exists_lift_polyPresentedAlgebraEquiv.{u} g P.g
  let e' := etalePresentedAlgebraEquivRing.{u} g F G P hF hG
  let E : CommRingCat.of (PresentedAlgebra.{u} (n + 2) (k + 2) (etalePresentation.{u} g F G)) ⟶
      CommRingCat.of S :=
    CommRingCat.ofHom (e'.toRingEquiv.trans e.symm.toRingEquiv).toRingHom
  haveI : IsIso E := ((e'.toRingEquiv.trans e.symm.toRingEquiv).toCommRingCatIso).isIso_hom
  have hE : CommRingCat.ofHom (etalePresHom.{u} g F G).toRingHom ≫ E =
      CommRingCat.ofHom (algebraMap (PresentedAlgebra.{u} n k g) S) := by
    refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
    change e.symm (e' ((etalePresHom.{u} g F G).toRingHom r)) =
      algebraMap (PresentedAlgebra.{u} n k g) S r
    rw [etalePresentedAlgebraEquivRing_etalePresHom, AlgEquiv.commutes]
  have hφ : CommRingCat.ofHom (uliftAlgMap.{u} (presentedAlgebraMap.{u}
      (etalePresentation.{u} g F G))) ≫ E = φS := by
    rw [← uliftAlgMap_comp_presHom (etalePresHom.{u} g F G), Category.assoc, hE, h]
  rw [← SchemeLFTℂ.specHom_comp_specHom (finiteType_presentedAlgebraMap g)
    (finiteType_presentedAlgebraMap _) hS _ E _ (uliftAlgMap_comp_presHom _) hφ h hE,
    Functor.map_comp]
  change IsLocalIso (_ ≫ analytification.map (specPresHom (etalePresHom.{u} g F G)))
  rw [analytification_map_specPresHom_eq]
  haveI := isLocalIso_analytificationMap_etalePresHom.{u} g F G P hF hG
  haveI := isLocalIso_of_isIso (analytificationSpecIso g).inv
  haveI := isLocalIso_of_isIso (analytificationSpecIso (etalePresentation.{u} g F G)).hom
  haveI := isLocalIso_of_isIso (analytification.map (SchemeLFTℂ.specHom
    (finiteType_presentedAlgebraMap (etalePresentation.{u} g F G)) hS E hφ))
  exact isLocalIso_comp _ _

variable {n' k' : ℕ} {g' : Fin k' → MvPolynomial (ULift.{u} (Fin n')) ℂ}

/-- **`Spec` of an étale map of presented algebras analytifies to a local isomorphism.** -/
theorem isLocalIso_analytification_specPresHom_of_etale (ψ : PresHom.{u} g' g)
    (hψ : ψ.toRingHom.Etale) : IsLocalIso (analytification.map (specPresHom ψ)) := by
  letI : Algebra (PresentedAlgebra.{u} n k g) (PresentedAlgebra.{u} n' k' g') :=
    ψ.toRingHom.toAlgebra
  haveI : Algebra.Etale (PresentedAlgebra.{u} n k g) (PresentedAlgebra.{u} n' k' g') := hψ
  refine isLocalIso_analytification_map_of_forall_openImmersion _ fun y ↦ ?_
  obtain ⟨a, ha, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale
    (R := PresentedAlgebra.{u} n k g) (y : PrimeSpectrum (PresentedAlgebra.{u} n' k' g')).asIdeal
  obtain ⟨Q⟩ := hstd.nonempty_standardEtalePresentation
  let Sa := Localization.Away a
  have hW : (CommRingCat.ofHom (uliftAlgMap.{u} (presentedAlgebraMap.{u} g')) ≫
      CommRingCat.ofHom (algebraMap (PresentedAlgebra.{u} n' k' g') Sa)).hom.FiniteType := by
    refine RingHom.FiniteType.comp ?_ (finiteType_presentedAlgebraMap g')
    haveI := IsLocalization.Away.finitePresentation (S := Sa) a
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have hjc : CommRingCat.ofHom (uliftAlgMap.{u} (presentedAlgebraMap.{u} g)) ≫
      CommRingCat.ofHom (algebraMap (PresentedAlgebra.{u} n k g) Sa) =
      CommRingCat.ofHom (uliftAlgMap.{u} (presentedAlgebraMap.{u} g')) ≫
        CommRingCat.ofHom (algebraMap (PresentedAlgebra.{u} n' k' g') Sa) := by
    rw [← uliftAlgMap_comp_presHom ψ, Category.assoc]
    congr 1
  let j := SchemeLFTℂ.specHom (finiteType_presentedAlgebraMap g') hW
    (CommRingCat.ofHom (algebraMap (PresentedAlgebra.{u} n' k' g') Sa)) rfl
  refine ⟨_, j, ?_, ?_, ?_⟩
  · change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap _ Sa)))
    infer_instance
  · change y ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap _ Sa))).base
    have := Scheme.Hom.opensRange_localizationAway
      (R := CommRingCat.of (PresentedAlgebra.{u} n' k' g')) a
    rw [← Scheme.Hom.coe_opensRange, this]
    exact ha
  · rw [specPresHom, SchemeLFTℂ.specHom_comp_specHom _ _ _ _ _
      (CommRingCat.ofHom (algebraMap (PresentedAlgebra.{u} n k g) Sa)) _ _ hjc
      (by ext1; exact (IsScalarTower.algebraMap_eq _ _ _).symm)]
    exact isLocalIso_analytification_specHom_of_algEquiv _ hjc Q.P Q.equivRing

/-- **An étale morphism of affine schemes of finite type over `ℂ` analytifies to a local
isomorphism.** -/
theorem isLocalIso_analytification_map_of_etale_of_isAffine {T S : SchemeLFTℂ.{u}} (φ : T ⟶ S)
    [IsAffine T.obj.left] [IsAffine S.obj.left] [Etale φ.hom.left] :
    IsLocalIso (analytification.map φ) := by
  obtain ⟨n, k, g, ⟨eS⟩⟩ := SchemeLFTℂ.exists_iso_specPresentation S
  obtain ⟨n', k', g', ⟨eT⟩⟩ := SchemeLFTℂ.exists_iso_specPresentation T
  obtain ⟨ψ, hψ⟩ := exists_specPresHom_eq (eT.hom ≫ φ ≫ eS.inv)
  have hφ : φ = eT.inv ≫ specPresHom ψ ≫ eS.hom := by simp [hψ]
  haveI : IsIso eT.hom.hom.left :=
    (Functor.map_isIso (locallyOfFiniteTypeℂ.ι ⋙ Over.forget _) eT.hom :)
  haveI : IsIso eS.inv.hom.left :=
    (Functor.map_isIso (locallyOfFiniteTypeℂ.ι ⋙ Over.forget _) eS.inv :)
  have het : Etale (Spec.map (CommRingCat.ofHom ψ.toRingHom)) := by
    rw [← specPresHom_hom_left, hψ]
    change Etale (eT.hom.hom.left ≫ φ.hom.left ≫ eS.inv.hom.left)
    infer_instance
  have hψe : ψ.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).1 het
  haveI := isLocalIso_analytification_specPresHom_of_etale ψ hψe
  haveI := isLocalIso_of_isIso (analytification.map eT.inv)
  haveI := isLocalIso_of_isIso (analytification.map eS.hom)
  rw [hφ, Functor.map_comp, Functor.map_comp]
  infer_instance

end Affine

/-! ### The general case -/

/-- **The analytification of an étale morphism is a local isomorphism.** -/
theorem isLocalIso_analytification_map_of_etale {Y X : SchemeLFTℂ.{u}} (f : Y ⟶ X)
    [Etale f.hom.left] : IsLocalIso (analytification.map f) := by
  refine isLocalIso_analytification_map_of_forall_openImmersion _ fun y ↦ ?_
  obtain ⟨U, hU⟩ := exists_affineOpens_mem X.obj.left (f.hom.left.base y)
  obtain ⟨V₀, hV, hyV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp Y.obj.left.isBasis_affineOpens)
    (show y ∈ f.hom.left ⁻¹ᵁ (U : X.obj.left.Opens) from hU)
  let V : Y.obj.left.affineOpens := ⟨V₀, hV⟩
  haveI : IsAffine (Y.restrict V).obj.left := V.2
  haveI : IsAffine (X.restrict U).obj.left := U.2
  let h : Y.restrict V ⟶ X.restrict U :=
    ObjectProperty.homMk (Over.homMk (f.hom.left.resLE U V hVU) (by
      change f.hom.left.resLE U V hVU ≫ (U : X.obj.left.Opens).ι ≫ X.obj.hom =
        (V : Y.obj.left.Opens).ι ≫ Y.obj.hom
      rw [Scheme.Hom.resLE_comp_ι_assoc, Over.w f.hom]))
  have hh : h ≫ X.restrictι U = Y.restrictι V ≫ f := by
    ext1
    exact Over.OverMorphism.ext (Scheme.Hom.resLE_comp_ι _ _)
  refine ⟨_, Y.restrictι V, ?_, ?_, ?_⟩
  · change IsOpenImmersion (V : Y.obj.left.Opens).ι
    infer_instance
  · change y ∈ Set.range (V : Y.obj.left.Opens).ι.base
    rw [Scheme.Opens.range_ι]
    exact hyV
  · rw [← hh, Functor.map_comp, analytification_map_restrictι]
    haveI : Etale h.hom.left := by
      change Etale (f.hom.left.resLE U V hVU)
      infer_instance
    haveI := isLocalIso_analytification_map_of_etale_of_isAffine h
    haveI := isLocalIso_of_isIso (analytificationRestrictIso X U).hom
    infer_instance

end

end ComplexAnalytic

end
