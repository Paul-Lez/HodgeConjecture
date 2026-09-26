/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicAnalytificationComparison
public import Other.Oka.Analytification.AffineSpace
public import Other.Oka.AlgebraicGeometry.GammaSpecAdjunction
public import Other.Oka.AnalyticSpace.Evaluation

/-! Local chart compatibility for the project-specific holomorphic analytification. -/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

abbrev localChartLRS (z : ComplexPoint X) : LocallyRingedSpace :=
  (holomorphicLocallyRingedSpace X d).restrict
    (localChartSource X d z).isOpenEmbedding

def localChartToComplexAffineSpace (z : ComplexPoint X) :
    localChartLRS X d z ⟶ _root_.complexAffineSpace.{0} d :=
  (localChartLocallyRingedSpaceIso X d z).hom ≫
    (_root_.complexAffineSpace.{0} d).ofRestrict
      (localChartTargetULift X d z).isOpenEmbedding

def localToAlgebraic (z : ComplexPoint X) :
    localChartLRS X d z ⟶ X.left.toLocallyRingedSpace :=
  (holomorphicLocallyRingedSpace X d).ofRestrict
      (localChartSource X d z).isOpenEmbedding ≫
    analytificationToAlgebraic X d

lemma localToAlgebraic_range (z : ComplexPoint X) :
    Set.range (localToAlgebraic X d z).base ⊆
      Set.range (localEtaleCoordinates X d z).neighborhood.ι.toLRSHom.base := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  change w.1.underlying ∈ (localEtaleCoordinates X d z).neighborhood
  exact mem_coordinateNeighborhood_of_mem_localChart_source X d z w.1 w.2

def localAnalytificationToNeighborhood (z : ComplexPoint X) :
    localChartLRS X d z ⟶
      (localEtaleCoordinates X d z).neighborhood.toScheme.toLocallyRingedSpace :=
  LocallyRingedSpace.IsOpenImmersion.lift
    (localEtaleCoordinates X d z).neighborhood.ι.toLRSHom
    (localToAlgebraic X d z)
    (localToAlgebraic_range X d z)

@[reassoc (attr := simp)]
lemma localAnalytificationToNeighborhood_comp (z : ComplexPoint X) :
    localAnalytificationToNeighborhood X d z ≫
        (localEtaleCoordinates X d z).neighborhood.ι.toLRSHom =
      localToAlgebraic X d z :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

variable {X d} {x : X.left} (D : LocalEtaleCoordinates X d x)

def coordinateRingHomULift :
    MvPolynomial (ULift.{0} (Fin d)) ℂ →+*
      LocallyRingedSpace.Γ.obj (op D.neighborhood.toScheme.toLocallyRingedSpace) :=
  D.coordinateRingHomOnOpen.comp (MvPolynomial.rename ULift.down).toRingHom

def toCoordinateSpecULift : D.neighborhood.toScheme ⟶
    Spec (CommRingCat.of (MvPolynomial (ULift.{0} (Fin d)) ℂ)) :=
  D.neighborhood.toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (coordinateRingHomULift D))

lemma mem_toΓSpecFun_asIdeal_iff_not_isUnit
    (Y : LocallyRingedSpace) (y : Y) (r : LocallyRingedSpace.Γ.obj (op Y)) :
    r ∈ (Y.toΓSpecFun y).asIdeal ↔ ¬ IsUnit (Y.presheaf.Γgerm y r) := by
  rw [← not_iff_not, not_not]
  exact Y.notMem_prime_iff_unit_in_stalk r y

def pointEvaluationLRS (Y : Over (Spec ↧ℂ)) (z : ComplexPoint Y) :
    Y.left.toLocallyRingedSpace.presheaf.obj (op ⊤) →+* ℂ :=
  (Point.stalkHom z).hom.comp
    (Y.left.toLocallyRingedSpace.presheaf.Γgerm z.underlying).hom

lemma pointEvaluationLRS_eq_evaluate (Y : Over (Spec ↧ℂ))
    (z : ComplexPoint Y) (s : Γ(Y.left, ⊤)) :
    pointEvaluationLRS Y z s = Point.evaluate ⊤ s z := by
  rw [Point.evaluate, dif_pos (show z.underlying ∈ (⊤ : Y.left.Opens) from trivial)]
  rfl

lemma canonicalRestrictedComplexSpaceIso_base
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (U : Opens (ι → ℂ)) (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ))
    (w : ↑↑((complexSpace ι).restrict U.isOpenEmbedding).toPresheafedSpace) :
    ((Euclidean.canonicalRestrictedComplexSpaceIso φ U).hom.base w).1 =
      φ w.1 := by
  let E := Euclidean.canonicalRestrictedComplexSpaceIso φ U
  let f : (complexSpace ι).restrict U.isOpenEmbedding ⟶ complexSpace κ :=
    (complexSpace ι).ofRestrict U.isOpenEmbedding ≫
      (Euclidean.complexSpaceIso φ).hom
  let g : (complexSpace κ).restrict (φ.opensCongr U).isOpenEmbedding ⟶
      complexSpace κ :=
    (complexSpace κ).ofRestrict (φ.opensCongr U).isOpenEmbedding
  have H : Set.range f.base ⊆ Set.range g.base := by
    change Set.range (fun x : U ↦ φ x) ⊆
      Set.range (Subtype.val : φ.opensCongr U → κ → ℂ)
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨φ x, ?_⟩, rfl⟩
    simpa using x.2
  have hfg : E.hom ≫ g = f := by
    change LocallyRingedSpace.IsOpenImmersion.lift g f H ≫ g = f
    exact LocallyRingedSpace.IsOpenImmersion.lift_fac g f H
  have h := congrArg (fun q :
      (complexSpace ι).restrict U.isOpenEmbedding ⟶ complexSpace κ ↦
      q.base w) hfg
  change ((E.hom.base w).1 : κ → ℂ) = φ w.1 at h
  exact h

lemma localChartToComplexAffineSpace_base_apply (z : ComplexPoint X)
    (w : ↑↑(localChartLRS X d z).toPresheafedSpace)
    (i : ULift.{0} (Fin d)) :
    (localChartToComplexAffineSpace X d z).base w i =
      localChart X d z w.1 i.down := by
  change
    ((Euclidean.canonicalRestrictedComplexSpaceIso
      (finToULiftCoord d) (localChartTarget X d z)).hom.base
      ((localChartLocallyRingedSpaceIsoFin X d z).hom.base w)).1 i = _
  rw [canonicalRestrictedComplexSpaceIso_base]
  rfl

def coordinateAlgebraMap (D : LocalEtaleCoordinates X d x) :
    ℂ →+* Γ(D.neighborhood.toScheme, ⊤) :=
  D.coordinateRingHomOnOpen.comp MvPolynomial.C

lemma neighborhoodInclusion_isCLinear (D : LocalEtaleCoordinates X d x) :
    ComplexAnalytic.IsCLinearHom D.neighborhood.ι.toLRSHom
      (coordinateAlgebraMap D) (algebraicAlgebraMap X) := by
  intro c
  rw [algebraicAlgebraMap_eq_appTop]
  have h := D.C_comp_coordinateRingHomOnOpen
  have hc := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) c
  exact hc.symm

lemma localToAlgebraic_isCLinear (z : ComplexPoint X) :
    ComplexAnalytic.IsCLinearHom (localToAlgebraic X d z)
      ((holomorphicLocallyRingedSpace X d).resAlgMap ContMDiffMap.C
        (localChartSource X d z))
      (algebraicAlgebraMap X) := by
  exact (ComplexAnalytic.isCLinearHom_ofRestrict
    (holomorphicLocallyRingedSpace X d) ContMDiffMap.C
    (localChartSource X d z)).comp
      (analytificationToAlgebraic_isCLinear (X := X) (d := d))

lemma localAnalytificationToNeighborhood_isCLinear (z : ComplexPoint X) :
    ComplexAnalytic.IsCLinearHom (localAnalytificationToNeighborhood X d z)
      ((holomorphicLocallyRingedSpace X d).resAlgMap ContMDiffMap.C
        (localChartSource X d z))
      (coordinateAlgebraMap (localEtaleCoordinates X d z)) := by
  exact ComplexAnalytic.IsCLinearHom.of_comp
    (localAnalytificationToNeighborhood_comp X d z)
    (localToAlgebraic_isCLinear (X := X) (d := d) z)
    (neighborhoodInclusion_isCLinear (D := localEtaleCoordinates X d z))

lemma localChartToComplexAffineSpace_isCLinear (z : ComplexPoint X) :
    ComplexAnalytic.IsCLinearHom (localChartToComplexAffineSpace X d z)
      ((holomorphicLocallyRingedSpace X d).resAlgMap ContMDiffMap.C
        (localChartSource X d z))
      (Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (ULift.{0} (Fin d) → ℂ)))) := by
  exact (localChartLocallyRingedSpaceIso_isCLinear X d z).comp
    (ComplexAnalytic.isCLinearHom_ofRestrict
      (_root_.complexAffineSpace.{0} d)
      (Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (ULift.{0} (Fin d) → ℂ))))
      (localChartTargetULift X d z))

abbrev localChartAnalyticSpace (z : ComplexPoint X) :
    ComplexAnalytic.AnalyticSpace :=
  (holomorphicAnalyticSpace X d).restrict (localChartSource X d z)

abbrev localChartTargetAnalyticSpace (z : ComplexPoint X) :
    ComplexAnalytic.AnalyticSpace :=
  (ComplexAnalytic.AnalyticSpace.complexAffineSpace.{0} d).restrict
    (localChartTargetULift X d z)

lemma localChartLocallyRingedSpaceIso_inv_isCLinear (z : ComplexPoint X) :
    ComplexAnalytic.IsCLinearHom (localChartLocallyRingedSpaceIso X d z).inv
      (localChartTargetAnalyticSpace (X := X) (d := d) z).algebraMap
      (localChartAnalyticSpace (X := X) (d := d) z).algebraMap := by
  exact ComplexAnalytic.IsCLinearHom.of_comp
    (localChartLocallyRingedSpaceIso X d z).inv_hom_id
    (ComplexAnalytic.IsCLinearHom.id
      (localChartTargetAnalyticSpace (X := X) (d := d) z).algebraMap)
    (localChartLocallyRingedSpaceIso_isCLinear X d z)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
lemma localChart_eval_inv (z : ComplexPoint X)
    (y : localChartTargetAnalyticSpace (X := X) (d := d) z)
    (s : (localChartAnalyticSpace (X := X) (d := d) z).presheaf.obj (op ⊤)) :
    (localChartTargetAnalyticSpace (X := X) (d := d) z).eval (U := ⊤) y
        (show y ∈ (⊤ : Opens (localChartTargetAnalyticSpace
          (X := X) (d := d) z)) from trivial)
        (LocallyRingedSpace.Γ.map
          (localChartLocallyRingedSpaceIso X d z).inv.op s) =
      (localChartAnalyticSpace (X := X) (d := d) z).eval (U := ⊤)
        ((localChartLocallyRingedSpaceIso X d z).inv.base y)
        (show (localChartLocallyRingedSpaceIso X d z).inv.base y ∈
          (⊤ : Opens (localChartAnalyticSpace (X := X) (d := d) z)) from trivial) s := by
  exact ComplexAnalytic.AnalyticSpace.eval_c_app
    (Z := localChartTargetAnalyticSpace (X := X) (d := d) z)
    (W := localChartAnalyticSpace (X := X) (d := d) z) (U := ⊤)
    (localChartLocallyRingedSpaceIso X d z).inv
    (localChartLocallyRingedSpaceIso_inv_isCLinear (X := X) (d := d) z)
    y (show (localChartLocallyRingedSpaceIso X d z).inv.base y ∈
      (⊤ : Opens (localChartAnalyticSpace (X := X) (d := d) z)) from trivial) s

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
lemma localChart_section_ext (z : ComplexPoint X)
    {s t : (localChartLRS X d z).presheaf.obj (op ⊤)}
    (h : ∀ w : localChartAnalyticSpace (X := X) (d := d) z,
      (localChartAnalyticSpace (X := X) (d := d) z).eval (U := ⊤) w
          (show w ∈ (⊤ : Opens (localChartAnalyticSpace
            (X := X) (d := d) z)) from trivial) s =
        (localChartAnalyticSpace (X := X) (d := d) z).eval (U := ⊤) w
          (show w ∈ (⊤ : Opens (localChartAnalyticSpace
            (X := X) (d := d) z)) from trivial) t) : s = t := by
  let e := localChartLocallyRingedSpaceIso X d z
  have hinj : Function.Injective
      (LocallyRingedSpace.Γ.map e.inv.op).hom :=
    (ConcreteCategory.bijective_of_isIso _).injective
  apply hinj
  apply OkaRing.ext
  funext y
  obtain ⟨y', hy', right⟩ := y.2
  change localChartTargetAnalyticSpace (X := X) (d := d) z at y'
  let V : (ComplexAnalytic.AnalyticSpace.complexAffineSpace.{0} d).Opens :=
    localChartTargetULift X d z
  let y₀ : V.isOpenEmbedding.isOpenMap.functor.obj ⊤ :=
    ⟨V.inclusion' y', ⟨y', trivial, rfl⟩⟩
  have hy : y = y₀ := by
    apply Subtype.ext
    exact right.symm
  rw [hy]
  change OkaRing.evalHom
      (U := V.isOpenEmbedding.isOpenMap.functor.obj ⊤)
      (x := V.inclusion' y') ⟨y', trivial, rfl⟩
      (LocallyRingedSpace.Γ.map e.inv.op s) =
    OkaRing.evalHom
      (U := V.isOpenEmbedding.isOpenMap.functor.obj ⊤)
      (x := V.inclusion' y') ⟨y', trivial, rfl⟩
      (LocallyRingedSpace.Γ.map e.inv.op t)
  rw [← ComplexAnalytic.eval_restrict_complexAffineSpace V y'
      (LocallyRingedSpace.Γ.map e.inv.op s),
    ← ComplexAnalytic.eval_restrict_complexAffineSpace V y'
      (LocallyRingedSpace.Γ.map e.inv.op t)]
  change (localChartTargetAnalyticSpace (X := X) (d := d) z).eval
      (U := ⊤) y' (show y' ∈ (⊤ : Opens (localChartTargetAnalyticSpace
        (X := X) (d := d) z)) from trivial)
      (LocallyRingedSpace.Γ.map e.inv.op s) =
    (localChartTargetAnalyticSpace (X := X) (d := d) z).eval
      (U := ⊤) y' (show y' ∈ (⊤ : Opens (localChartTargetAnalyticSpace
        (X := X) (d := d) z)) from trivial)
      (LocallyRingedSpace.Γ.map e.inv.op t)
  change (localChartTargetAnalyticSpace (X := X) (d := d) z).eval
      (U := ⊤) y' (show y' ∈ (⊤ : Opens (localChartTargetAnalyticSpace
        (X := X) (d := d) z)) from trivial)
      (e.inv.c.app (op ⊤) s) =
    (localChartTargetAnalyticSpace (X := X) (d := d) z).eval
      (U := ⊤) y' (show y' ∈ (⊤ : Opens (localChartTargetAnalyticSpace
        (X := X) (d := d) z)) from trivial)
      (e.inv.c.app (op ⊤) t)
  have hs := localChart_eval_inv (X := X) (d := d) z y' s
  have ht := localChart_eval_inv (X := X) (d := d) z y' t
  exact hs.trans ((h (e.inv.base y')).trans ht.symm)

def localLeftCoordinateRingHom (z : ComplexPoint X) :
    MvPolynomial (ULift.{0} (Fin d)) ℂ →+*
      (localChartAnalyticSpace (X := X) (d := d) z).presheaf.obj (op ⊤) :=
  (okaGlobalOfMvPolynomial (ULift.{0} (Fin d)) ≫
    LocallyRingedSpace.Γ.map (localChartToComplexAffineSpace X d z).op).hom

def localRightCoordinateRingHom (z : ComplexPoint X) :
    MvPolynomial (ULift.{0} (Fin d)) ℂ →+*
      (localChartAnalyticSpace (X := X) (d := d) z).presheaf.obj (op ⊤) :=
  (CommRingCat.ofHom (coordinateRingHomULift (localEtaleCoordinates X d z)) ≫
    LocallyRingedSpace.Γ.map
      (localAnalytificationToNeighborhood X d z).op).hom

lemma leftComparison_eq_toSpecOfAlgMap (z : ComplexPoint X) :
    localChartToComplexAffineSpace X d z ≫
        complexSpaceToSpec (ULift.{0} (Fin d)) =
      LocallyRingedSpace.toSpecOfAlgMap
        (localChartAnalyticSpace (X := X) (d := d) z).toLocallyRingedSpace
        (localLeftCoordinateRingHom (X := X) (d := d) z) := by
  exact LocallyRingedSpace.comp_toSpecOfAlgMap
    (localChartToComplexAffineSpace X d z)
    (okaGlobalOfMvPolynomial (ULift.{0} (Fin d))).hom

lemma rightComparison_eq_toSpecOfAlgMap (z : ComplexPoint X) :
    localAnalytificationToNeighborhood X d z ≫
        (toCoordinateSpecULift (localEtaleCoordinates X d z)).toLRSHom =
      LocallyRingedSpace.toSpecOfAlgMap
        (localChartAnalyticSpace (X := X) (d := d) z).toLocallyRingedSpace
        (localRightCoordinateRingHom (X := X) (d := d) z) := by
  exact LocallyRingedSpace.comp_toSpecOfAlgMap
    (localAnalytificationToNeighborhood X d z)
    (coordinateRingHomULift (localEtaleCoordinates X d z))

lemma mem_toSpecOfAlgMap_base_iff_eval_eq_zero
    {R : Type} [CommRing R] (Z : ComplexAnalytic.AnalyticSpace)
    (a : R →+* LocallyRingedSpace.Γ.obj (op Z.toLocallyRingedSpace))
    (w : Z) (r : R) :
    r ∈ ((LocallyRingedSpace.toSpecOfAlgMap Z.toLocallyRingedSpace a).base w).asIdeal ↔
      Z.eval (U := ⊤) w (show w ∈ (⊤ : Z.Opens) from trivial) (a r) = 0 := by
  change r ∈ (PrimeSpectrum.comap a
    (Z.toLocallyRingedSpace.toΓSpecFun w)).asIdeal ↔ _
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    mem_toΓSpecFun_asIdeal_iff_not_isUnit]
  rw [← Z.evalStalk_ne_zero_iff_isUnit, not_ne_iff]
  rfl

lemma localLeftCoordinateRingHom_C (z : ComplexPoint X) (c : ℂ) :
    localLeftCoordinateRingHom (X := X) (d := d) z (MvPolynomial.C c) =
      (localChartAnalyticSpace (X := X) (d := d) z).algebraMap c := by
  change LocallyRingedSpace.Γ.map (localChartToComplexAffineSpace X d z).op
      (okaGlobalOfMvPolynomial (ULift.{0} (Fin d)) (MvPolynomial.C c)) = _
  rw [show okaGlobalOfMvPolynomial (ULift.{0} (Fin d)) (MvPolynomial.C c) =
    Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (ULift.{0} (Fin d) → ℂ))) c by
      exact (OkaRing.ofMvPolynomial
        (⊤ : Opens (ULift.{0} (Fin d) → ℂ))).commutes c]
  exact localChartToComplexAffineSpace_isCLinear (X := X) (d := d) z c

lemma localRightCoordinateRingHom_C (z : ComplexPoint X) (c : ℂ) :
    localRightCoordinateRingHom (X := X) (d := d) z (MvPolynomial.C c) =
      (localChartAnalyticSpace (X := X) (d := d) z).algebraMap c := by
  change LocallyRingedSpace.Γ.map (localAnalytificationToNeighborhood X d z).op
      (coordinateRingHomULift (localEtaleCoordinates X d z) (MvPolynomial.C c)) = _
  rw [show coordinateRingHomULift (localEtaleCoordinates X d z)
      (MvPolynomial.C c) = coordinateAlgebraMap (localEtaleCoordinates X d z) c by
    change (localEtaleCoordinates X d z).coordinateRingHomOnOpen
      ((MvPolynomial.rename ULift.down) (MvPolynomial.C c)) = _
    rw [MvPolynomial.rename_C]
    rfl]
  exact localAnalytificationToNeighborhood_isCLinear (X := X) (d := d) z c

lemma localChart_comparison_square_raw_base (z : ComplexPoint X) :
    (localChartToComplexAffineSpace X d z ≫
        complexSpaceToSpec (ULift.{0} (Fin d))).base =
      (localAnalytificationToNeighborhood X d z ≫
        (toCoordinateSpecULift (localEtaleCoordinates X d z)).toLRSHom).base := by
  ext w
  apply PrimeSpectrum.ext
  ext p
  let v : ULift.{0} (Fin d) → ℂ :=
    (localChartToComplexAffineSpace X d z).base w
  change p ∈ ((complexSpaceToSpec (ULift.{0} (Fin d))).base
      v).asIdeal ↔ _
  refine (mem_complexSpaceToSpec_base_asIdeal_iff
    v p).trans ?_
  let D := localEtaleCoordinates X d z
  let g := localAnalytificationToNeighborhood X d z
  let y : D.neighborhood.toScheme := g.base w
  let q : PrimeSpectrum (MvPolynomial (ULift.{0} (Fin d)) ℂ) :=
    (toCoordinateSpecULift D).base y
  change MvPolynomial.eval v p = 0 ↔ p ∈ q.asIdeal
  have hq : q =
      PrimeSpectrum.comap (coordinateRingHomULift D)
        (D.neighborhood.toScheme.toLocallyRingedSpace.toΓSpecFun y) := rfl
  rw [hq, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    mem_toΓSpecFun_asIdeal_iff_not_isUnit]
  have hw : w.1 ∈ Point.overOpen D.neighborhood :=
    mem_coordinateNeighborhood_of_mem_localChart_source X d z w.1 w.2
  let wz : ComplexPoint (ComplexPoint.openScheme X D.neighborhood) :=
    ComplexPoint.asOpenPoint X D.neighborhood w.1 hw
  have hy : wz.underlying = y := by
    apply Subtype.ext
    have hwz : Point.map (ComplexPoint.openInclusion X D.neighborhood) wz = w.1 := by
      exact congrArg Subtype.val
        ((ComplexPoint.openEquiv X D.neighborhood).apply_symm_apply ⟨w.1, hw⟩)
    have hwz' := congrArg Point.underlying hwz
    rw [Point.underlying_map] at hwz'
    have hgy := congrArg (fun f : localChartLRS X d z ⟶
        X.left.toLocallyRingedSpace ↦ f.base w)
      (localAnalytificationToNeighborhood_comp X d z)
    have hgy' : y.1 = w.1.underlying := by
      change y.1 = w.1.underlying at hgy
      exact hgy
    exact hwz'.trans hgy'.symm
  rw [← hy, ← isUnit_map_iff (Point.stalkHom wz).hom,
    isUnit_iff_ne_zero, not_ne_iff]
  let s : Γ(D.neighborhood.toScheme, ⊤) := coordinateRingHomULift D p
  change MvPolynomial.eval v p = 0 ↔
    pointEvaluationLRS (ComplexPoint.openScheme X D.neighborhood) wz s = 0
  rw [pointEvaluationLRS_eq_evaluate]

  have hring : MvPolynomial.eval v =
      (pointEvaluationLRS (ComplexPoint.openScheme X D.neighborhood) wz).comp
        (coordinateRingHomULift D) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [MvPolynomial.eval_C]
      change c = pointEvaluationLRS (ComplexPoint.openScheme X D.neighborhood) wz
        (coordinateRingHomULift D (MvPolynomial.C c))
      let sc : Γ(D.neighborhood.toScheme, ⊤) :=
        coordinateRingHomULift D (MvPolynomial.C c)
      change c = pointEvaluationLRS (ComplexPoint.openScheme X D.neighborhood) wz sc
      rw [pointEvaluationLRS_eq_evaluate]
      letI : Algebra ℂ Γ(D.neighborhood.toScheme, ⊤) :=
        (D.coordinateRingHomOnOpen.comp MvPolynomial.C).toAlgebra
      rw [← D.pointAlgHomHomeomorph_apply]
      have hsc : sc = algebraMap ℂ Γ(D.neighborhood.toScheme, ⊤) c := by
        change D.coordinateRingHomOnOpen
          ((MvPolynomial.rename ULift.down) (MvPolynomial.C c)) =
          (D.coordinateRingHomOnOpen.comp MvPolynomial.C) c
        rw [MvPolynomial.rename_C]
        rfl
      rw [hsc]
      exact (D.pointAlgHomHomeomorph wz).commutes c |>.symm
    · intro i
      rw [MvPolynomial.eval_X]
      change v i = pointEvaluationLRS (ComplexPoint.openScheme X D.neighborhood) wz
        (coordinateRingHomULift D (MvPolynomial.X i))
      let si : Γ(D.neighborhood.toScheme, ⊤) :=
        coordinateRingHomULift D (MvPolynomial.X i)
      change v i = pointEvaluationLRS (ComplexPoint.openScheme X D.neighborhood) wz si
      rw [pointEvaluationLRS_eq_evaluate]
      have hsi : si = D.coordinateRingHomOnOpen (MvPolynomial.X i.down) := by
        change D.coordinateRingHomOnOpen
          ((MvPolynomial.rename ULift.down) (MvPolynomial.X i)) = _
        rw [MvPolynomial.rename_X]
      rw [hsi]
      rw [← D.analyticCoordinates_apply_eq_evaluate wz i.down]
      dsimp [v]
      rw [localChartToComplexAffineSpace_base_apply]
      rw [localChart_apply_component_eq_evaluate X d z w.1 w.2 i.down]
      rw [← D.ambientAnalyticCoordinates_apply_eq_evaluate
        (⟨w.1, hw⟩ : {q : ComplexPoint X // q ∈ Point.overOpen D.neighborhood}) i.down]
      rfl
  rw [RingHom.congr_fun hring p]
  change pointEvaluationLRS (ComplexPoint.openScheme X D.neighborhood) wz s = 0 ↔
    Point.evaluate ⊤ s wz = 0
  rw [pointEvaluationLRS_eq_evaluate]

lemma localChart_coordinateRing_square (z : ComplexPoint X) :
    okaGlobalOfMvPolynomial (ULift.{0} (Fin d)) ≫
        LocallyRingedSpace.Γ.map (localChartToComplexAffineSpace X d z).op =
      CommRingCat.ofHom (coordinateRingHomULift (localEtaleCoordinates X d z)) ≫
        LocallyRingedSpace.Γ.map (localAnalytificationToNeighborhood X d z).op := by
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    change LocallyRingedSpace.Γ.map (localChartToComplexAffineSpace X d z).op
        (okaGlobalOfMvPolynomial (ULift.{0} (Fin d)) (MvPolynomial.C c)) =
      LocallyRingedSpace.Γ.map (localAnalytificationToNeighborhood X d z).op
        (coordinateRingHomULift (localEtaleCoordinates X d z) (MvPolynomial.C c))
    have hl := localChartToComplexAffineSpace_isCLinear (X := X) (d := d) z c
    have hr := localAnalytificationToNeighborhood_isCLinear
      (X := X) (d := d) z c
    rw [show okaGlobalOfMvPolynomial (ULift.{0} (Fin d)) (MvPolynomial.C c) =
      Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (ULift.{0} (Fin d) → ℂ))) c by
        exact (OkaRing.ofMvPolynomial
          (⊤ : Opens (ULift.{0} (Fin d) → ℂ))).commutes c]
    rw [show coordinateRingHomULift (localEtaleCoordinates X d z)
        (MvPolynomial.C c) =
      coordinateAlgebraMap (localEtaleCoordinates X d z) c by
        change (localEtaleCoordinates X d z).coordinateRingHomOnOpen
          ((MvPolynomial.rename ULift.down) (MvPolynomial.C c)) = _
        rw [MvPolynomial.rename_C]
        rfl]
    exact hl.trans hr.symm
  · intro i
    apply localChart_section_ext (X := X) (d := d) z
    intro w
    let Z := localChartAnalyticSpace (X := X) (d := d) z
    let L := localLeftCoordinateRingHom (X := X) (d := d) z
    let R := localRightCoordinateRingHom (X := X) (d := d) z
    let ev := Z.eval (U := ⊤) w
      (show w ∈ (⊤ : Z.Opens) from trivial)
    let a : ℂ := ev (L (MvPolynomial.X i))
    let p : MvPolynomial (ULift.{0} (Fin d)) ℂ :=
      MvPolynomial.X i - MvPolynomial.C a
    have hbase := localChart_comparison_square_raw_base (X := X) (d := d) z
    rw [leftComparison_eq_toSpecOfAlgMap (X := X) (d := d) z,
      rightComparison_eq_toSpecOfAlgMap (X := X) (d := d) z] at hbase
    have hpoint := congrArg (fun f ↦ f w) hbase
    have hmem :
        p ∈ ((LocallyRingedSpace.toSpecOfAlgMap Z.toLocallyRingedSpace
          (localLeftCoordinateRingHom (X := X) (d := d) z)).base w).asIdeal ↔
        p ∈ ((LocallyRingedSpace.toSpecOfAlgMap Z.toLocallyRingedSpace
          (localRightCoordinateRingHom (X := X) (d := d) z)).base w).asIdeal := by
      change p ∈ ((LocallyRingedSpace.toSpecOfAlgMap
          (localChartAnalyticSpace (X := X) (d := d) z).toLocallyRingedSpace
          (localLeftCoordinateRingHom (X := X) (d := d) z)).base w).asIdeal ↔
        p ∈ ((LocallyRingedSpace.toSpecOfAlgMap
          (localChartAnalyticSpace (X := X) (d := d) z).toLocallyRingedSpace
          (localRightCoordinateRingHom (X := X) (d := d) z)).base w).asIdeal
      let qL : PrimeSpectrum (MvPolynomial (ULift.{0} (Fin d)) ℂ) :=
        (LocallyRingedSpace.toSpecOfAlgMap
          (localChartAnalyticSpace (X := X) (d := d) z).toLocallyRingedSpace
          (localLeftCoordinateRingHom (X := X) (d := d) z)).base w
      let qR : PrimeSpectrum (MvPolynomial (ULift.{0} (Fin d)) ℂ) :=
        (LocallyRingedSpace.toSpecOfAlgMap
          (localChartAnalyticSpace (X := X) (d := d) z).toLocallyRingedSpace
          (localRightCoordinateRingHom (X := X) (d := d) z)).base w
      have hq : qL = qR := hpoint
      change p ∈ qL.asIdeal ↔ p ∈ qR.asIdeal
      exact hq ▸ Iff.rfl
    rw [mem_toSpecOfAlgMap_base_iff_eval_eq_zero
        (localChartAnalyticSpace (X := X) (d := d) z)
        (localLeftCoordinateRingHom (X := X) (d := d) z) w p,
      mem_toSpecOfAlgMap_base_iff_eval_eq_zero
        (localChartAnalyticSpace (X := X) (d := d) z)
        (localRightCoordinateRingHom (X := X) (d := d) z) w p] at hmem
    have hLC : L (MvPolynomial.C a) = Z.algebraMap a := by
      exact localLeftCoordinateRingHom_C (X := X) (d := d) z a
    have hRC : R (MvPolynomial.C a) = Z.algebraMap a := by
      exact localRightCoordinateRingHom_C (X := X) (d := d) z a
    have hLzero : ev (L p) = 0 := by
      calc
        ev (L p) = ev (L (MvPolynomial.X i) - L (MvPolynomial.C a)) := by
          dsimp only [p]
          rw [map_sub]
        _ = ev (L (MvPolynomial.X i)) - ev (L (MvPolynomial.C a)) := map_sub ev _ _
        _ = a - a := by
          rw [hLC, ComplexAnalytic.AnalyticSpace.eval_algebraMap]
        _ = 0 := sub_self a
    have hRzero : ev (R p) = 0 := hmem.mp hLzero
    have hRsub : ev (R (MvPolynomial.X i)) - a = 0 := by
      calc
        ev (R (MvPolynomial.X i)) - a =
            ev (R (MvPolynomial.X i)) - ev (R (MvPolynomial.C a)) := by
          rw [hRC, ComplexAnalytic.AnalyticSpace.eval_algebraMap]
        _ = ev (R (MvPolynomial.X i) - R (MvPolynomial.C a)) := (map_sub ev _ _).symm
        _ = ev (R p) := by
          apply congrArg ev
          dsimp only [p]
          rw [map_sub]
        _ = 0 := hRzero
    exact (sub_eq_zero.mp hRsub).symm

theorem localChart_comparison_square_raw (z : ComplexPoint X) :
    localChartToComplexAffineSpace X d z ≫
        complexSpaceToSpec (ULift.{0} (Fin d)) =
      localAnalytificationToNeighborhood X d z ≫
        (toCoordinateSpecULift (localEtaleCoordinates X d z)).toLRSHom := by
  let D := localEtaleCoordinates X d z
  change localChartToComplexAffineSpace X d z ≫
      (complexSpace (ULift.{0} (Fin d))).toΓSpec ≫
        Spec.locallyRingedSpaceMap (okaGlobalOfMvPolynomial (ULift.{0} (Fin d))) =
    localAnalytificationToNeighborhood X d z ≫
      D.neighborhood.toScheme.toLocallyRingedSpace.toΓSpec ≫
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom (coordinateRingHomULift D))
  rw [← Category.assoc, LocallyRingedSpace.toΓSpec_naturality,
    ← Category.assoc, LocallyRingedSpace.toΓSpec_naturality]
  simp only [Category.assoc]
  rw [← Spec.locallyRingedSpaceMap_comp]
  rw [localChart_coordinateRing_square]
  rw [Spec.locallyRingedSpaceMap_comp]
  rfl

end AlgebraicGeometry.ComplexPoint
