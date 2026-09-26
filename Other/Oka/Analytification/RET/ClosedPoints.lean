/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Field.ULift
public import Other.Oka.Analytification.RET.SpecBridge
public import Other.Oka.Analytification.GAGA.OpenImmersion
public import Other.Oka.Analytification.GAGA.ClosedImmersion

/-!
# The points of the analytification are the closed points

For a scheme `X` locally of finite type over `ℂ`, the comparison morphism `π : X^an ⟶ X` is a
bijection from the points of `X^an` onto the closed points of `X`.

For `X = Spec (ℂ[x] ⧸ (g))` the points of `X^an` are the common zeros `z` of `g`, sent to the
maximal ideals `ker (ev_z)`; that every maximal ideal is of this form is the Nullstellensatz
(`MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`). The general case follows by covering
`X` by open immersions from such spectra, since the analytification of an open immersion
`j : U ⟶ X` is an open embedding onto `π⁻¹(j(U))` and `X` is a Jacobson space, so that the closed
points of `U` are the points of `U` mapping to closed points of `X`.

## Main results

- `ComplexAnalytic.range_analytificationToSpec_base`: the image of `X^an ⟶ Spec (ℂ[x] ⧸ (g))` is
  the set of maximal ideals.
- `ComplexAnalytic.range_analytificationπ_base`: **the image of `π : X^an ⟶ X` is the set of
  closed points of `X`.**
- `ComplexAnalytic.analytificationπ_base_injective`: `π` is injective on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

/-- `ULift ℂ` is algebraically closed. -/
instance isAlgClosed_uliftComplex : IsAlgClosed (ULift.{u} ℂ) :=
  IsAlgClosed.of_exists_root _ fun p _ hirr ↦ by
    let f : ULift.{u} ℂ →+* ℂ := ULift.ringEquiv.toRingHom
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p.map f) (by
      rw [Polynomial.degree_map]; exact (Polynomial.degree_pos_of_irreducible hirr).ne')
    exact ⟨ULift.up z, (Polynomial.isRoot_map_iff (f := f) ULift.ringEquiv.injective).1 hz⟩

/-- **A scheme locally of finite type over `ℂ` is a Jacobson space.** -/
instance SchemeLFTℂ.jacobsonSpace (X : SchemeLFTℂ.{u}) : JacobsonSpace X.obj.left :=
  haveI : LocallyOfFiniteType X.obj.hom := X.property
  LocallyOfFiniteType.jacobsonSpace X.obj.hom

/-! ### The affine case -/

section Affine

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- **The image of `X^an ⟶ Spec (ℂ[x] ⧸ (g))` is the set of maximal ideals**, by the
Nullstellensatz: a maximal ideal of `ℂ[x]` containing `(g)` is the ideal of a common zero of
`g`. -/
theorem range_analytificationToSpec_base :
    Set.range (fun y : AnalyticSpace.analytification.{u} g ↦ (analytificationToSpec g).base y) =
      {p | p.asIdeal.IsMaximal} := by
  ext p
  constructor
  · rintro ⟨y, rfl⟩
    exact isMaximal_analytificationToSpec_base_asIdeal g y
  · intro (hp : p.asIdeal.IsMaximal)
    have hm : (p.asIdeal.comap (Ideal.Quotient.mk (presentationIdeal g))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨z, hz⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hm
    have hmem (r : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
        Ideal.Quotient.mk (presentationIdeal g) r ∈ p.asIdeal ↔ MvPolynomial.eval z r = 0 := by
      rw [← Ideal.mem_comap, hz, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      exact Iff.rfl
    have hg (j : Fin k) : Ideal.Quotient.mk (presentationIdeal g) (g j) ∈ p.asIdeal := by
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self j))]
      exact p.asIdeal.zero_mem
    let z' : complexAffineSpaceTop.{u} n := ⟨z, trivial⟩
    let y : AnalyticSpace.analytification.{u} g :=
      ⟨z', (mem_zeroLocus_polySection_iff g z').2 fun j ↦ (hmem (g j)).1 (hg j)⟩
    refine ⟨y, PrimeSpectrum.ext ?_⟩
    rw [analytificationToSpec_base_asIdeal]
    refine (hp.eq_of_le (RingHom.ker_ne_top _) fun q hq ↦ ?_).symm
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact RingHom.mem_ker.2 ((hmem r).1 hq)

/-- The comparison morphism of `Spec (ℂ[x] ⧸ (g))` on points is `X^an ⟶ Spec (ℂ[x] ⧸ (g))`, through
`ComplexAnalytic.analytificationSpecIso`. -/
lemma analytificationπ_specPresentation_base_apply
    (y : analytification.obj (SchemeLFTℂ.specPresentation g)) :
    (analytificationπ (SchemeLFTℂ.specPresentation g)).left.base y =
      (analytificationToSpec g).base ((analytificationSpecIso g).hom.toLRSHom.base y) := by
  rw [← analytificationSpecIso_hom_comp g]
  rfl

/-- The image of the comparison morphism of `Spec (ℂ[x] ⧸ (g))` is its set of closed points. -/
theorem range_analytificationπ_specPresentation_base :
    Set.range (analytificationπ (SchemeLFTℂ.specPresentation g)).left.base =
      closedPoints (SchemeLFTℂ.specPresentation g).obj.left := by
  have hb := (bijective_base_of_isIso (analytificationSpecIso g).hom).2
  ext p
  refine ⟨?_, fun hp ↦ ?_⟩
  · rintro ⟨y, rfl⟩
    rw [analytificationπ_specPresentation_base_apply]
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2
      (isMaximal_analytificationToSpec_base_asIdeal g _)
  · replace hp := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 hp
    obtain ⟨w, hw⟩ : p ∈ Set.range
        (fun y : AnalyticSpace.analytification.{u} g ↦ (analytificationToSpec g).base y) := by
      rw [range_analytificationToSpec_base]
      exact hp
    obtain ⟨y, rfl⟩ := hb w
    exact ⟨y, (analytificationπ_specPresentation_base_apply g y).trans hw⟩

/-- The comparison morphism of `Spec (ℂ[x] ⧸ (g))` is injective on points. -/
theorem analytificationπ_specPresentation_base_injective :
    Function.Injective (analytificationπ (SchemeLFTℂ.specPresentation g)).left.base := by
  intro y w h
  rw [analytificationπ_specPresentation_base_apply,
    analytificationπ_specPresentation_base_apply] at h
  exact (bijective_base_of_isIso (analytificationSpecIso g).hom).1
    (analytificationToSpec_base_injective g h)

end Affine

/-! ### The general case -/

/-- The comparison morphisms intertwine `f^an` and `f` on points. -/
lemma analytificationπ_base_map_apply {Y X : SchemeLFTℂ.{u}} (f : Y ⟶ X)
    (y : analytification.obj Y) :
    (analytificationπ X).left.base ((analytification.map f).toLRSHom.base y) =
      f.hom.left.base ((analytificationπ Y).left.base y) :=
  congrArg (fun φ ↦ φ.left.base y) (analytificationπ_naturality f)

/-- Every point of `X` lies in the image of an open immersion from `Spec (ℂ[x] ⧸ (g))` for some
presentation `g`. -/
lemma exists_openImmersion_specPresentation (X : SchemeLFTℂ.{u}) (x : X.obj.left) :
    ∃ (n k : ℕ) (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
      (j : SchemeLFTℂ.specPresentation g ⟶ X),
      IsOpenImmersion j.hom.left ∧ x ∈ Set.range j.hom.left.base := by
  obtain ⟨U, hU⟩ := exists_affineOpens_mem X.obj.left x
  haveI : IsAffine (X.restrict U).obj.left := U.2
  obtain ⟨n, k, g, ⟨e⟩⟩ := SchemeLFTℂ.exists_iso_specPresentation (X.restrict U)
  haveI : IsIso e.hom.hom.left :=
    (Functor.map_isIso (locallyOfFiniteTypeℂ.ι ⋙ Over.forget _) e.hom :)
  refine ⟨n, k, g, e.hom ≫ X.restrictι U, ?_, ?_⟩
  · haveI : IsOpenImmersion (X.restrictι U).hom.left :=
      (inferInstance : IsOpenImmersion (U : X.obj.left.Opens).ι)
    change IsOpenImmersion (e.hom.hom.left ≫ (X.restrictι U).hom.left)
    infer_instance
  · obtain ⟨v, rfl⟩ : x ∈ Set.range (U : X.obj.left.Opens).ι.base := by
      rw [Scheme.Opens.range_ι]
      exact hU
    obtain ⟨w, rfl⟩ := e.hom.hom.left.surjective v
    exact ⟨w, rfl⟩

/-- A point `y` of `X^an` over the image of an open immersion `j : U ⟶ X` comes from a point of
`U^an`. -/
lemma exists_analytification_map_eq_of_openImmersion {U X : SchemeLFTℂ.{u}} (j : U ⟶ X)
    [IsOpenImmersion j.hom.left] (y : analytification.obj X)
    (hy : (analytificationπ X).left.base y ∈ Set.range j.hom.left.base) :
    ∃ y' : analytification.obj U, (analytification.map j).toLRSHom.base y' = y := by
  have : y ∈ Set.range (analytification.map j).toLRSHom.base := by
    rw [range_analytification_map]
    exact hy
  exact this

/-- **The image of the comparison morphism `π : X^an ⟶ X` is the set of closed points of `X`.** -/
theorem range_analytificationπ_base (X : SchemeLFTℂ.{u}) :
    Set.range (analytificationπ X).left.base = closedPoints X.obj.left := by
  ext x
  obtain ⟨n, k, g, j, hj, u, rfl⟩ := exists_openImmersion_specPresentation X x
  have hc : j.hom.left.base u ∈ closedPoints X.obj.left ↔
      u ∈ closedPoints (SchemeLFTℂ.specPresentation g).obj.left := by
    rw [← j.hom.left.isOpenEmbedding.preimage_closedPoints]
    rfl
  refine Iff.trans ?_ hc.symm
  rw [← range_analytificationπ_specPresentation_base]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨y', rfl⟩ := exists_analytification_map_eq_of_openImmersion j y ⟨u, hy.symm⟩
    refine ⟨y', j.hom.left.isOpenEmbedding.injective ?_⟩
    rw [← hy, analytificationπ_base_map_apply]
  · rintro ⟨y', rfl⟩
    exact ⟨_, analytificationπ_base_map_apply j y'⟩

/-- **The comparison morphism `π : X^an ⟶ X` is injective on points.** -/
theorem analytificationπ_base_injective (X : SchemeLFTℂ.{u}) :
    Function.Injective (analytificationπ X).left.base := by
  intro y w h
  obtain ⟨n, k, g, j, hj, hx⟩ :=
    exists_openImmersion_specPresentation X ((analytificationπ X).left.base y)
  obtain ⟨y', rfl⟩ := exists_analytification_map_eq_of_openImmersion j y hx
  obtain ⟨w', rfl⟩ := exists_analytification_map_eq_of_openImmersion j w (h ▸ hx)
  rw [analytificationπ_base_map_apply, analytificationπ_base_map_apply] at h
  rw [analytificationπ_specPresentation_base_injective g (j.hom.left.isOpenEmbedding.injective h)]

/-- A point of `X` is the image of a point of `X^an` if and only if it is closed. -/
theorem mem_range_analytificationπ_base_iff (X : SchemeLFTℂ.{u}) (x : X.obj.left) :
    x ∈ Set.range (analytificationπ X).left.base ↔ IsClosed {x} := by
  rw [range_analytificationπ_base]
  rfl

end

end ComplexAnalytic

end
