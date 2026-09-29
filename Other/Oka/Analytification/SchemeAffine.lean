/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.Scheme

/-!
# The analytification of an affine scheme is the zero locus of a presentation

Analytifications are unique up to unique isomorphism over the space they analytify
(`ComplexAnalytic.IsAnalytification.isoOfIsAnalytification`). For a presentation
`g₁, …, g_k ∈ ℂ[x₁, …, x_n]`, the analytification functor on schemes therefore sends
`Spec (ℂ[x] ⧸ (g))` to the zero locus `AnalyticSpace.analytification g` of `Other/Oka/Analytification/`,
compatibly with the comparison morphisms (`ComplexAnalytic.analytificationSpecIso`).
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace ComplexAnalytic

open AnalyticSpace

namespace IsAnalytification

variable {Y : Over specℂ} {W W' : AnalyticSpace.{u}} {π : toOverSpec.obj W ⟶ Y}
  {π' : toOverSpec.obj W' ⟶ Y}

/-- **Analytifications are unique**: two analytifications of the same object are isomorphic, by
the unique isomorphism compatible with the maps to it. -/
noncomputable def isoOfIsAnalytification (h : IsAnalytification π) (h' : IsAnalytification π') :
    W ≅ W' where
  hom := h'.lift π
  inv := h.lift π'
  hom_inv_id := h.hom_ext (by simp [Functor.map_comp])
  inv_hom_id := h'.hom_ext (by simp [Functor.map_comp])

@[reassoc (attr := simp)]
theorem isoOfIsAnalytification_hom_comp (h : IsAnalytification π)
    (h' : IsAnalytification π') :
    toOverSpec.map (isoOfIsAnalytification h h').hom ≫ π' = π :=
  h'.lift_fac π

@[reassoc (attr := simp)]
theorem isoOfIsAnalytification_inv_comp (h : IsAnalytification π)
    (h' : IsAnalytification π') :
    toOverSpec.map (isoOfIsAnalytification h h').inv ≫ π = π' :=
  h.lift_fac π'

end IsAnalytification

/-- `Spec R`, for a `ℂ`-algebra `R` of finite type, as a scheme locally of finite type over
`ℂ`. -/
noncomputable def SchemeLFTℂ.spec {R : CommRingCat.{u}} (φ : CommRingCat.of (ULift.{u} ℂ) ⟶ R)
    (hφ : φ.hom.FiniteType) : SchemeLFTℂ :=
  ⟨Over.mk (Spec.map φ), (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 hφ⟩

lemma schemeToOverSpec_obj_spec {R : CommRingCat.{u}} (φ : CommRingCat.of (ULift.{u} ℂ) ⟶ R)
    (hφ : φ.hom.FiniteType) : schemeToOverSpec.obj (SchemeLFTℂ.spec φ hφ).obj = specOver φ :=
  rfl

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- The structure map of a presented algebra is of finite type. -/
theorem finiteType_presentedAlgebraMap : (uliftAlgMap.{u} (presentedAlgebraMap g)).FiniteType := by
  refine RingHom.FiniteType.comp ?_
    (RingHom.FiniteType.of_surjective _ ULift.ringEquiv.surjective)
  refine RingHom.FiniteType.comp_surjective ?_ Ideal.Quotient.mk_surjective
  rw [← MvPolynomial.algebraMap_eq, RingHom.finiteType_algebraMap]
  infer_instance

/-- `Spec (ℂ[x] ⧸ (g))` as a scheme locally of finite type over `ℂ`. -/
noncomputable abbrev SchemeLFTℂ.specPresentation : SchemeLFTℂ :=
  SchemeLFTℂ.spec (CommRingCat.ofHom (uliftAlgMap (presentedAlgebraMap g)))
    (finiteType_presentedAlgebraMap g)

/-- **The analytification of `Spec (ℂ[x] ⧸ (g))` is the zero locus of `g`**, the isomorphism being
compatible with the comparison morphisms to `Spec (ℂ[x] ⧸ (g))`. -/
noncomputable def analytificationSpecIso :
    analytification.obj (SchemeLFTℂ.specPresentation g) ≅ AnalyticSpace.analytification g :=
  (isAnalytification_analytificationπ _).isoOfIsAnalytification
    (isAnalytification_analytificationToSpec g)

@[reassoc (attr := simp)]
theorem analytificationSpecIso_hom_comp :
    toOverSpec.map (analytificationSpecIso g).hom ≫ analytificationToSpecOver g =
      analytificationπ (SchemeLFTℂ.specPresentation g) :=
  IsAnalytification.isoOfIsAnalytification_hom_comp _ _

end ComplexAnalytic

end
