/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.FlasqueSections
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.FlasqueComparison
public import HodgeConjecture.Mathlib.Algebra.Homology.MapExtend

/-!
# Supported-section kernels and open restriction cones

For a termwise flasque coefficient complex, the kernel-defined supported section complex
computes the cone of restriction from `V` to `V ∩ U`, with the conventional degree shift.
The arrow identification displays the open-intersection map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- Let `X` be a topological space and `W ⊆ V` open subsets. This natural transformation sends a
sheaf of abelian groups `F` to its restriction map `F(V) → F(W)`. -/
def supportEvaluationRestriction {V W : Opens X} (i : W ⟶ V) :
    supportEvaluation X V ⟶ supportEvaluation X W where
  app F := F.obj.map i.op
  naturality _F _G f := (f.hom.naturality i.op).symm

/-- Let `X` be a topological space, `W ⊆ V` open subsets, and `K` a complex of sheaves of abelian
groups with any specified grading. This map of section complexes `K(V) → K(W)` restricts
sections in each degree. -/
def sectionComplexRestriction {I : Type*} (c : ComplexShape I)
    (K : HomologicalComplex (Sheaf AddCommGrpCat.{u} X) c)
    {V W : Opens X} (i : W ⟶ V) :
    ((supportEvaluation X V).mapHomologicalComplex c).obj K ⟶
      ((supportEvaluation X W).mapHomologicalComplex c).obj K :=
  ((supportEvaluationRestriction X i).mapHomologicalComplex c).app K

/-- Section restriction commutes with extension from natural to integer degrees. -/
theorem sectionComplexRestriction_extend
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ)
    {V W : Opens X} (i : W ⟶ V) :
    sectionComplexRestriction X ℤᵘᵖ (K.extend ComplexShape.embeddingUpNat) i ≫
      (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X W) K
        ComplexShape.embeddingUpNat).hom =
      (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X V) K
        ComplexShape.embeddingUpNat).hom ≫
      HomologicalComplex.extendMap (sectionComplexRestriction X (.up ℕ) K i)
        ComplexShape.embeddingUpNat :=
  HomologicalComplex.mapExtendCanonicalIso_natTrans (supportEvaluation X V) K
    ComplexShape.embeddingUpNat (supportEvaluationRestriction X i)

/-- Let `X` be a topological space, `W ⊆ V` open subsets, and `K` a nonnegative complex of sheaves
of abelian groups. The two ways to extend the restriction map `K(V) → K(W)` by zero to negative
degrees give canonically isomorphic mapping cones: extend the sheaf complex before taking
sections, or extend the resulting section complexes. -/
def sectionComplexRestrictionExtendConeIso
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ)
    {V W : Opens X} (i : W ⟶ V) :
    CochainComplex.mappingCone
      (sectionComplexRestriction X ℤᵘᵖ (K.extend ComplexShape.embeddingUpNat) i) ≅
      CochainComplex.mappingCone
        (HomologicalComplex.extendMap (sectionComplexRestriction X (.up ℕ) K i)
          ComplexShape.embeddingUpNat) :=
  HomologicalComplex.homotopyCofiber.mapArrowIso _ _
    (fun j => ⟨j - 1, ComplexShape.up_mk _ _ (by omega)⟩)
    (Arrow.isoMk
      (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X V) K
        ComplexShape.embeddingUpNat)
      (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X W) K
        ComplexShape.embeddingUpNat)
      (sectionComplexRestriction_extend X K i).symm)

variable (U V : Opens X) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- Let `X` be a topological space, `U` and `V` open subsets, and `K` an integer-indexed complex of
sheaves of abelian groups on `X`. For `j : U → X`, this is the degreewise identification `Γ(V,
j_*(K|_U)) ≅ K(V ∩ U)`. It identifies the last complex in the sequence of supported sections,
all sections, and restricted sections. -/
def supportRestrictionSectionsIntersectionIso :
    (supportRestrictionSectionsComplexShortComplex X U V K).X₃ ≅
      ((supportEvaluation X (V ⊓ U)).mapHomologicalComplex ℤᵘᵖ).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => supportedOutsideIntersectionIso X U V (K.X n))
    (fun n m _ => (K.d n m).hom.naturality
      (eqToHom (congrArg op (Opens.functor_map_eq_inf U V))))

/-- The intersection identification preserves the restriction arrow. -/
theorem supportRestrictionSectionsIntersectionIso_restriction :
    (supportRestrictionSectionsComplexShortComplex X U V K).g ≫
      (supportRestrictionSectionsIntersectionIso X U V K).hom =
        sectionComplexRestriction X ℤᵘᵖ K (Opens.infLELeft V U) :=
  HomologicalComplex.Hom.ext (funext fun n ↦
    toOpenRestrictionPushforward_intersection X U V (K.X n))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `X` be a topological space, `U` and `V` open subsets, and `K` an integer-indexed complex of
sheaves of abelian groups on `X`. The equality `Γ(V, j_*(K|_U)) ≅ K(V ∩ U)`, for `j : U → X`,
induces this isomorphism from the cone of `K(V) → Γ(V, j_*(K|_U))` to the cone of restriction
`K(V) → K(V ∩ U)`. -/
def supportRestrictionSectionsConeIso :
    CochainComplex.mappingCone (supportRestrictionSectionsComplexShortComplex X U V K).g ≅
      CochainComplex.mappingCone
        (sectionComplexRestriction X ℤᵘᵖ K (Opens.infLELeft V U)) :=
  HomologicalComplex.homotopyCofiber.mapArrowIso _ _
    (fun j => ⟨j - 1, ComplexShape.up_mk _ _ (by omega)⟩)
    (Arrow.isoMk (Iso.refl _) (supportRestrictionSectionsIntersectionIso X U V K)
      (by simpa using (supportRestrictionSectionsIntersectionIso_restriction X U V K).symm))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `X` be a topological space, `U` and `V` open subsets, and `K` an integer-indexed complex of
sheaves of abelian groups on `X`. Assume every term of `K` is flasque, so its restriction maps
are surjective. Then sections on `V` vanishing on `V ∩ U` form the kernel of a surjective map of
complexes. This gives the isomorphism `H^n(Γ_{X \ U}(V, K)) ≅ H^{n-1}(Cone(K(V) → K(V ∩ U)))`. -/
def supportedSectionHomologyIsoRestrictionCone
    (hK : ∀ n, (K.X n).IsFlasque) (n : ℤ) :
    -- `H^n(Γ_{X \ U}(V, K)) ≅ H^{n-1}(cone(K(V) → K(V ⊓ U)))`.
    -- `Γ_{X \ U}(V, K)`, the first term of `Γ_{X \ U}(V, K) → K(V) → K(V ⊓ U)`.
    (supportRestrictionSectionsComplexShortComplex X U V K).X₁.homology n ≅
      (CochainComplex.mappingCone
        -- The restriction `K(V) → K(V ⊓ U)`.
        (sectionComplexRestriction X ℤᵘᵖ K (Opens.infLELeft V U))).homology (n - 1) :=
  let S := supportRestrictionSectionsComplexShortComplex X U V K
  letI : QuasiIso (CochainComplex.mappingCocone.shiftedLiftShortComplex S) :=
    CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S
      (supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U V K hK)
  let e := ((HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0).shiftIso
    1 (n - 1) n (by omega)).app S.X₁
  e.symm ≪≫
    asIso (HomologicalComplex.homologyMap
      (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1)) ≪≫
    HomologicalComplex.homologyMapIso (supportRestrictionSectionsConeIso X U V K) (n - 1)

end TopCat.Sheaf
