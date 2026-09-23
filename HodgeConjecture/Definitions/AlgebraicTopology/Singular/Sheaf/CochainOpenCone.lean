/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainOpenSections
public import HodgeConjecture.Lemmas.Algebra.Homology.MappingConeQuasiIso
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeCochainCone
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeCochainConeNaturality
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportSingularGlobal
public import HodgeConjecture.Lemmas.Algebra.Homology.MapExtendNaturality

/-! # Local singular-cochain restriction cones

The comparison is the cone map of the sheafification units and
restriction maps. Cone degree `n - 1` computes relative degree `n`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicTopology.Singular

variable (R : Type) [CommRing R] (X : TopCat.{0})

local instance singularCochainOpenConeDerivedCategory : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard AddCommGrpCat

/-- Let `R` be a commutative ring and `W ⊆ V` open subsets of a topological space `X`. This is the
mapping cone of singular-cochain restriction `C^*(V; R) → C^*(W; R)`. Both cochain complexes are
extended by zero to negative integer degrees before taking the cone; the cone itself can have a
term in degree `-1`. -/
def openRawSingularRestrictionCone {V W : Opens X} (i : W ⟶ V) :
    CochainComplex AddCommGrpCat ℤ :=
  CochainComplex.mappingCone
    (HomologicalComplex.extendMap (openRawSingularRestriction R X i)
      ComplexShape.embeddingUpNat)

/-- Let `R` be a commutative ring and `W ⊆ V` open subsets of a topological space `X`. Let `S^•` be
the sheafification on `X` of singular cochains. This is `Cone(Γ(V, S^•) → Γ(W, S^•))`, formed
after extending both section complexes by zero to negative integer degrees. -/
def openSingularSheafRestrictionCone {V W : Opens X} (i : W ⟶ V) :
    CochainComplex AddCommGrpCat ℤ :=
  CochainComplex.mappingCone
    (HomologicalComplex.extendMap (openSingularSheafRestriction R X i)
      ComplexShape.embeddingUpNat)

/-- The local sheafification restriction square, after extension by zero. -/
lemma openSingularSheafRestrictionInt_naturality {V W : Opens X} (i : W ⟶ V) :
    HomologicalComplex.extendMap (openRawSingularRestriction R X i)
        ComplexShape.embeddingUpNat ≫
      HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex R X W)
        ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex R X V)
        ComplexShape.embeddingUpNat ≫
      HomologicalComplex.extendMap (openSingularSheafRestriction R X i)
        ComplexShape.embeddingUpNat := by
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    openSingularSheafRestriction_naturality]

/-- Let `R` be a commutative ring and `W ⊆ V` open subsets of a topological space `X`. The maps
taking singular cochains to their sheafified sections on `V` and `W` commute with restriction.
This is the induced map from `Cone(C^*(V; R) → C^*(W; R))` to the cone of restriction of those
sheaf sections, in integer degrees. -/
def openRawToSingularSheafRestrictionCone {V W : Opens X} (i : W ⟶ V) :
    openRawSingularRestrictionCone R X i ⟶ openSingularSheafRestrictionCone R X i :=
  CochainComplex.mappingCone.map _ _
    (HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex R X V)
      ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex R X W)
      ComplexShape.embeddingUpNat)
    (openSingularSheafRestrictionInt_naturality R X i)

/-- Both local open spaces being paracompact Hausdorff suffices for the
cone comparison to be a quasi-isomorphism. -/
theorem openRawToSingularSheafRestrictionCone_quasiIso {V W : Opens X} (i : W ⟶ V)
    [ParacompactSpace V] [T2Space V] [ParacompactSpace W] [T2Space W] :
    QuasiIso (openRawToSingularSheafRestrictionCone ℚ X i) := by
  let := openRawToSingularCochainSheafComplex_quasiIso X V
  let := openRawToSingularCochainSheafComplex_quasiIso X W
  exact CochainComplex.mappingCone.map_quasiIso_of_vertical_quasiIso _ _ _ _ _

/-- Let `W ⊆ V` be open subsets of a topological space `X`. This is the topological pair `(V, W)`,
consisting of the two subspaces and their inclusion. -/
def openInclusionPair {V W : Opens X} (i : W ⟶ V) : TopPair :=
  TopPair.of ((Opens.toTopCat X).map i)
    (Topology.IsEmbedding.of_comp ((Opens.toTopCat X).map i).hom.continuous
      V.inclusion'.hom.continuous W.isOpenEmbedding.isEmbedding)

set_option backward.isDefEq.respectTransparency false in
/-- Let `R` be a commutative ring and `V` an open subset of a topological space `X`. This identifies
evaluation at `V` of the singular cochain presheaf complex with `Hom_R(C_*(V; R), R)`, viewed as
a complex of abelian groups. -/
def openRawSingularCochainComplexIsoDual (V : Opens X) :
    openRawSingularCochainComplex R X V ≅
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
        (SingularChainComplex R (TopCat.of V)).linearDualCochainComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (AddEquiv.refl (OpenCochains R X (.op V) n)).toAddCommGrpIso) (by
      intro n m h
      obtain rfl := h
      dsimp only [openRawSingularCochainComplex]
      rw [Functor.mapHomologicalComplex_obj_d,
        Functor.mapHomologicalComplex_obj_d,
        singularCochainPresheafComplex_d,
        HomologicalComplex.linearDualCochainComplex_d]
      ext φ
      rfl)

/-- The preceding identification preserves the dual of the
singular-chain inclusion of nested opens. -/
private lemma openRawSingularRestriction_transport {V W : Opens X} (i : W ⟶ V) :
    openRawSingularRestriction R X i ≫ (openRawSingularCochainComplexIsoDual R X W).hom =
      (openRawSingularCochainComplexIsoDual R X V).hom ≫
        ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
          (HomologicalComplex.linearDualMap
            ((chainPairFunctor R).obj (openInclusionPair X i)).hom) := rfl

/-- Let `R` be a commutative ring and `V` an open subset of a topological space `X`. This identifies
the integer-indexed extension of the singular cochains on `V` with the linear dual of its
singular chain complex extended to integer degrees, after forgetting the module structure. -/
def openRawSingularCochainComplexIntIsoDual (V : Opens X) :
    (openRawSingularCochainComplex R X V).extend ComplexShape.embeddingUpNat ≅
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex ℤᵘᵖ).obj
        ((SingularChainComplex R (TopCat.of V)).linearDualCochainComplex.extend
          ComplexShape.embeddingUpNat) :=
  (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).mapIso
    (openRawSingularCochainComplexIsoDual R X V) ≪≫
      (HomologicalComplex.mapExtendCanonicalIso (forget₂ (ModuleCat R) AddCommGrpCat)
        (SingularChainComplex R (TopCat.of V)).linearDualCochainComplex
        ComplexShape.embeddingUpNat).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The integer comparison preserves the original pair's restriction map. -/
lemma openRawSingularRestrictionInt_transport {V W : Opens X} (i : W ⟶ V) :
    HomologicalComplex.extendMap (openRawSingularRestriction R X i)
        ComplexShape.embeddingUpNat ≫
      (openRawSingularCochainComplexIntIsoDual R X W).hom =
    (openRawSingularCochainComplexIntIsoDual R X V).hom ≫
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex ℤᵘᵖ).map
        (relativeCochainRestrictionInt R (openInclusionPair X i)) := by
  dsimp only [openRawSingularCochainComplexIntIsoDual, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  change (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).map
    (openRawSingularRestriction R X i) ≫ _ = _
  rw [← Category.assoc, ← Functor.map_comp, openRawSingularRestriction_transport,
    Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg
    (fun f => HomologicalComplex.extendMap
      (openRawSingularCochainComplexIsoDual R X V).hom ComplexShape.embeddingUpNat ≫ f)
    (HomologicalComplex.mapExtendCanonicalIso_inv_naturality
      (forget₂ (ModuleCat R) AddCommGrpCat)
      (HomologicalComplex.linearDualMap
        ((chainPairFunctor R).obj (openInclusionPair X i)).hom)
      ComplexShape.embeddingUpNat)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let `R` be a commutative ring and `W ⊆ V` open subsets of a topological space `X`. This
identifies the cone formed from the presheaf restriction on singular cochains with the cone of
the dual chain map of the pair `(V, W)`, after forgetting the `R`-module structure. Both cones
use integer degrees. -/
def openRawSingularRestrictionConeIsoRelative {V W : Opens X} (i : W ⟶ V) :
    openRawSingularRestrictionCone R X i ≅
      CochainComplex.mappingCone
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex ℤᵘᵖ).map
          (relativeCochainRestrictionInt R (openInclusionPair X i))) :=
  HomologicalComplex.homotopyCofiber.mapArrowIso _ _
    (fun j => ⟨j - 1, ComplexShape.up_mk _ _ (by lia)⟩)
    (Arrow.isoMk (openRawSingularCochainComplexIntIsoDual R X V)
      (openRawSingularCochainComplexIntIsoDual R X W)
      (openRawSingularRestrictionInt_transport R X i).symm)

/-- Let `R` be a commutative ring and `W ⊆ V` open subsets of a topological space `X`. This additive
equivalence is `H^{n-1}(Cone(C^*(V; R) → C^*(W; R))) ≃ H^n(V, W; R)`, where the right side is
relative singular cohomology and the cone uses integer degrees. -/
def openRawSingularRestrictionConeCohomologyEquivRelative {V W : Opens X}
    (i : W ⟶ V) (n : ℕ) :
    (openRawSingularRestrictionCone R X i).homology ((n : ℤ) - 1) ≃+
      RelativeCohomology R (openInclusionPair X i) n :=
  (HomologicalComplex.homologyMapIso
    (openRawSingularRestrictionConeIsoRelative R X i) ((n : ℤ) - 1)).addCommGroupIsoToAddEquiv
    |>.trans <|
  (HomologicalComplex.homologyMapIso
    (CochainComplex.mappingCone.mapHomologicalComplexIso
      (relativeCochainRestrictionInt R (openInclusionPair X i))
      (forget₂ (ModuleCat R) AddCommGrpCat)).symm ((n : ℤ) - 1)).addCommGroupIsoToAddEquiv
    |>.trans <|
  (ShortComplex.mapHomologyIso
    ((CochainComplex.mappingCone
      (relativeCochainRestrictionInt R (openInclusionPair X i))).sc ((n : ℤ) - 1))
    (forget₂ (ModuleCat R) AddCommGrpCat)).addCommGroupIsoToAddEquiv
    |>.trans (relativeCochainConeCohomologyEquivCanonical R (openInclusionPair X i) n).toAddEquiv

/-- Let `W ⊆ V` be open subsets of a topological space `X`, with both subspaces paracompact and
Hausdorff. Let `S^•` be the sheafified rational singular cochain complex on `X`. This additive
equivalence identifies `H^{n-1}(Cone(Γ(V, S^•) → Γ(W, S^•)))` with relative singular cohomology
`H^n(V, W; ℚ)`. -/
def openSingularSheafRestrictionConeCohomologyEquivRelative {V W : Opens X}
    (i : W ⟶ V) [ParacompactSpace V] [T2Space V]
    [ParacompactSpace W] [T2Space W] (n : ℕ) :
    (openSingularSheafRestrictionCone ℚ X i).homology ((n : ℤ) - 1) ≃+
      RelativeCohomology ℚ (openInclusionPair X i) n :=
  letI := openRawToSingularSheafRestrictionCone_quasiIso X i
  (asIso (HomologicalComplex.homologyMap
    (openRawToSingularSheafRestrictionCone ℚ X i) ((n : ℤ) - 1))).symm.addCommGroupIsoToAddEquiv
    |>.trans (openRawSingularRestrictionConeCohomologyEquivRelative ℚ X i n)

end AlgebraicTopology.Singular
