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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SingularSheafComparison
public import Other.AlgebraicGeometry.Cohomology.GlobalSections
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.FlasqueQuasiIso
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.InjectiveFlasque
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.SubdivisionCochain
public import Other.AlgebraicTopology.Singular.Sheaf.CochainSubdivision
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Betti cohomology and global sections

This file identifies rational singular cohomology with the cohomology of the global-section
complex of the sheafified singular-cochain resolution on a paracompact Hausdorff space. It also
computes the hypercohomology of that resolution on a hereditarily paracompact Hausdorff space.

The derived comparison uses a bounded-below termwise-injective replacement. The mapping-cone
argument in `FlasqueQuasiIsoGlobalSections` proves that its quasi-isomorphism remains a
quasi-isomorphism after taking global sections. Thus no spectral sequence or acyclic-resolution
theorem is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace TopCat.Sheaf

section

variable {Y : TopCat.{0}}

/-- Morphisms from the constant integer sheaf are the same as global sections. This is the
degree-zero adjunction underlying the global-sections comparison below. -/
def integerConstantHomEquivGlobalSections
    (F : TopCat.Sheaf AddCommGrpCat Y) :
    ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ) ⟶ F) ≃
      F.obj.obj (.op (⊤ : Opens Y)) :=
  ((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat
      isTerminalTop).homEquiv (AddCommGrpCat.of ℤ) F).trans <|
    ConcreteCategory.homEquiv.trans (zmultiplesHom (F.obj.obj (.op ⊤))).symm

/-- The constant-integer/global-sections equivalence is natural in the sheaf. -/
lemma integerConstantHomEquivGlobalSections_naturality
    {F G : TopCat.Sheaf AddCommGrpCat Y} (f : F ⟶ G)
    (g : (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ) ⟶ F) :
    integerConstantHomEquivGlobalSections G (g ≫ f) =
      f.hom.app (.op (⊤ : Opens Y))
        (integerConstantHomEquivGlobalSections F g) := by
  have h := (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat
    isTerminalTop).homEquiv_naturality_right g f
  exact ConcreteCategory.congr_hom h (1 : ℤ)

end

end TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))


/-- If a K-injective resolution remains a quasi-isomorphism after taking global sections, then
the hypercohomology of the rational singular-cochain resolution is the homology of its own
global-section complex. The hypotheses are the precise resolution properties needed by the
construction; no acyclic-resolution theorem is assumed here. -/
def rationalSingularCochainHypercohomologyEquivGlobalSectionsOfResolution
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [I.IsKInjective]
    (i : singularCochainSheafComplexInt X ℚ ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map i)]
    (n : ℤ) :
    RationalSingularCochainHypercohomology X n ≃
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℚ)).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  let A := constantIntegerSheafComplexInt X
  let A' := TopCat.Sheaf.integerConstantSingleComplex Y
  let S := singularCochainSheafComplexInt X ℚ
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let e : A ≅ A' := constantIntegerSheafComplexIntIsoSingle X
  have hi : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) i := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have he : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) e.inv := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  let e₁ := Localization.SmallShiftedHom.postcompEquiv
    (X := A) (Y := S) (Z := I) (a := n) i hi
  let e₂ := Localization.SmallShiftedHom.precompEquiv
    (X := A') (Y := A) (Z := I) (a := n) e.inv he
  let e₃ := (CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective
    (K := A') (L := I) (n := n)).symm
  let e₄ := (CochainComplex.HomComplex.homologyAddEquiv A' I n).symm.toEquiv
  let e₅ := (HomologicalComplex.homologyMapIso
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y I) n)
      |>.addCommGroupIsoToAddEquiv.toEquiv
  let : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map i) := inferInstance
  let e₆ := (asIso (HomologicalComplex.homologyMap
    ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map i) n)).symm
      |>.addCommGroupIsoToAddEquiv.toEquiv
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans e₆))))

/-- On a hereditarily paracompact Hausdorff complex-point space, hypercohomology of the rational
singular-cochain resolution is computed by its global-section complex. This chooses Mathlib's
bounded-below termwise-injective replacement and proves that global sections preserve the
replacement quasi-isomorphism by the flasque mapping-cone argument. -/
def rationalSingularCochainHypercohomologyEquivGlobalSections
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) :
    RationalSingularCochainHypercohomology X n ≃
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℚ)).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  let S := singularCochainSheafComplexInt X ℚ
  let : S.IsStrictlyGE 0 := by
    dsimp [S, singularCochainSheafComplexInt]
    infer_instance
  let hres := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective S 0
  let I := Classical.choose hres
  let hresI := Classical.choose_spec hres
  let i := Classical.choose hresI
  let hresi := Classical.choose_spec hresI
  let hi : QuasiIso i := Classical.choose hresi
  let hresiHi := Classical.choose_spec hresi
  let hI : ∀ q : ℤ, Injective (I.X q) := Classical.choose hresiHi
  let hIge : I.IsStrictlyGE 0 := Classical.choose_spec hresiHi
  letI : QuasiIso i := hi
  letI : ∀ q : ℤ, Injective (I.X q) := hI
  letI : I.IsStrictlyGE 0 := hIge
  letI : I.IsKInjective := CochainComplex.isKInjective_of_injective I 0
  have hSflasque : ∀ q, (S.X q).IsFlasque :=
    fun q ↦ singularCochainSheafComplexInt_isFlasque X q
  have hIflasque : ∀ q, (I.X q).IsFlasque := fun _ ↦ inferInstance
  letI : QuasiIso
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i 0 0 hSflasque hIflasque
  exact rationalSingularCochainHypercohomologyEquivGlobalSectionsOfResolution
    X I i n

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicTopology.Singular

universe u

variable (R : Type u) [CommRing R] (Y : TopCat.{u})

set_option backward.isDefEq.respectTransparency false in
/-- The short complex controlling degree-`n` cohomology of the full linear-dual cochain complex
is the reversed dual of the degree-`n` singular-chain short complex. -/
def linearDualCochainComplexScIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    K.linearDualCochainComplex.sc n ≅ (K.sc n).linearDual := by
  let D := K.linearDualCochainComplex
  have hprev : (ComplexShape.up ℕ).prev n = (ComplexShape.down ℕ).next n := by
    cases n <;> simp
  have hnext : (ComplexShape.up ℕ).next n = (ComplexShape.down ℕ).prev n := by simp
  refine D.isoSc' ((ComplexShape.down ℕ).next n) n
      ((ComplexShape.down ℕ).prev n) hprev hnext ≪≫
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · cases n with
    | zero =>
        simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
          HomologicalComplex.shortComplexFunctor'_obj_f]
        dsimp only [ShortComplex.linearDual, ShortComplex.moduleCatMk,
          HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
          HomologicalComplex.shortComplexFunctor']
        rw [ChainComplex.next_nat_zero]
        change ModuleCat.ofHom (K.d 0 0).hom.dualMap = D.d 0 0
        rw [K.shape 0 0 (by simp), D.shape 0 0 (by simp)]
        exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ LinearMap.ext fun _ ↦ map_zero φ)
    | succ n =>
        simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
          HomologicalComplex.shortComplexFunctor'_obj_f]
        dsimp only [ShortComplex.linearDual, ShortComplex.moduleCatMk,
          HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
          HomologicalComplex.shortComplexFunctor']
        rw [ChainComplex.next_nat_succ]
        change ModuleCat.ofHom (K.d (n + 1) n).hom.dualMap = D.d n (n + 1)
        exact (HomologicalComplex.linearDualCochainComplex_d_succ K n).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
      HomologicalComplex.shortComplexFunctor'_obj_g]
    dsimp only [ShortComplex.linearDual, ShortComplex.moduleCatMk,
      HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor']
    rw [ChainComplex.prev]
    change ModuleCat.ofHom (K.d (n + 1) n).hom.dualMap = D.d n (n + 1)
    exact (HomologicalComplex.linearDualCochainComplex_d_succ K n).symm

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- On a hereditarily paracompact Hausdorff complex-point space, hypercohomology of the rational
singular-cochain resolution is the repository's existing rational singular cohomology type. -/
def rationalSingularCochainHypercohomologyEquivCohomology
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    RationalSingularCochainHypercohomology X (n : ℤ) ≃
      AlgebraicTopology.Singular.Cohomology ℚ
        (TopCat.of (ComplexPoint X)) n := by
  let Y := TopCat.of (ComplexPoint X)
  let K := AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℚ Y
  letI : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  exact (rationalSingularCochainHypercohomologyEquivGlobalSections
      X (n : ℤ)).trans <|
    (HomologicalComplex.homologyMapIso
      (globalSectionsSingularCochainComplexIntIsoExtend X)
        (n : ℤ)).addCommGroupIsoToAddEquiv.toEquiv |>.trans <|
      (K.extendHomologyIso ComplexShape.embeddingUpNat rfl).addCommGroupIsoToAddEquiv.toEquiv
        |>.trans <|
        (AlgebraicTopology.Singular.HereditarilyParacompact.ordinaryRationalSingularCohomologyEquivGlobalSections
          Y n).symm.toEquiv

/-- On a smooth complex scheme whose analytification is hereditarily paracompact Hausdorff,
rational constant-sheaf cohomology agrees with the repository's rational singular cohomology. -/
def rationalCohomologyEquivSingularCohomology
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    H^n(X; ℚ) ≃
      AlgebraicTopology.Singular.Cohomology ℚ
        (TopCat.of (ComplexPoint X)) n :=
  (rationalCohomologySingularCochainAddEquiv X n).toEquiv.trans
    (rationalSingularCochainHypercohomologyEquivCohomology X n)

end AlgebraicGeometry.ComplexPoint
