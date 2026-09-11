/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CycleComponentSheafClass
public import Other.AlgebraicGeometry.ClosedSupportCoheightDimension
public import Other.AlgebraicTopology.CohomologySheafSectionRestriction
public import Other.AlgebraicTopology.OpenRestrictedLowestCohomologyNormalization
public import HodgeConjecture.Lemmas.AlgebraicGeometry.CycleComponentDimension

/-!
# Restriction of the local relative-cohomology sheaf away from a small closed subset

Let `Z = Z_x` be the component of a point `x` of coheight `p`, `U` its smooth-support open
`cycleComponentSmoothSupportAmbientOpen X x`, and `B ⊆ Z_x` a Zariski-closed subset not
containing the generic point `x`. Every point of `B` is then a proper specialisation of `x`, so
has coheight at least `p + 1`; the same holds for the singular boundary of `Z_x`. The supported
cohomology of `X^an` along the analytic support of `B' = (singular boundary) ⊔ B` therefore
vanishes in all degrees `< 2(p + 1)` (`closedSupportSectionCohomology_isZero_of_lt`), and the
nested-support localisation sequence

  `Γ_{B'^an}(X, I•) → Γ_{Z}(X, I•) → Γ_{Z}(U', I•)`,   `U' = U ∖ B^an = X ∖ B'^an`,

shows that restriction from `Γ_Z(X, I•)` to `Γ_Z(U', I•)` is injective on `H^{2p}`. Since
restriction to `U` is an isomorphism on `H^{2p}` (`cycleComponentSupportSectionRestriction_homology_isIso`),
restriction from `U` to `U'` is injective on `H^{2p}`, and the canonical comparison
`sectionCohomologyToSheafSection` — an isomorphism on both `U` and `U'` by the lowest-degree
purity along the smooth locus — transports this to the sheaf
`supportRelativeCohomologySheaf … (2p)`:

`cycleComponentSmoothSupport_restriction_injective` — restriction of sections of the local
relative-cohomology sheaf from `U` to `U ∖ B^an` is **injective**.

This is the gluing lemma that lets the winding-chart obligation of
`Other/AlgebraicGeometry/ChernLocalModelWinding.lean` be required only off a Zariski-closed subset
of `Z_x` of codimension at least one in `Z_x` (`HasNormalizedWindingCharts`), instead of at every
point of `U ∩ Z_x`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open AlgebraicTopology.Singular

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- Actual section restriction along a composite of open inclusions. -/
theorem sectionComplexRestriction_comp' {I : Type*} (c : ComplexShape I)
    (K : HomologicalComplex (Sheaf AddCommGrpCat.{u} X) c)
    {U V W : Opens X} (i : V ⟶ U) (j : W ⟶ V) (k : W ⟶ U) :
    sectionComplexRestriction X c K k =
      sectionComplexRestriction X c K i ≫ sectionComplexRestriction X c K j := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (K.X n).obj.map k.op = (K.X n).obj.map i.op ≫ (K.X n).obj.map j.op
  rw [← Functor.map_comp]
  congr 1

/-- Vanishing of supported section cohomology transports along an equality of the opens. -/
theorem supportedSections_homology_isZero_congr {W W' : Opens X} (hW : W = W')
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) (n : ℤ)
    (h : IsZero ((((supportEvaluation X ⊤).mapHomologicalComplex (.up ℤ)).obj
      (((sheafSectionsSupportedOutside X W).mapHomologicalComplex (.up ℤ)).obj K)).homology n)) :
    IsZero ((((supportEvaluation X ⊤).mapHomologicalComplex (.up ℤ)).obj
      (((sheafSectionsSupportedOutside X W').mapHomologicalComplex (.up ℤ)).obj K)).homology n) := by
  subst hW
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- If the supported section cohomology along the complement of `U` vanishes in degree `n`, then
restriction from global sections to sections on `U`, for the sheaves supported outside `V ⊆ U`,
is injective on `H^n`. This is the "mono" half of
`nestedSupportRestriction_homologyMap_isIso_of_vanishing`, for flasque coefficients. -/
theorem nestedSupportRestriction_homologyMap_top_mono_of_vanishing
    {U V : Opens X} (h : V ≤ U) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)
    (hK : ∀ n, (K.X n).IsFlasque) (n : ℤ)
    (hsmall : IsZero ((((supportEvaluation X ⊤).mapHomologicalComplex (.up ℤ)).obj
      (((sheafSectionsSupportedOutside X U).mapHomologicalComplex (.up ℤ)).obj K)).homology n)) :
    Mono (HomologicalComplex.homologyMap
      (sectionComplexRestriction X (.up ℤ)
        (((sheafSectionsSupportedOutside X V).mapHomologicalComplex (.up ℤ)).obj K)
        (homOfLE (le_top : U ≤ ⊤))) n) := by
  let S := nestedSupportRestrictionSectionsComplexShortComplex X h ⊤ K
  have hS := nestedSupportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X h ⊤ K hK
  have : Mono (HomologicalComplex.homologyMap S.g n) :=
    (hS.homology_exact₂ n).mono_g (hsmall.eq_zero_of_src _)
  have he : HomologicalComplex.homologyMap S.g n ≫
      HomologicalComplex.homologyMap (nestedSupportRestrictionLastComplexIso X h K).hom n =
      HomologicalComplex.homologyMap
        (sectionComplexRestriction X (.up ℤ)
          (((sheafSectionsSupportedOutside X V).mapHomologicalComplex (.up ℤ)).obj K)
          (homOfLE (le_top : U ≤ ⊤))) n := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun f => HomologicalComplex.homologyMap f n)
      (nestedSupportRestrictionLastComplexIso_g X h K)
  rw [← he]
  exact mono_comp _ _

/-- If restriction from global sections to `U` is an isomorphism on `H^n` and restriction from
global sections to `U' ⊆ U` is injective on `H^n`, then restriction from `U` to `U'` is injective
on `H^n`. -/
theorem homologyMap_sectionComplexRestriction_mono_of_top
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) {U U' : Opens X} (h : U' ≤ U) (n : ℤ)
    [IsIso (HomologicalComplex.homologyMap
      (sectionComplexRestriction X (.up ℤ) K (homOfLE (le_top : U ≤ ⊤))) n)]
    [Mono (HomologicalComplex.homologyMap
      (sectionComplexRestriction X (.up ℤ) K (homOfLE (le_top : U' ≤ ⊤))) n)] :
    Mono (HomologicalComplex.homologyMap
      (sectionComplexRestriction X (.up ℤ) K (homOfLE h)) n) := by
  have heq : HomologicalComplex.homologyMap
      (sectionComplexRestriction X (.up ℤ) K (homOfLE h)) n =
      inv (HomologicalComplex.homologyMap
        (sectionComplexRestriction X (.up ℤ) K (homOfLE (le_top : U ≤ ⊤))) n) ≫
      HomologicalComplex.homologyMap
        (sectionComplexRestriction X (.up ℤ) K (homOfLE (le_top : U' ≤ ⊤))) n := by
    rw [sectionComplexRestriction_comp' X (.up ℤ) K (homOfLE (le_top : U ≤ ⊤)) (homOfLE h)
      (homOfLE (le_top : U' ≤ ⊤)), HomologicalComplex.homologyMap_comp,
      IsIso.inv_hom_id_assoc]
  rw [heq]
  exact mono_comp _ _

/-- Injectivity of restriction on section cohomology transports, through the canonical section
comparison (assumed to be an isomorphism on both opens), to injectivity of restriction on the
cohomology sheaf. -/
theorem cohomologySheaf_map_mono_of_sectionRestriction_mono
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) (n : ℤ) {U U' : Opens X} (h : U' ≤ U)
    [IsIso (sectionCohomologyToSheafSection X K n U)]
    [IsIso (sectionCohomologyToSheafSection X K n U')]
    [Mono (HomologicalComplex.homologyMap
      (sectionComplexRestriction X (.up ℤ) K (homOfLE h)) n)] :
    Mono ((K.homology n).obj.map (homOfLE h).op) := by
  have heq : (K.homology n).obj.map (homOfLE h).op =
      inv (sectionCohomologyToSheafSection X K n U) ≫
        (HomologicalComplex.homologyMap
          (sectionComplexRestriction X (.up ℤ) K (homOfLE h)) n ≫
            sectionCohomologyToSheafSection X K n U') := by
    rw [sectionCohomologyToSheafSection_restriction, IsIso.inv_hom_id_assoc]
  rw [heq]
  exact mono_comp _ _

/-- Injectivity of a restriction map transports along an isomorphism of sheaves. -/
theorem map_mono_of_iso {F G : Sheaf AddCommGrpCat.{u} X} (e : F ≅ G) {U U' : Opens X}
    (h : U' ≤ U) [Mono (F.obj.map (homOfLE h).op)] : Mono (G.obj.map (homOfLE h).op) := by
  let e' : F.obj ≅ G.obj :=
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapIso e
  have hnat : F.obj.map (homOfLE h).op ≫ e'.hom.app (op U') =
      e'.hom.app (op U) ≫ G.obj.map (homOfLE h).op := e'.hom.naturality (homOfLE h).op
  have heq : G.obj.map (homOfLE h).op =
      inv (e'.hom.app (op U)) ≫ (F.obj.map (homOfLE h).op ≫ e'.hom.app (op U')) := by
    rw [hnat, IsIso.inv_hom_id_assoc]
  rw [heq]
  exact mono_comp _ _

end TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance cycleComponentRestrictionInjectiveAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable (x : X.left)

/-! ### The singular boundary misses the generic point -/

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The generic point of a component does not lie in its singular boundary: the singular locus
of the (integral) component is a proper closed subset, so cannot contain the generic point. -/
theorem notMem_cycleComponentSingularAmbientClosedFiltration_zero :
    x ∉ cycleComponentSingularAmbientClosedFiltration X x 0 := by
  rintro ⟨z, hz, hzx⟩
  have hzgen : z = cycleComponentGenericPoint X.left x :=
    (cycleComponentι X.left x).isClosedEmbedding.injective
      (hzx.trans (cycleComponentι_genericPoint X.left x).symm)
  have hgen := cycleComponentGenericPoint_isGeneric X.left x
  have hz' : cycleComponentGenericPoint X.left x ∈
      (singularLocusClosed (cycleComponentι X.left x ≫ X.hom) : Set (cycleComponent X.left x)) :=
    hzgen ▸ hz
  have : Nonempty (cycleComponent X.left x) := ⟨cycleComponentGenericPoint X.left x⟩
  refine singularLocusClosed_ne_top (cycleComponentι X.left x ≫ X.hom) (le_antisymm le_top ?_)
  intro w _
  exact (hgen.specializes (Set.mem_univ w)).mem_closed
    (singularLocusClosed (cycleComponentι X.left x ≫ X.hom)).isClosed hz'

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The singular boundary of a component lies in the component. -/
theorem cycleComponentSingularAmbientClosedFiltration_zero_le_closure :
    (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) ⊆
      closure ({x} : Set X.left) := by
  rintro _ ⟨z, _, rfl⟩
  rw [← range_cycleComponentι]
  exact ⟨z, rfl⟩

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- A proper specialisation of a point of coheight `p` has coheight at least `p + 1`. -/
theorem coheight_succ_le_of_mem_closure_of_ne {p : ℕ} (hx : coheight x = p) {z : X.left}
    (hz : z ∈ closure ({x} : Set X.left)) (hzx : z ≠ x) :
    ((p + 1 : ℕ) : ℕ∞) ≤ coheight z := by
  have hxz : x ⤳ z := specializes_iff_mem_closure.mpr hz
  have hlt : z < x := ⟨hxz, fun hzx0 => hzx (hzx0.antisymm hxz).eq⟩
  rw [Nat.cast_succ, ← hx]
  exact Order.coheight_add_one_le hlt

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Every point of the union of the singular boundary of `Z_x` with a Zariski-closed subset
`B ⊆ Z_x` not containing `x` has coheight at least `coheight x + 1`. -/
theorem coheight_succ_le_of_mem_singularBoundary_sup {p : ℕ} (hx : coheight x = p)
    (B : Closeds X.left) (hB : (B : Set X.left) ⊆ closure ({x} : Set X.left)) (hxB : x ∉ B) :
    ∀ z ∈ cycleComponentSingularAmbientClosedFiltration X x 0 ⊔ B,
      ((p + 1 : ℕ) : ℕ∞) ≤ coheight z := by
  intro z hz
  rcases (show z ∈ (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) ∪ B
    from hz) with hz₁ | hz₂
  · refine coheight_succ_le_of_mem_closure_of_ne X x hx
      (cycleComponentSingularAmbientClosedFiltration_zero_le_closure X x hz₁) ?_
    intro hzx
    exact notMem_cycleComponentSingularAmbientClosedFiltration_zero X x (hzx ▸ hz₁)
  · refine coheight_succ_le_of_mem_closure_of_ne X x hx (hB hz₂) ?_
    intro hzx
    exact hxB (hzx ▸ hz₂)

/-! ### Vanishing along the enlarged boundary -/

/-- Supported section cohomology along the analytic support of `(singular boundary) ⊔ B` vanishes
below `2(p + 1)`. -/
theorem singularBoundarySupSectionCohomology_isZero_of_lt
    {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : coheight x = p)
    (B : Closeds X.left) (hB : (B : Set X.left) ⊆ closure ({x} : Set X.left)) (hxB : x ∉ B)
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero (SupportedInjectiveHomology X
      (analyticClosedSupport X (cycleComponentSingularAmbientClosedFiltration X x 0 ⊔ B)) n) := by
  have hstr : ClosedSupportStrataNormalCodimension X
      (cycleComponentSingularAmbientClosedFiltration X x 0 ⊔ B) d (p + 1) :=
    closedSupportStrataNormalCodimension_of_forall_le_coheight X _
      (coheight_succ_le_of_mem_singularBoundary_sup X x hx B hB hxB)
  exact closedSupportSectionCohomology_isZero_of_lt hstr n (by push_cast; exact hn)

/-! ### The complement of the enlarged boundary -/

/-- The open `U ∖ B^an` is the complement of the analytic support of `(singular boundary) ⊔ B`. -/
theorem singularBoundarySup_compl_eq (B : Closeds X.left) :
    (analyticClosedSupport X (cycleComponentSingularAmbientClosedFiltration X x 0 ⊔ B)).compl =
      cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl :=
  Opens.ext (Set.compl_union _ _)

/-- The complement of the component lies in `U ∖ B^an` for `B ⊆ Z_x`. -/
theorem cycleComponentSupportComplement_le_smoothAmbientOpen_inf (B : Closeds X.left)
    (hB : (B : Set X.left) ⊆ closure ({x} : Set X.left)) :
    (cycleComponentAnalyticClosedSupport X x).compl ≤
      cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl :=
  le_inf (cycleComponentSupportComplement_le_smoothAmbientOpen X x)
    (fun _ hy hyB => hy (hB hyB))

/-! ### The injectivity -/

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction of the supported section complex from `X` to `U ∖ B^an` is injective on `H^{2p}`,
by the nested-support localisation sequence and the vanishing along the enlarged boundary. -/
theorem cycleComponentSupportSectionRestriction_inf_homologyMap_mono
    {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : coheight x = p)
    (B : Closeds X.left) (hB : (B : Set X.left) ⊆ closure ({x} : Set X.left)) (hxB : x ∉ B) :
    Mono (HomologicalComplex.homologyMap
      (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) (.up ℤ)
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
        (homOfLE (le_top : cycleComponentSmoothSupportAmbientOpen X x ⊓
          (analyticClosedSupport X B).compl ≤ ⊤))) (2 * (p : ℤ))) := by
  have hvan := singularBoundarySupSectionCohomology_isZero_of_lt X x (d := d) hx B hB hxB
    (2 * (p : ℤ)) (by omega)
  exact TopCat.Sheaf.nestedSupportRestriction_homologyMap_top_mono_of_vanishing
    (TopCat.of (ComplexPoint X))
    (cycleComponentSupportComplement_le_smoothAmbientOpen_inf X x B hB)
    (ambientRationalInjectiveComplex X) (fun j => TopCat.Sheaf.injective_isFlasque _ _)
    (2 * (p : ℤ))
    (TopCat.Sheaf.supportedSections_homology_isZero_congr (TopCat.of (ComplexPoint X))
      (singularBoundarySup_compl_eq X x B) (ambientRationalInjectiveComplex X) (2 * (p : ℤ)) hvan)

/-- The canonical section comparison is an isomorphism on `U ∖ B^an` in degree `2p`: the
cofinal vanishing of the smooth-support purity holds at every point of `U`, hence of `U ∖ B^an`. -/
theorem sectionCohomologyToSheafSection_inf_isIso
    {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : coheight x = p) (B : Closeds X.left) :
    IsIso (TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
      (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)) (2 * (p : ℤ))
      (cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl)) := by
  rw [← TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso_hom (TopCat.of (ComplexPoint X))
    (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
    (cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl)
    0 (2 * (p : ℤ))
    (fun j hj => TopCat.Sheaf.openRestriction_homology_isZero_of_cofinal_sections
      (TopCat.of (ComplexPoint X)) _ _ j
      (fun y hy V hyV => cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing
        X x (d := d) hx j (ne_of_lt hj) y hy.1 V hyV))
    (fun j => TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl
        ((ambientRationalInjectiveComplex X).X j))]
  infer_instance

/-- The canonical section comparison is an isomorphism on `U` in degree `2p`. -/
theorem sectionCohomologyToSheafSection_smoothSupportAmbientOpen_isIso
    {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : coheight x = p) :
    IsIso (TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
      (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)) (2 * (p : ℤ))
      (cycleComponentSmoothSupportAmbientOpen X x)) := by
  rw [← TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso_hom (TopCat.of (ComplexPoint X))
    (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
    (cycleComponentSmoothSupportAmbientOpen X x) 0 (2 * (p : ℤ))
    (fun j hj => cycleComponentSmoothRestrictedInjective_homology_isZero_of_ne
      X x (d := d) hx j (ne_of_lt hj))
    (fun j => TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl
        ((ambientRationalInjectiveComplex X).X j))]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction from `U` to `U ∖ B^an` on the homology sheaf in degree `2p` is a monomorphism. -/
theorem cycleComponentSupportHomologySheaf_map_inf_mono
    {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : coheight x = p)
    (B : Closeds X.left) (hB : (B : Set X.left) ⊆ closure ({x} : Set X.left)) (hxB : x ∉ B) :
    Mono (((complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)).homology
      (2 * (p : ℤ))).obj.map
      (homOfLE (inf_le_left : cycleComponentSmoothSupportAmbientOpen X x ⊓
        (analyticClosedSupport X B).compl ≤ cycleComponentSmoothSupportAmbientOpen X x)).op) := by
  have h₁ : IsIso (HomologicalComplex.homologyMap
      (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) (.up ℤ)
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
        (homOfLE (le_top : cycleComponentSmoothSupportAmbientOpen X x ≤ ⊤))) (2 * (p : ℤ))) :=
    cycleComponentSupportSectionRestriction_homology_isIso X x (d := d) hx
  have h₂ := cycleComponentSupportSectionRestriction_inf_homologyMap_mono X x (d := d) hx B hB hxB
  have h₃ := TopCat.Sheaf.homologyMap_sectionComplexRestriction_mono_of_top
    (TopCat.of (ComplexPoint X))
    (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
    (inf_le_left : cycleComponentSmoothSupportAmbientOpen X x ⊓
      (analyticClosedSupport X B).compl ≤ cycleComponentSmoothSupportAmbientOpen X x)
    (2 * (p : ℤ))
  have h₄ := sectionCohomologyToSheafSection_smoothSupportAmbientOpen_isIso X x (d := d) hx
  have h₅ := sectionCohomologyToSheafSection_inf_isIso X x (d := d) hx B
  exact TopCat.Sheaf.cohomologySheaf_map_mono_of_sectionRestriction_mono
    (TopCat.of (ComplexPoint X))
    (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
    (2 * (p : ℤ)) _

/-- **Restriction away from a small closed subset is injective.** For a Zariski-closed
`B ⊆ Z_x` not containing the generic point `x`, restriction of sections of the local
relative-cohomology sheaf `supportRelativeCohomologySheaf … (2p)` from the smooth-support open
`U` to `U ∖ B^an` is injective. -/
theorem cycleComponentSmoothSupport_restriction_injective
    {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : coheight x = p)
    (B : Closeds X.left) (hB : (B : Set X.left) ⊆ closure ({x} : Set X.left)) (hxB : x ∉ B) :
    Function.Injective
      ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
        (2 * p)).obj.map
        (homOfLE (inf_le_left : cycleComponentSmoothSupportAmbientOpen X x ⊓
          (analyticClosedSupport X B).compl ≤ cycleComponentSmoothSupportAmbientOpen X x)).op) := by
  have he : ((2 * p : ℕ) : ℤ) = 2 * (p : ℤ) := by push_cast; ring
  have hmono := cycleComponentSupportHomologySheaf_map_inf_mono X x (d := d) hx B hB hxB
  rw [← he] at hmono
  have := TopCat.Sheaf.map_mono_of_iso (TopCat.of (ComplexPoint X))
    (complexSupportInjectiveCohomologySheafIsoRelative X
      (cycleComponentAnalyticClosedSupport X x) (2 * p))
    (inf_le_left : cycleComponentSmoothSupportAmbientOpen X x ⊓
      (analyticClosedSupport X B).compl ≤ cycleComponentSmoothSupportAmbientOpen X x)
  exact (AddCommGrpCat.mono_iff_injective _).1 this

end AlgebraicGeometry.ComplexPoint
