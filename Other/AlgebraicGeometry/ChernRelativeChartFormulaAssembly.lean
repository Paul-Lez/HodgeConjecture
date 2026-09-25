/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicGeometry.ChernRelativeChartFormula
public import Other.AlgebraicGeometry.ChernRelativeCanonicalLift
public import Other.AlgebraicGeometry.ChernComponentRecovery
public import Other.AlgebraicGeometry.ChernWindingGenericChartAlgebraic

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open AlgebraicTopology.Singular
open AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance assemblyTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable {X}

set_option maxHeartbeats 1000000 in
theorem hasChernLocalModel_of_original_local_section
    (horig : ∀ (c : Scheme.CartierData X.left)
      (E : HolomorphicUnitExtension X (dim X.left))
      (L : X.left.Modules)
      (_hL : TauCeti.SheafOfModules.IsInvertible L)
      (e : ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules))
      (_hc : c.Represents L)
      (g : ∀ i : c.ι, Γ(L, c.opens i))
      (hg : ∀ i, Scheme.Modules.Generates (g i))
      (_hrep : c.RepresentsWith L g)
      (ℓ : E.middle.obj.obj
        (op ((analyticClosedSupport X (badLocus c)).compl)))
      (hℓ : E.projection.hom.app
        (op ((analyticClosedSupport X (badLocus c)).compl)) ℓ =
        (𝓒(↧(ComplexPoint X); ℤ)).obj.map
          (homOfLE (le_top : (analyticClosedSupport X (badLocus c)).compl ≤ ⊤)).op
          HolomorphicUnitExtension.integerOneSection)
      (_hcompat : IsCartierComplementLift g E e hg
        ((analyticClosedSupport X (badLocus c)).compl) ℓ)
      (cmp : RelativeChernComparison X (dim X.left)
        ((analyticClosedSupport X (badLocus c)).compl))
      (x : X.left) (hxS : x ∈ cycleComponents X c.divisor)
      (_hx : coheight x = ((1 : ℕ) : ℕ∞))
      (q : ComplexPoint X)
      (G : GenericWindingChartData X c x (dim X.left) q)
      (_hG : G.toChart.carrier ≤ E.localLifts.opens q),
      supportedInjectiveLocalSection G.toChart.carrier (2 : ℤ)
          (relativeChernSupportedClassOnClosed
            (analyticClosedSupport X (badLocus c)) E ℓ hℓ cmp) =
        (HomologicalComplex.homologyMap
          (supportedInjectiveComplexMap X
            (show cycleComponentAnalyticClosedSupport X x ≤
                analyticClosedSupport X (badLocus c) from
              fun _ hy => closure_subset_badLocus c x
                ((mem_cycleComponents_iff X c.divisor x).mp hxS) hy)) (2 : ℤ)).hom.app
          (op G.toChart.carrier)
          ((complexSupportInjectiveCohomologySheafIsoRelative X
            (cycleComponentAnalyticClosedSupport X x) 2).inv.hom.app
            (op G.toChart.carrier)
            (G.toChart.winding G.toChart.cartierUnit))) :
    HasChernLocalModel X := by
  intro E L hL e c hc
  obtain ⟨g, hg, hrep, ℓ, hℓ, hcompat, cmp, β, hβ, hambient⟩ :=
    exists_compatible_global_lift_and_supported_class E L e c hc
  refine ⟨β, hambient, ?_⟩
  intro γ hγ x hxS hx
  obtain ⟨B, hB, hxB, hcover⟩ :=
    exists_genericWindingChartData_off_component_exceptional X c x hx
  have hbad : componentsAnalyticClosedSupport X (cycleComponents X c.divisor) ≤
      analyticClosedSupport X (badLocus c) := by
    rw [← analyticClosedSupport_componentsZariskiSupport X
      (cycleComponents X c.divisor)]
    exact analyticClosedSupport_le_of_le X
      (componentsZariskiSupport_le_badLocus (X := X) c)
  choose G hG using
    fun q : {q : ComplexPoint X // q ∈ cycleComponentSmoothSupportAmbientOpen X x ∧
        q ∈ cycleComponentSupport X x ∧ Point.underlying q ∉ B} =>
      hcover q.1 q.2.1 q.2.2.1 q.2.2.2
        (cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl ⊓
          E.localLifts.opens q.1)
        ⟨⟨q.2.1, q.2.2.2⟩, E.localLifts.mem_opens q.1⟩
  refine cycleComponentSmoothSupport_restriction_injective X x (d := dim X.left) hx B hB hxB ?_
  refine TopCat.Sheaf.eq_of_locally_eq'
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * 1))
    (fun q : Option {q : ComplexPoint X // q ∈ cycleComponentSmoothSupportAmbientOpen X x ∧
        q ∈ cycleComponentSupport X x ∧ Point.underlying q ∉ B} =>
      q.elim ((cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl) ⊓
        (cycleComponentAnalyticClosedSupport X x).compl)
        fun q => (G q).toChart.carrier ⊓
          (cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl))
    (cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl)
    (fun q => match q with
      | none => homOfLE inf_le_left
      | some _ => homOfLE inf_le_right) ?_ _ _ ?_
  · intro y hy
    rw [Opens.mem_iSup]
    by_cases hyS : y ∈ cycleComponentSupport X x
    · exact ⟨some ⟨y, hy.1, hyS, hy.2⟩,
        (G ⟨y, hy.1, hyS, hy.2⟩).toChart.mem, hy⟩
    · exact ⟨none, hy, hyS⟩
  · rintro (_ | q)
    · have hVS : ∀ y ∈ ((cycleComponentSmoothSupportAmbientOpen X x ⊓
          (analyticClosedSupport X B).compl) ⊓
          (cycleComponentAnalyticClosedSupport X x).compl :
            Opens (TopCat.of (ComplexPoint X))), y ∉ cycleComponentSupport X x :=
        fun _ hy => hy.2
      exact (AlgebraicTopology.Singular.supportRelativeCohomologySheaf_section_eq_zero
          (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x) (2 * 1)
          (cycleComponentAnalyticClosedSupport X x).isClosed _ hVS _).trans
        (AlgebraicTopology.Singular.supportRelativeCohomologySheaf_section_eq_zero
          (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x) (2 * 1)
          (cycleComponentAnalyticClosedSupport X x).isClosed _ hVS _).symm
    · let ch := (G q).toChart
      let U' : Opens (ComplexPoint X) :=
        cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl
      let i : ch.carrier ⊓ U' ⟶ U' := homOfLE inf_le_right
      let j : U' ⟶ cycleComponentSmoothSupportAmbientOpen X x := homOfLE inf_le_left
      let k : ch.carrier ⊓ U' ⟶ ch.carrier := homOfLE inf_le_left
      let l : ch.carrier ⟶ cycleComponentSmoothSupportAmbientOpen X x := homOfLE ch.le
      let m : ch.carrier ⊓ U' ⟶ cycleComponentSmoothSupportAmbientOpen X x :=
        homOfLE (le_trans inf_le_left ch.le)
      have hnorm := ChernWindingChart.normalizedClass_restrict_eq_divisor_smul_of_original
        (X := X) ch hx hxS
        (fun y hy => coheight_of_mem_cycleComponents X hy)
        (fun y hy => (mem_cycleComponents_iff X c.divisor y).mp hy)
        β γ hγ hbad
        (relativeChernSupportedClassOnClosed
          (analyticClosedSupport X (badLocus c)) E ℓ hℓ cmp) hβ
        (horig c E L hL e hc g hg hrep ℓ hℓ hcompat cmp x hxS hx q.1 (G q)
          ((hG q).trans inf_le_right))
        (G q).toGeometric.hasTrivialUnitWinding ((G q).normalizesCoclass hx)
      let F := supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * 1)
      have key' := congrArg (F.obj.map k.op) hnorm
      exact (sheaf_map_map_eq F i j m _).trans
        ((sheaf_map_map_eq F k l m _).symm.trans (key'.trans
          ((sheaf_map_map_eq F k l m _).trans (sheaf_map_map_eq F i j m _).symm)))

end AlgebraicGeometry.ComplexPoint
