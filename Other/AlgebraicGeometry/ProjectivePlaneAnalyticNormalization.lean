/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectivePlaneHyperplaneSmooth
public import Other.AlgebraicTopology.NormalChartWindingClass
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexManifold
public import HodgeConjecture.Lemmas.AlgebraicGeometry.HolomorphicClosedImmersionCharts
public import HodgeConjecture.Lemmas.AlgebraicTopology.NormalProjectionOverlap
public import Mathlib.Analysis.Analytic.Polynomial

/-!
# Explicit analytic normal charts for the coordinate hyperplane in `ℙ²`

The standard projective chart `D₊(Xᵢ)` is identified with complex affine two-space using
the actual homogeneous-localization ring equivalence.  After swapping the two affine
coordinates, the second factor is literally the regular function `X₀ / Xᵢ`.  Thus the
resulting global homeomorphism is an explicit support-flattening chart for `i = 1, 2`;
no choice of local coordinates is hidden in its definition.
-/

@[expose] public noncomputable section

open CategoryTheory Topology MvPolynomial AlgebraicGeometry AlgebraicTopology.Singular
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

open Point

/-- Evaluation of a global regular function on complex affine space, in the literal polynomial
coordinates supplied by `affineSpaceEquiv`, is complex analytic. -/
lemma analyticAt_evaluate_top_affineSpaceEquiv_symm {n : Type} [Fintype n]
    (s : Γ(complexAffineSpace n, ⊤)) (v : n → ℂ) :
    AnalyticAt ℂ (fun w : n → ℂ ↦ evaluate ⊤ s ((affineSpaceEquiv n).symm w)) v := by
  rw [show (fun w : n → ℂ ↦ evaluate ⊤ s ((affineSpaceEquiv n).symm w)) =
      fun w ↦ MvPolynomial.eval w (affineGlobalPolynomial s) by
    funext w
    exact evaluate_affineSpaceEquiv_symm_top s w]
  have h := AnalyticAt.aeval_mvPolynomial
    (z := v) (fun i ↦
      (ContinuousLinearMap.proj i : (n → ℂ) →L[ℂ] ℂ).analyticAt v)
    (affineGlobalPolynomial s)
  simpa [MvPolynomial.aeval_def] using h

/-- If global regular functions are analytic in a homeomorphic affine parametrization, then so
are arbitrary local regular functions on their domains.  The proof shrinks to a principal open
and uses its actual quotient presentation. -/
lemma analyticAt_evaluate_of_homeomorph
    {X : Over (Spec (CommRingCat.of ℂ))} {n : Type} [Fintype n]
    (hX : IsAffineOpen (⊤ : X.left.Opens))
    (e : (n → ℂ) ≃ₜ ComplexPoint X)
    (hglobal : ∀ (r : Γ(X.left, ⊤)) (w : n → ℂ),
      AnalyticAt ℂ (fun u ↦ evaluate ⊤ r (e u)) w)
    (V : X.left.Opens) (s : Γ(X.left, V))
    (v : n → ℂ) (hv : e v ∈ overOpen V) :
    AnalyticAt ℂ (fun w : n → ℂ ↦ evaluate V s (e w)) v := by
  obtain ⟨f, hfV, hvf⟩ :=
    hX.exists_basicOpen_le ⟨(e v).underlying, hv⟩ trivial
  let t := X.left.presheaf.map (homOfLE hfV).op s
  obtain ⟨k, a, heval⟩ :=
    exists_evaluate_basicOpen_eq_div (X := X) hX f t
  have ha := hglobal a v
  have hf := hglobal f v
  have hfv : evaluate ⊤ f (e v) ≠ 0 :=
    (mem_overOpen_basicOpen_iff_evaluate_ne_zero
      (X := X) (U := ⊤) f _ trivial).mp hvf
  have hrat : AnalyticAt ℂ
      (fun w : n → ℂ ↦ evaluate ⊤ a (e w) /
        evaluate ⊤ f (e w) ^ k) v :=
    ha.div (hf.pow k) (pow_ne_zero k hfv)
  apply hrat.congr
  have hnhd : e ⁻¹' overOpen (X.left.basicOpen f) ∈ 𝓝 v :=
    e.continuous.continuousAt ((isOpen_overOpen (X := X)
      (X.left.basicOpen f)).mem_nhds hvf)
  filter_upwards [hnhd] with w hw
  exact ((evaluate_res hfV s _ hw).trans (heval _ hw)).symm

/-- Evaluation of an arbitrary local regular function on complex affine space is analytic in
the literal polynomial coordinates wherever that function is defined. -/
lemma analyticAt_evaluate_affineSpaceEquiv_symm {n : Type} [Fintype n]
    (V : (complexAffineSpace n).Opens) (s : Γ(complexAffineSpace n, V))
    (v : n → ℂ) (hv : (affineSpaceEquiv n).symm v ∈ overOpen V) :
    AnalyticAt ℂ (fun w : n → ℂ ↦ evaluate V s ((affineSpaceEquiv n).symm w)) v := by
  apply analyticAt_evaluate_of_homeomorph (isAffineOpen_top (complexAffineSpace n))
    (affineSpaceHomeomorph n).symm
    (fun r w ↦ analyticAt_evaluate_top_affineSpaceEquiv_symm r w) V s v hv

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicGeometry.ProjectivePlane.AnalyticNormalization

open AlgebraicGeometry.ComplexPoint
open CoordinateCharts HyperplaneSmooth

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every standard affine chart of the projective plane is smooth of relative dimension two.
This is obtained by composing its open immersion with the proved smooth structure map of
`ℙ²`, rather than postulated as chart data. -/
noncomputable instance analyticChart_smoothOfRelativeDimension (i : Fin 3) :
    SmoothOfRelativeDimension 2 (analyticChart i).hom := by
  change SmoothOfRelativeDimension 2 ((chartOpen i).ι ≫ structureMap)
  simpa only [Nat.zero_add] using
    smoothOfRelativeDimension_comp 0 2 (chartOpen i).ι structureMap

/-- The analytic projective plane carries the proved relative-dimension-two smooth
structure used by its canonical algebraic local charts. -/
noncomputable instance analyticPlane_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 2 analyticPlane.hom := by
  change SmoothOfRelativeDimension 2 planeOver.hom
  infer_instance

/-- The same explicit hyperplane immersion, with codomain written as the transparent
`analyticPlane` presentation used by the coordinate-chart development. -/
def hyperplaneAnalyticι : hyperplaneOver ⟶ analyticPlane :=
  Over.homMk hyperplaneι rfl

/-- The transparent-codomain immersion is the original over-scheme immersion; only the
presentation of its codomain differs. -/
lemma hyperplaneAnalyticι_eq_hyperplaneOverι :
    hyperplaneAnalyticι = hyperplaneOverι := by
  apply Over.OverMorphism.ext
  rfl

noncomputable instance hyperplaneAnalyticι_isClosedImmersion :
    IsClosedImmersion hyperplaneAnalyticι.left := by
  change IsClosedImmersion hyperplaneι
  infer_instance

/-- The canonical holomorphic flattening chart for the coordinate hyperplane at a specified
hyperplane point, in the same ambient presentation as the explicit affine charts. -/
def canonicalHyperplaneFlattening (z : ComplexPoint hyperplaneOver) :
    OpenPartialHomeomorph (ComplexPoint analyticPlane)
      ((Fin 1 → ℂ) × (Fin 1 → ℂ)) :=
  ComplexPoint.closedImmersionHolomorphicFlatteningChart analyticPlane hyperplaneOver
    hyperplaneAnalyticι 1 2 z

/-- The standard `Proj` chart, as the actual affine plane over `ℂ`. -/
def chartSchemeIsoAffine (i : Fin 3) :
    (chartOpen i).toScheme ≅ ComplexPoint.complexAffineSpace (Fin 2) :=
  (chartIsAffine i).isoSpec ≪≫
    Scheme.Spec.mapIso (chartGlobalRingEquiv i).toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso (Fin 2) (CommRingCat.of ℂ)).symm

/-- The affine-chart isomorphism respects the displayed structure morphisms to `Spec ℂ`. -/
lemma chartSchemeIsoAffine_over (i : Fin 3) :
    (chartSchemeIsoAffine i).hom ≫
        (ComplexPoint.complexAffineSpace (Fin 2) ↘ Spec (CommRingCat.of ℂ)) =
      (chartOpen i).ι ≫ structureMap := by
  rw [← cancel_epi (chartIsAffine i).isoSpec.inv]
  simp only [chartSchemeIsoAffine, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op,
    AffineSpace.SpecIso_inv_over, Iso.inv_hom_id_assoc]
  rw [← Category.assoc]
  rw [show (chartIsAffine i).isoSpec.inv ≫ (chartOpen i).ι =
      (chartIsAffine i).fromSpec from rfl]
  rw [chartFromSpec_comp_structureMap]
  rw [← Spec.map_comp]
  congr 1

/-- The standard projective chart, as an isomorphism over `Spec ℂ`. -/
def chartOverIsoAffine (i : Fin 3) :
    analyticChart i ≅
      Over.mk (ComplexPoint.complexAffineSpace (Fin 2) ↘ Spec (CommRingCat.of ℂ)) :=
  Over.isoMk (chartSchemeIsoAffine i) (chartSchemeIsoAffine_over i)

/-- Analytic points of `D₊(Xᵢ)` are globally homeomorphic to `ℂ²`. -/
def chartAffineHomeomorph (i : Fin 3) :
    ComplexPoint (analyticChart i) ≃ₜ (Fin 2 → ℂ) :=
  (Point.isoMapHomeomorph (chartOverIsoAffine i)).trans
    (ComplexPoint.affineSpaceHomeomorph (Fin 2))

/-- The inverse explicit affine chart is the point-map of the inverse scheme isomorphism,
applied to the standard affine-space point with the displayed coordinates. -/
lemma chartAffineHomeomorph_symm_apply (i : Fin 3) (v : Fin 2 → ℂ) :
    (chartAffineHomeomorph i).symm v =
      Point.map (chartOverIsoAffine i).inv
        ((ComplexPoint.affineSpaceEquiv (Fin 2)).symm v) := by
  rfl

/-- Evaluation of any local regular function is analytic along the inverse explicit affine
chart wherever the function is defined. -/
lemma analyticAt_chartAffineHomeomorph_symm_evaluate
    (i : Fin 3) (V : (analyticChart i).left.Opens)
    (s : Γ((analyticChart i).left, V))
    (v : Fin 2 → ℂ) (hv : (chartAffineHomeomorph i).symm v ∈ Point.overOpen V) :
    AnalyticAt ℂ
      (fun w ↦ Point.evaluate V s ((chartAffineHomeomorph i).symm w)) v := by
  let e := chartOverIsoAffine i
  have hv' : (ComplexPoint.affineSpaceEquiv (Fin 2)).symm v ∈
      Point.overOpen (e.inv.left ⁻¹ᵁ V) := by
    rw [← Point.mem_overOpen_map_iff e.inv _ V]
    simpa only [e, chartAffineHomeomorph_symm_apply] using hv
  have ha := ComplexPoint.analyticAt_evaluate_affineSpaceEquiv_symm
    (e.inv.left ⁻¹ᵁ V) (e.inv.left.app V s) v hv'
  apply ha.congr
  filter_upwards with w
  rw [← Point.evaluate_map e.inv V s]
  rfl

/-- Conversely, every canonical algebraic étale chart is analytic after the inverse explicit
affine chart.  This is the formerly missing analytic transition direction. -/
lemma analyticAt_localChart_comp_chartAffineHomeomorph_symm
    (i : Fin 3) (z : ComplexPoint (analyticChart i)) {v : Fin 2 → ℂ}
    (hv : (chartAffineHomeomorph i).symm v ∈
      (ComplexPoint.localChart (analyticChart i) 2 z).source) :
    AnalyticAt ℂ
      (fun w ↦ ComplexPoint.localChart (analyticChart i) 2 z
        ((chartAffineHomeomorph i).symm w)) v := by
  apply AnalyticAt.pi
  intro j
  let D := ComplexPoint.localEtaleCoordinates (analyticChart i) 2 z
  have hV : (chartAffineHomeomorph i).symm v ∈ Point.overOpen D.ambientCoordinateOpen := by
    have hmem := ComplexPoint.mem_coordinateNeighborhood_of_mem_localChart_source
      (analyticChart i) 2 z ((chartAffineHomeomorph i).symm v) hv
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using hmem
  have ha := analyticAt_chartAffineHomeomorph_symm_evaluate i
    D.ambientCoordinateOpen (D.ambientCoordinateSection j) v hV
  apply ha.congr
  have hnhd : (chartAffineHomeomorph i).symm ⁻¹'
      (ComplexPoint.localChart (analyticChart i) 2 z).source ∈ 𝓝 v :=
    (chartAffineHomeomorph i).symm.continuous.continuousAt
      ((ComplexPoint.localChart (analyticChart i) 2 z).open_source.mem_nhds hv)
  filter_upwards [hnhd] with w hw
  exact (ComplexPoint.localChart_apply_component_eq_evaluate (analyticChart i) 2 z
    ((chartAffineHomeomorph i).symm w) hw j).symm

/-- Put the tangent coordinate first and the `X₀ / Xᵢ` coordinate second. -/
def splitNormalHomeomorph :
    (Fin 2 → ℂ) ≃ₜ ((Fin 1 → ℂ) × (Fin 1 → ℂ)) where
  toFun v := (fun _ ↦ v 1, fun _ ↦ v 0)
  invFun w := Fin.cases (w.2 0) (fun _ ↦ w.1 0)
  left_inv v := by funext j; fin_cases j <;> rfl
  right_inv w := by apply Prod.ext <;> funext j <;> fin_cases j <;> rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_pi (fun _ ↦ continuous_apply 1)
    · exact continuous_pi (fun _ ↦ continuous_apply 0)
  continuous_invFun := by
    apply continuous_pi
    intro j
    fin_cases j
    · change Continuous (fun w : (Fin 1 → ℂ) × (Fin 1 → ℂ) ↦ w.2 0)
      exact (continuous_apply 0).comp continuous_snd
    · change Continuous (fun w : (Fin 1 → ℂ) × (Fin 1 → ℂ) ↦ w.1 0)
      exact (continuous_apply 0).comp continuous_fst

/-- A canonical local algebraic chart, with the same fixed tangent/normal permutation used by
the explicit affine flattening. -/
def splitLocalChart (i : Fin 3) (z : ComplexPoint (analyticChart i)) :
    OpenPartialHomeomorph (ComplexPoint (analyticChart i))
      ((Fin 1 → ℂ) × (Fin 1 → ℂ)) :=
  (ComplexPoint.localChart (analyticChart i) 2 z).trans
    splitNormalHomeomorph.toOpenPartialHomeomorph

/-- The coordinate swap used by the explicit flattening is complex analytic. -/
lemma analyticAt_splitNormalHomeomorph (v : Fin 2 → ℂ) :
    AnalyticAt ℂ (splitNormalHomeomorph) v := by
  change AnalyticAt ℂ
    (fun v : Fin 2 → ℂ ↦ (fun _ : Fin 1 ↦ v 1, fun _ : Fin 1 ↦ v 0)) v
  apply AnalyticAt.prod
  · apply AnalyticAt.pi
    intro j
    fin_cases j
    exact (ContinuousLinearMap.proj (R := ℂ) (1 : Fin 2)).analyticAt v
  · apply AnalyticAt.pi
    intro j
    fin_cases j
    exact (ContinuousLinearMap.proj (R := ℂ) (0 : Fin 2)).analyticAt v

/-- The inverse coordinate swap is complex analytic as well. -/
lemma analyticAt_splitNormalHomeomorph_symm
    (w : (Fin 1 → ℂ) × (Fin 1 → ℂ)) :
    AnalyticAt ℂ (splitNormalHomeomorph.symm) w := by
  change AnalyticAt ℂ (fun w : (Fin 1 → ℂ) × (Fin 1 → ℂ) ↦
    (splitNormalHomeomorph.symm w : Fin 2 → ℂ)) w
  dsimp [splitNormalHomeomorph]
  apply AnalyticAt.pi
  intro j
  fin_cases j
  · exact ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 1)).analyticAt w.2).comp
      ((ContinuousLinearMap.snd ℂ (Fin 1 → ℂ) (Fin 1 → ℂ)).analyticAt w)
  · exact ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 1)).analyticAt w.1).comp
      ((ContinuousLinearMap.fst ℂ (Fin 1 → ℂ) (Fin 1 → ℂ)).analyticAt w)

/-- A global explicit flattening chart on `D₊(Xᵢ)`.  For `i = 1, 2`, its normal component
is the coordinate cutting out the hyperplane `X₀ = 0`. -/
def chartFlattening (i : Fin 3) :
    OpenPartialHomeomorph (ComplexPoint (analyticChart i))
      ((Fin 1 → ℂ) × (Fin 1 → ℂ)) :=
  ((chartAffineHomeomorph i).trans splitNormalHomeomorph).toOpenPartialHomeomorph

/-- The open immersion from the standard affine chart into the analytic projective plane,
on complex points. -/
def chartEmbeddingMap (i : Fin 3) :
    ComplexPoint (analyticChart i) → ComplexPoint analyticPlane :=
  Point.map (ComplexPoint.openInclusion analyticPlane (chartOpen i))

/-- The map of complex points induced by a standard projective open chart is an open
embedding. -/
lemma chartEmbeddingMap_isOpenEmbedding (i : Fin 3) :
    IsOpenEmbedding (chartEmbeddingMap i) := by
  exact ComplexPoint.isOpenEmbedding_map_open analyticPlane (chartOpen i)

/-- The explicit affine flattening, regarded as an honest partial chart in the ambient
analytic projective plane. -/
def ambientChartFlattening (i : Fin 3) :
    OpenPartialHomeomorph (ComplexPoint analyticPlane)
      ((Fin 1 → ℂ) × (Fin 1 → ℂ)) :=
  (chartFlattening i).lift_openEmbedding (chartEmbeddingMap_isOpenEmbedding i)

/-- The ambient lift agrees literally with the explicit affine flattening on chart points. -/
lemma ambientChartFlattening_apply (i : Fin 3)
    (z : ComplexPoint (analyticChart i)) :
    ambientChartFlattening i (chartEmbeddingMap i z) = chartFlattening i z := by
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _

/-- The transition from the explicit affine flattening to the permuted canonical local chart is
complex analytic at every point of its actual domain. -/
lemma analyticAt_chartFlattening_transition_splitLocalChart
    (i : Fin 3) (z : ComplexPoint (analyticChart i))
    (v : (Fin 1 → ℂ) × (Fin 1 → ℂ))
    (hv : v ∈ ((chartFlattening i).symm.trans (splitLocalChart i z)).source) :
    AnalyticAt ℂ ((chartFlattening i).symm.trans (splitLocalChart i z)) v := by
  rw [OpenPartialHomeomorph.trans_source] at hv
  have hy : (chartAffineHomeomorph i).symm (splitNormalHomeomorph.symm v) ∈
      (ComplexPoint.localChart (analyticChart i) 2 z).source := by
    exact hv.2.1
  have h1 := analyticAt_splitNormalHomeomorph_symm v
  have h2 := analyticAt_localChart_comp_chartAffineHomeomorph_symm i z hy
  have h3 := analyticAt_splitNormalHomeomorph
    (ComplexPoint.localChart (analyticChart i) 2 z
      ((chartAffineHomeomorph i).symm (splitNormalHomeomorph.symm v)))
  have hmiddle : AnalyticAt ℂ
      (fun u ↦ ComplexPoint.localChart (analyticChart i) 2 z
        ((chartAffineHomeomorph i).symm (splitNormalHomeomorph.symm u))) v := by
    simpa only [Function.comp_def] using h2.comp (x := v) h1
  have hcomp : AnalyticAt ℂ
      (fun u ↦ splitNormalHomeomorph
        (ComplexPoint.localChart (analyticChart i) 2 z
          ((chartAffineHomeomorph i).symm (splitNormalHomeomorph.symm u)))) v := by
    exact h3.comp (x := v) hmiddle
  change AnalyticAt ℂ
    (fun u ↦ splitNormalHomeomorph
      (ComplexPoint.localChart (analyticChart i) 2 z
        ((chartAffineHomeomorph i).symm (splitNormalHomeomorph.symm u)))) v
  exact hcomp

/-- Pullback of an affine coordinate through the scheme chart is the literal homogeneous
ratio used to define `chartCoordinate`. -/
lemma chartSchemeIsoAffine_hom_appTop_coord (i : Fin 3) (j : Fin 2) :
    (chartSchemeIsoAffine i).hom.appTop
        (AffineSpace.coord (Spec (CommRingCat.of ℂ)) j) =
      chartCoordinate i j := by
  simp only [chartSchemeIsoAffine, Iso.trans_hom, Iso.symm_hom,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Functor.mapIso_hom,
    Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [AffineSpace.SpecIso_inv_appTop_coord]
  have hmap :
      (Spec.map (chartGlobalRingEquiv i).toCommRingCatIso.hom).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) ℂ))).inv.hom
            (MvPolynomial.X j)) =
        (Scheme.ΓSpecIso Γ(plane, chartOpen i)).inv.hom
          (chartGlobalRingEquiv i (MvPolynomial.X j)) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
    rfl
  rw [hmap, (chartIsAffine i).isoSpec_hom_appTop]
  have hcancel := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso Γ(plane, chartOpen i)).inv_hom_id
      (chartGlobalRingEquiv i (MvPolynomial.X j))
  change (Scheme.ΓSpecIso Γ(plane, chartOpen i)).hom.hom
      ((Scheme.ΓSpecIso Γ(plane, chartOpen i)).inv.hom
        (chartGlobalRingEquiv i (MvPolynomial.X j))) =
      chartGlobalRingEquiv i (MvPolynomial.X j) at hcancel
  change (chartOpen i).topIso.inv.hom
      ((Scheme.ΓSpecIso Γ(plane, chartOpen i)).hom.hom
        ((Scheme.ΓSpecIso Γ(plane, chartOpen i)).inv.hom
          (chartGlobalRingEquiv i (MvPolynomial.X j)))) = _
  rw [hcancel]
  change (chartOpen i).topIso.inv.hom
      ((Proj.basicOpenIsoAway Grading (MvPolynomial.X i)
        (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).hom.hom
          (Other.ProjectiveChart.chartRingEquiv ℂ i (MvPolynomial.X j))) = _
  congr 2
  exact Other.ProjectiveChart.chartHom_X ℂ i j

/-- On analytic points, the affine chart coordinates are exactly the evaluated regular
ratio coordinates. -/
lemma chartAffineHomeomorph_apply (i : Fin 3)
    (z : ComplexPoint (analyticChart i)) (j : Fin 2) :
    chartAffineHomeomorph i z j = chartCoordinateValue i j z := by
  rw [chartCoordinateValue, ComplexPoint.evaluate_top_eq_appTop]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
      ((z.left ≫ (chartOverIsoAffine i).hom.left).appTop
        (AffineSpace.coord (Spec (CommRingCat.of ℂ)) j)) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
      (z.left.appTop.hom ((chartSchemeIsoAffine i).hom.appTop.hom
        (AffineSpace.coord (Spec (CommRingCat.of ℂ)) j))) = _
  rw [chartSchemeIsoAffine_hom_appTop_coord]

/-- The projective ratio section before transport to the open subscheme. -/
def chartCoordinateAmbient (i : Fin 3) (j : Fin 2) : Γ(plane, chartOpen i) :=
  (Proj.basicOpenIsoAway Grading (MvPolynomial.X i)
    (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).hom
      (Other.ProjectiveChart.gen ℂ i j)

/-- Explicit affine coordinates equal evaluation of the corresponding regular functions on
the ambient projective open. -/
lemma chartAffineHomeomorph_apply_eq_ambient_evaluate (i : Fin 3)
    (z : ComplexPoint (analyticChart i)) (j : Fin 2) :
    chartAffineHomeomorph i z j =
      Point.evaluate (chartOpen i) (chartCoordinateAmbient i j)
        (chartEmbeddingMap i z) := by
  rw [chartAffineHomeomorph_apply]
  change Point.evaluate ⊤ (chartCoordinate i j) z = _
  change Point.evaluate ⊤ ((chartOpen i).topIso.inv (chartCoordinateAmbient i j)) z = _
  have h := CoordinateCharts.evaluate_topIso_inv (X := analyticPlane) (chartOpen i)
    (chartCoordinateAmbient i j) z
  change Point.evaluate ⊤ ((chartOpen i).topIso.inv (chartCoordinateAmbient i j)) z =
    Point.evaluate (chartOpen i) (chartCoordinateAmbient i j)
      (Point.map (ComplexPoint.openInclusion analyticPlane (chartOpen i)) z) at h
  exact h

/-- In explicit affine coordinates, the ambient canonical local chart is analytic.  This is
the forward ambient transition needed to compare the explicit and canonical flattenings. -/
lemma analyticAt_localChart_comp_chartEmbedding_chartAffineHomeomorph_symm
    (i : Fin 3) (z : ComplexPoint analyticPlane) {v : Fin 2 → ℂ}
    (hv : chartEmbeddingMap i ((chartAffineHomeomorph i).symm v) ∈
      (ComplexPoint.localChart analyticPlane 2 z).source) :
    AnalyticAt ℂ (fun w ↦ ComplexPoint.localChart analyticPlane 2 z
      (chartEmbeddingMap i ((chartAffineHomeomorph i).symm w))) v := by
  apply AnalyticAt.pi
  intro j
  let D := ComplexPoint.localEtaleCoordinates analyticPlane 2 z
  have hV : chartEmbeddingMap i ((chartAffineHomeomorph i).symm v) ∈
      Point.overOpen D.ambientCoordinateOpen := by
    have hmem := ComplexPoint.mem_coordinateNeighborhood_of_mem_localChart_source
      analyticPlane 2 z _ hv
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using hmem
  have hV' : (chartAffineHomeomorph i).symm v ∈
      Point.overOpen
        ((ComplexPoint.openInclusion analyticPlane (chartOpen i)).left ⁻¹ᵁ
          D.ambientCoordinateOpen) :=
    (Point.mem_overOpen_map_iff
      (ComplexPoint.openInclusion analyticPlane (chartOpen i)) _ _).mp hV
  have ha := analyticAt_chartAffineHomeomorph_symm_evaluate i
    ((ComplexPoint.openInclusion analyticPlane (chartOpen i)).left ⁻¹ᵁ
      D.ambientCoordinateOpen)
    ((ComplexPoint.openInclusion analyticPlane (chartOpen i)).left.app
      D.ambientCoordinateOpen (D.ambientCoordinateSection j)) v hV'
  apply ha.congr
  have hnhd : (fun w ↦ chartEmbeddingMap i ((chartAffineHomeomorph i).symm w)) ⁻¹'
      (ComplexPoint.localChart analyticPlane 2 z).source ∈ 𝓝 v :=
    ((chartEmbeddingMap_isOpenEmbedding i).continuous.continuousAt.comp
      (chartAffineHomeomorph i).symm.continuous.continuousAt)
      ((ComplexPoint.localChart analyticPlane 2 z).open_source.mem_nhds hv)
  filter_upwards [hnhd] with w hw
  rw [ComplexPoint.localChart_apply_component_eq_evaluate analyticPlane 2 z _ hw j]
  exact (Point.evaluate_map (ComplexPoint.openInclusion analyticPlane (chartOpen i))
    D.ambientCoordinateOpen (D.ambientCoordinateSection j)
    ((chartAffineHomeomorph i).symm w)).symm

/-- On its actual source, the lifted ambient explicit chart is literally the fixed
tangent/normal permutation of the two ambient regular ratio functions. -/
lemma ambientChartFlattening_apply_eq_ambient_coordinates (i : Fin 3)
    (y : ComplexPoint analyticPlane) (hy : y ∈ (ambientChartFlattening i).source) :
    ambientChartFlattening i y =
      splitNormalHomeomorph
        (fun j ↦ Point.evaluate (chartOpen i) (chartCoordinateAmbient i j) y) := by
  obtain ⟨q, hq, rfl⟩ := hy
  rw [ambientChartFlattening_apply]
  change splitNormalHomeomorph (chartAffineHomeomorph i q) = _
  congr 1
  funext j
  exact chartAffineHomeomorph_apply_eq_ambient_evaluate i q j

/-- Conversely, the lifted explicit ambient coordinates are analytic after the inverse of an
ambient canonical local chart, wherever the inverse-chart point lies in the affine chart. -/
lemma analyticAt_ambientChartFlattening_comp_localChart_symm
    (i : Fin 3) (z : ComplexPoint analyticPlane) {w : Fin 2 → ℂ}
    (hw : w ∈ (ComplexPoint.localChart analyticPlane 2 z).target)
    (hsource : (ComplexPoint.localChart analyticPlane 2 z).symm w ∈
      (ambientChartFlattening i).source) :
    AnalyticAt ℂ (fun v ↦ ambientChartFlattening i
      ((ComplexPoint.localChart analyticPlane 2 z).symm v)) w := by
  have hsource' := hsource
  obtain ⟨q, hq, hqw⟩ := hsource'
  have hopen : (ComplexPoint.localChart analyticPlane 2 z).symm w ∈
      Point.overOpen (chartOpen i) := by
    rw [← hqw]
    exact (ComplexPoint.openEquiv analyticPlane (chartOpen i) q).property
  have hj (j : Fin 2) := ComplexPoint.analyticAt_localChart_symm_evaluate
    analyticPlane 2 z hw (chartOpen i) (chartCoordinateAmbient i j) hopen
  have hcoords : AnalyticAt ℂ
      (fun v ↦ fun j ↦ Point.evaluate (chartOpen i) (chartCoordinateAmbient i j)
        ((ComplexPoint.localChart analyticPlane 2 z).symm v)) w :=
    AnalyticAt.pi hj
  have hsplit := (analyticAt_splitNormalHomeomorph _).comp (x := w) hcoords
  apply hsplit.congr
  have hnhd : (ComplexPoint.localChart analyticPlane 2 z).symm ⁻¹'
      (ambientChartFlattening i).source ∈ 𝓝 w :=
    (ComplexPoint.localChart analyticPlane 2 z).continuousAt_symm hw
      ((ambientChartFlattening i).open_source.mem_nhds hsource)
  filter_upwards [hnhd] with v hv
  exact (ambientChartFlattening_apply_eq_ambient_coordinates i _ hv).symm

/-- At a hyperplane point contained in the explicit affine chart, the transition from the
ambient lifted explicit flattening to the canonical closed-immersion flattening is analytic. -/
lemma analyticAt_ambientChartFlattening_transition_canonical
    (i : Fin 3) (q : ComplexPoint (analyticChart i))
    (z : ComplexPoint hyperplaneOver)
    (hcenter : chartEmbeddingMap i q = Point.map hyperplaneAnalyticι z) :
    let e := ambientChartFlattening i
    let e' := canonicalHyperplaneFlattening z
    AnalyticAt ℂ (e.symm.trans e') (e (chartEmbeddingMap i q)) := by
  dsimp only
  let x : ComplexPoint analyticPlane := chartEmbeddingMap i q
  let e := ambientChartFlattening i
  let e' := canonicalHyperplaneFlattening z
  let C := ComplexPoint.localChart analyticPlane 2 (Point.map hyperplaneAnalyticι z)
  let N := ComplexPoint.closedImmersionNormalCoordinateChange analyticPlane hyperplaneOver
    hyperplaneAnalyticι 1 2 z
  have hx : x ∈ e.source := ⟨q, by trivial, rfl⟩
  have hqC : chartEmbeddingMap i q ∈ C.source := by
    rw [hcenter]
    exact ComplexPoint.mem_localChart_source analyticPlane 2 (Point.map hyperplaneAnalyticι z)
  have hsplit := analyticAt_splitNormalHomeomorph_symm (e x)
  have hC0 := analyticAt_localChart_comp_chartEmbedding_chartAffineHomeomorph_symm
    i (Point.map hyperplaneAnalyticι z)
      (v := splitNormalHomeomorph.symm (e x)) (by
      have heq : (chartAffineHomeomorph i).symm
          (splitNormalHomeomorph.symm (e x)) = q := by
        rw [show e x = chartFlattening i q by
          exact ambientChartFlattening_apply i q]
        change (chartAffineHomeomorph i).symm
          (splitNormalHomeomorph.symm
            (splitNormalHomeomorph (chartAffineHomeomorph i q))) = q
        rw [splitNormalHomeomorph.symm_apply_apply,
          (chartAffineHomeomorph i).symm_apply_apply]
      rwa [heq])
  have hC : AnalyticAt ℂ
      (fun u ↦ C (chartEmbeddingMap i
        ((chartAffineHomeomorph i).symm (splitNormalHomeomorph.symm u)))) (e x) := by
    simpa only [C, Function.comp_def] using hC0.comp (x := e x) hsplit
  have hNx := ComplexPoint.analyticAt_closedImmersionNormalCoordinateChange
    analyticPlane hyperplaneOver hyperplaneAnalyticι 1 2 z
  have hlast : AnalyticAt ℂ N
      (C (chartEmbeddingMap i
        ((chartAffineHomeomorph i).symm (splitNormalHomeomorph.symm (e x))))) := by
    have heq : chartEmbeddingMap i
        ((chartAffineHomeomorph i).symm (splitNormalHomeomorph.symm (e x))) = x := by
      rw [show e x = chartFlattening i q by
        exact ambientChartFlattening_apply i q,
        show splitNormalHomeomorph.symm (chartFlattening i q) =
          chartAffineHomeomorph i q by
            change splitNormalHomeomorph.symm
              (splitNormalHomeomorph (chartAffineHomeomorph i q)) = _
            rw [splitNormalHomeomorph.symm_apply_apply],
        (chartAffineHomeomorph i).symm_apply_apply]
    rw [heq, show x = Point.map hyperplaneAnalyticι z from hcenter]
    simpa only [N, C] using hNx
  have hcomp := hlast.comp (x := e x) hC
  change AnalyticAt ℂ (e.symm.trans e') (e x)
  apply hcomp.congr
  have hnhd : e.symm ⁻¹' e'.source ∈ 𝓝 (e x) := by
    have hx' : x ∈ e'.source := by
      have hz' := ComplexPoint.closedImmersionHolomorphicFlatteningChart_mem_source
        analyticPlane hyperplaneOver hyperplaneAnalyticι 1 2 z
      rw [← hcenter] at hz'
      exact hz'
    exact e.continuousAt_symm (e.map_source hx) (e'.open_source.mem_nhds (by
      rw [e.left_inv hx]
      exact hx'))
  filter_upwards [hnhd] with u hu
  change N (C (e.symm u)) = _
  rw [show e.symm u = chartEmbeddingMap i
      ((chartAffineHomeomorph i).symm (splitNormalHomeomorph.symm u)) by
    rfl]
  change N (C (e.symm u)) = e' (e.symm u)
  rfl

/-- The inverse transition from the canonical closed-immersion flattening back to the explicit
ambient affine flattening is analytic at the corresponding center as well. -/
lemma analyticAt_ambientChartFlattening_transition_canonical_symm
    (i : Fin 3) (q : ComplexPoint (analyticChart i))
    (z : ComplexPoint hyperplaneOver)
    (hcenter : chartEmbeddingMap i q = Point.map hyperplaneAnalyticι z) :
    let e := ambientChartFlattening i
    let e' := canonicalHyperplaneFlattening z
    let T := e.symm.trans e'
    AnalyticAt ℂ T.symm (T (e (chartEmbeddingMap i q))) := by
  dsimp only
  let x : ComplexPoint analyticPlane := chartEmbeddingMap i q
  let xc : ComplexPoint analyticPlane := Point.map hyperplaneAnalyticι z
  let e := ambientChartFlattening i
  let e' := canonicalHyperplaneFlattening z
  let T := e.symm.trans e'
  let C := ComplexPoint.localChart analyticPlane 2 xc
  let N := ComplexPoint.closedImmersionNormalCoordinateChange analyticPlane hyperplaneOver
    hyperplaneAnalyticι 1 2 z
  let center : (Fin 1 → ℂ) × (Fin 1 → ℂ) :=
    (ComplexPoint.localChart hyperplaneOver 1 z z, 0)
  have hx : x ∈ e.source := ⟨q, by trivial, rfl⟩
  have hxc : xc ∈ e.source := by
    change Point.map hyperplaneAnalyticι z ∈ e.source
    rw [← hcenter]
    exact hx
  have hCsrc : xc ∈ C.source := ComplexPoint.mem_localChart_source analyticPlane 2 xc
  have hCtgt : C xc ∈ C.target := C.map_source hCsrc
  have hE := analyticAt_ambientChartFlattening_comp_localChart_symm
    i xc hCtgt (by rw [C.left_inv hCsrc]; exact hxc)
  have hN := ComplexPoint.analyticAt_closedImmersionNormalCoordinateChange_symm
    analyticPlane hyperplaneOver hyperplaneAnalyticι 1 2 z
  have hNcenter : N.symm center = C xc := by
    have hleft := N.left_inv
      (ComplexPoint.closedImmersionNormalCoordinateChange_mem_source
        analyticPlane hyperplaneOver hyperplaneAnalyticι 1 2 z)
    change N.symm (N (C xc)) = C xc at hleft
    rw [ComplexPoint.closedImmersionNormalCoordinateChange_center] at hleft
    exact hleft
  have hE' : AnalyticAt ℂ (fun v ↦ e (C.symm v)) (N.symm center) := by
    rw [hNcenter]
    exact hE
  have hcomp : AnalyticAt ℂ
      (fun u ↦ e (C.symm (N.symm u))) center := by
    exact hE'.comp (x := center) hN
  have hTx : T (e x) = center := by
    change e' (e.symm (e x)) = center
    rw [e.left_inv hx]
    rw [show x = xc from hcenter]
    exact ComplexPoint.closedImmersionHolomorphicFlatteningChart_center
      analyticPlane hyperplaneOver hyperplaneAnalyticι 1 2 z
  rw [hTx]
  apply hcomp.congr
  filter_upwards with u
  rfl

/-- The two actual normal-projection coclasses agree on a sufficiently small common ambient
neighborhood.  All analytic and orientation inputs are supplied by the preceding explicit
transition theorems. -/
lemma exists_open_ambientChartFlattening_canonical_coclass_eq
    (i : Fin 3) (q : ComplexPoint (analyticChart i))
    (z : ComplexPoint hyperplaneOver)
    (hcenter : chartEmbeddingMap i q = Point.map hyperplaneAnalyticι z)
    (hS : ∀ y ∈ (ambientChartFlattening i).source,
      y ∈ Set.range (Point.map hyperplaneAnalyticι) ↔
        (ambientChartFlattening i y).2 = 0) :
    let e := ambientChartFlattening i
    let e' := canonicalHyperplaneFlattening z
    let x := chartEmbeddingMap i q
    ∃ (W : TopologicalSpace.Opens (ComplexPoint analyticPlane))
      (hW : (W : Set _) ⊆ e.source) (hW' : (W : Set _) ⊆ e'.source),
      x ∈ W ∧
      AlgebraicTopology.Singular.chartNormalProjectionCoclass (Fin 1 → ℂ) 1 e
        (Set.range (Point.map hyperplaneAnalyticι)) hS W hW =
      AlgebraicTopology.Singular.chartNormalProjectionCoclass (Fin 1 → ℂ) 1 e'
        (Set.range (Point.map hyperplaneAnalyticι))
        (ComplexPoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff
          analyticPlane hyperplaneOver hyperplaneAnalyticι 1 2 z) W hW' := by
  dsimp only
  let e := ambientChartFlattening i
  let e' := canonicalHyperplaneFlattening z
  let x := chartEmbeddingMap i q
  have hx : x ∈ e.source := ⟨q, by trivial, rfl⟩
  have hx' : x ∈ e'.source := by
    have hz' := ComplexPoint.closedImmersionHolomorphicFlatteningChart_mem_source
      analyticPlane hyperplaneOver hyperplaneAnalyticι 1 2 z
    rw [← hcenter] at hz'
    exact hz'
  have hxS : x ∈ Set.range (Point.map hyperplaneAnalyticι) := ⟨z, hcenter.symm⟩
  have h0 : (e x).2 = 0 := (hS x hx).mp hxS
  exact AlgebraicTopology.Singular.exists_open_chartNormalProjectionCoclass_eq 1 e e'
    (Set.range (Point.map hyperplaneAnalyticι)) hS
    (ComplexPoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff
      analyticPlane hyperplaneOver hyperplaneAnalyticι 1 2 z)
    x hx h0 hx'
    (analyticAt_ambientChartFlattening_transition_canonical i q z hcenter)
    (analyticAt_ambientChartFlattening_transition_canonical_symm i q z hcenter)

/-- The explicit polynomial coordinates are analytic after the inverse of any canonical
algebraic étale chart on the same projective affine chart. -/
lemma analyticAt_chartAffineHomeomorph_comp_localChart_symm
    (i : Fin 3) (z : ComplexPoint (analyticChart i)) {w : Fin 2 → ℂ}
    (hw : w ∈ (ComplexPoint.localChart (analyticChart i) 2 z).target) :
    AnalyticAt ℂ
      (fun v ↦ chartAffineHomeomorph i
        ((ComplexPoint.localChart (analyticChart i) 2 z).symm v)) w := by
  apply AnalyticAt.pi
  intro j
  rw [show (fun v ↦ chartAffineHomeomorph i
      ((ComplexPoint.localChart (analyticChart i) 2 z).symm v) j) =
      fun v ↦ chartCoordinateValue i j
        ((ComplexPoint.localChart (analyticChart i) 2 z).symm v) by
    funext v
    exact chartAffineHomeomorph_apply i _ j]
  exact ComplexPoint.analyticAt_localChart_symm_evaluate (analyticChart i) 2 z hw
    ⊤ (chartCoordinate i j) trivial

/-- The inverse transition, from the permuted canonical chart to the explicit affine
flattening, is complex analytic as well. -/
lemma analyticAt_chartFlattening_transition_splitLocalChart_symm
    (i : Fin 3) (z : ComplexPoint (analyticChart i))
    (v : (Fin 1 → ℂ) × (Fin 1 → ℂ))
    (hv : v ∈ ((chartFlattening i).symm.trans (splitLocalChart i z)).source) :
    AnalyticAt ℂ ((chartFlattening i).symm.trans (splitLocalChart i z)).symm
      (((chartFlattening i).symm.trans (splitLocalChart i z)) v) := by
  let T := (chartFlattening i).symm.trans (splitLocalChart i z)
  have hv' := T.map_source hv
  change AnalyticAt ℂ ((splitLocalChart i z).symm.trans (chartFlattening i)) (T v)
  rw [OpenPartialHomeomorph.trans_target] at hv'
  have hy : splitNormalHomeomorph.symm (T v) ∈
      (ComplexPoint.localChart (analyticChart i) 2 z).target := by
    have hy' := hv'.1
    rw [splitLocalChart, OpenPartialHomeomorph.trans_target] at hy'
    exact hy'.2
  have h1 := analyticAt_splitNormalHomeomorph_symm (T v)
  have h2 := analyticAt_chartAffineHomeomorph_comp_localChart_symm i z hy
  have h3 := analyticAt_splitNormalHomeomorph
    (chartAffineHomeomorph i
      ((ComplexPoint.localChart (analyticChart i) 2 z).symm
        (splitNormalHomeomorph.symm (T v))))
  have hmiddle : AnalyticAt ℂ
      (fun u ↦ chartAffineHomeomorph i
        ((ComplexPoint.localChart (analyticChart i) 2 z).symm
          (splitNormalHomeomorph.symm u))) (T v) := by
    simpa only [Function.comp_def] using h2.comp (x := T v) h1
  have hcomp : AnalyticAt ℂ
      (fun u ↦ splitNormalHomeomorph
        (chartAffineHomeomorph i
          ((ComplexPoint.localChart (analyticChart i) 2 z).symm
            (splitNormalHomeomorph.symm u)))) (T v) := by
    exact h3.comp (x := T v) hmiddle
  change AnalyticAt ℂ
    (fun u ↦ splitNormalHomeomorph
      (chartAffineHomeomorph i
        ((ComplexPoint.localChart (analyticChart i) 2 z).symm
          (splitNormalHomeomorph.symm u)))) (T v)
  exact hcomp

/-- The normal component of the explicit flattening chart is literally `X₀ / Xᵢ`. -/
lemma chartFlattening_normal_eq_coordinate (i : Fin 3)
    (z : ComplexPoint (analyticChart i)) :
    (chartFlattening i z).2 = fun _ ↦ chartCoordinateValue i 0 z := by
  ext
  exact chartAffineHomeomorph_apply i z 0

/- The tangent coordinate of the explicit flattening is the second affine ratio. -/
lemma chartFlattening_tangent_eq_coordinate (i : Fin 3)
    (z : ComplexPoint (analyticChart i)) :
    (chartFlattening i z).1 = fun _ ↦ chartCoordinateValue i 1 z := by
  ext
  exact chartAffineHomeomorph_apply i z 1

/-- The zero set of the literal normal coordinate on the `i`-th standard chart. -/
def chartHyperplaneSupport (i : Fin 3) : Set (ComplexPoint (analyticChart i)) :=
  {z | chartCoordinateValue i 0 z = 0}

/-- The explicit global chart flattens the zero set of `X₀ / Xᵢ` to the zero-normal plane. -/
lemma chartFlattening_support_iff (i : Fin 3) :
    ∀ y ∈ (chartFlattening i).source,
      y ∈ chartHyperplaneSupport i ↔ (chartFlattening i y).2 = 0 := by
  intro y hy
  rw [chartFlattening_normal_eq_coordinate]
  constructor
  · intro h
    funext j
    fin_cases j
    exact h
  · intro h
    exact congrFun h 0

/-- On the first affine chart, the ambient lifted explicit chart flattens the actual analytic
image of the scheme-theoretic hyperplane. -/
lemma ambientChartFlattening_one_support_iff :
    ∀ y ∈ (ambientChartFlattening 1).source,
      y ∈ Set.range (Point.map hyperplaneOverι) ↔
        (ambientChartFlattening 1 y).2 = 0 := by
  rintro y ⟨z, hz, rfl⟩
  rw [ambientChartFlattening_apply]
  have hc := chartFlattening_support_iff 1 z hz
  have hn := mem_firstNormalComplement_iff_not_mem_hyperplane z
  change firstNormalCoordinate z = 0 ↔ _ at hc
  change firstNormalCoordinate z ≠ 0 ↔ _ at hn
  tauto

/-- On the second affine chart, the ambient lifted explicit chart flattens the actual analytic
image of the scheme-theoretic hyperplane. -/
lemma ambientChartFlattening_two_support_iff :
    ∀ y ∈ (ambientChartFlattening 2).source,
      y ∈ Set.range (Point.map hyperplaneOverι) ↔
        (ambientChartFlattening 2 y).2 = 0 := by
  rintro y ⟨z, hz, rfl⟩
  rw [ambientChartFlattening_apply]
  have hc := chartFlattening_support_iff 2 z hz
  have hn := mem_secondNormalComplement_iff_not_mem_hyperplane z
  change secondNormalCoordinate z = 0 ↔ _ at hc
  change secondNormalCoordinate z ≠ 0 ↔ _ at hn
  tauto

/-- First-chart support flattening, with the hyperplane immersion written in the transparent
ambient presentation used by the canonical chart. -/
lemma ambientChartFlattening_one_support_iff_analytic :
    ∀ y ∈ (ambientChartFlattening 1).source,
      y ∈ Set.range (Point.map hyperplaneAnalyticι) ↔
        (ambientChartFlattening 1 y).2 = 0 := by
  rw [hyperplaneAnalyticι_eq_hyperplaneOverι]
  exact ambientChartFlattening_one_support_iff

/-- Second-chart support flattening in the same transparent ambient presentation. -/
lemma ambientChartFlattening_two_support_iff_analytic :
    ∀ y ∈ (ambientChartFlattening 2).source,
      y ∈ Set.range (Point.map hyperplaneAnalyticι) ↔
        (ambientChartFlattening 2 y).2 = 0 := by
  rw [hyperplaneAnalyticι_eq_hyperplaneOverι]
  exact ambientChartFlattening_two_support_iff

/- The two explicit affine charts cover every complex point of the coordinate hyperplane. -/
lemma hyperplaneSupport_mem_chart_one_or_two
    (x : ComplexPoint analyticPlane)
    (hx : x ∈ Set.range (Point.map hyperplaneOverι)) :
    ∃ (i : Fin 2) (z : ComplexPoint (analyticChart i.succ)),
      x = chartEmbeddingMap i.succ z := by
  obtain ⟨y, rfl⟩ := hx
  have hyall : y.underlying ∈
      (⨆ i : Fin 2, hyperplaneι ⁻¹ᵁ chartOpen i.succ : hyperplane.Opens) := by
    rw [iSup_hyperplane_preimage_chartOpen_succ_eq_top]
    trivial
  obtain ⟨i, hyi⟩ := TopologicalSpace.Opens.mem_iSup.mp hyall
  let x' := Point.map hyperplaneOverι y
  have hxopen : x' ∈ Point.overOpen (chartOpen i.succ) := hyi
  let z := ComplexPoint.asOpenPoint analyticPlane (chartOpen i.succ) x' hxopen
  refine ⟨i, z, ?_⟩
  have h := congrArg Subtype.val
    ((ComplexPoint.openEquiv analyticPlane (chartOpen i.succ)).right_inv
      ⟨x', hxopen⟩)
  change x' = Point.map (ComplexPoint.openInclusion analyticPlane (chartOpen i.succ)) z
  exact h.symm

/-- The first-chart presentation of the normal coordinate is definitionally the evaluation
of the direct regular section `X₀ / X₁`. -/
lemma firstNormalCoordinate_eq_evaluate_firstNormalSection
    (z : ComplexPoint (analyticChart 1)) :
    firstNormalCoordinate z = Point.evaluate ⊤ firstNormalSection z := by
  rfl

/-- The zero set flattened by the explicit first chart is exactly the complement of the
previously constructed punctured first chart. -/
lemma chartHyperplaneSupport_one_eq_compl :
    chartHyperplaneSupport 1 = firstNormalComplementᶜ := by
  ext z
  change firstNormalCoordinate z = 0 ↔ ¬ firstNormalValue z ≠ 0
  change firstNormalCoordinate z = 0 ↔ ¬ firstNormalCoordinate z ≠ 0
  tauto

/-- The zero set flattened by the explicit second chart is exactly the complement of the
previously constructed punctured second chart. -/
lemma chartHyperplaneSupport_two_eq_compl :
    chartHyperplaneSupport 2 = secondNormalComplementᶜ := by
  ext z
  change secondNormalCoordinate z = 0 ↔ ¬ secondNormalCoordinate z ≠ 0
  tauto

/-- On the actual punctured flattened neighbourhood, the normal function used by the winding
construction is still literally the evaluated projective coordinate `X₀ / Xᵢ`. -/
lemma flattenedNormalCoordinate_eq_chartCoordinate (i : Fin 3)
    (x : ComplexPoint (analyticChart i)) (hx : x ∈ (chartFlattening i).source)
    (w : ChernWinding.puncturedSpace
      ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening i) x hx :
        TopologicalSpace.Opens (ComplexPoint (analyticChart i))) :
          Set (ComplexPoint (analyticChart i)))
      (chartHyperplaneSupport i)) :
    ChernWinding.flattenedNormalCoordinate (Fin 1 → ℂ) (chartFlattening i)
      (chartFlattening_support_iff i) x hx w =
        chartCoordinateValue i 0 w.1.1 := by
  change ((chartFlattening i w.1.1).2) 0 = _
  rw [chartFlattening_normal_eq_coordinate]

end AlgebraicGeometry.ProjectivePlane.AnalyticNormalization
