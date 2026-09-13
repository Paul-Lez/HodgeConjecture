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

public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClass
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClassGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.LocalGenerator

/-!
# LocalGenerator, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.LocalGenerator`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Topology
namespace AlgebraicGeometry
attribute [local instance] overSpecAlgebra
variable {d n : ℕ} {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom] {x : X.left}
  [SmoothOfRelativeDimension d X.hom]
namespace CycleComponentSeparateLocalCoordinates
variable (C : CycleComponentSeparateLocalCoordinates X x d n)
attribute [local instance] coordinateRingAlgebra
attribute [local instance] coordinateRingComplexAlgebra
attribute [local instance] coordinateRingScalarTower
attribute [local instance] coordinateRingEtale

/-- The selected smooth component point regarded as a complex point of the smooth locus. -/
def smoothPoint : ComplexPoint (componentSmoothScheme X x) :=
  ComplexPoint.asOpenPoint (Over.mk (cycleComponentι X.left x ≫ X.hom))
    (componentSmoothLocus X x)
    C.point C.point_mem_smoothLocus

/-- The selected affine component neighborhood, bundled over the complex base. -/
abbrev neighborhoodScheme : Over (Spec ↧ℂ) :=
  Over.mk C.neighborhoodStructureMap

/-- The selected smooth point regarded as a complex point of its affine neighborhood. -/
def neighborhoodPoint :
    ComplexPoint C.neighborhoodScheme :=
  ComplexPoint.asOpenPoint (componentSmoothScheme X x) C.componentNeighborhood
    (smoothPoint C) (by
      change (smoothPoint C).underlying ∈ C.componentNeighborhood
      have hmap : Point.map (ComplexPoint.openInclusion (Over.mk (cycleComponentι X.left x ≫ X.hom))
          (componentSmoothLocus X x)) (smoothPoint C) =
          C.point :=
        congrArg Subtype.val
          ((ComplexPoint.openEquiv (Over.mk (cycleComponentι X.left x ≫ X.hom))
            (componentSmoothLocus X x)).apply_symm_apply
              ⟨C.point, C.point_mem_smoothLocus⟩)
      have hu := congrArg Point.underlying hmap
      rw [Point.underlying_map] at hu
      have hu' : (smoothPoint C).underlying =
          (⟨C.point.underlying, C.point_mem_smoothLocus⟩ :
            (componentSmoothLocus X x).toScheme) := Subtype.ext hu
      rw [hu']
      exact C.point_mem_componentNeighborhood)

/-- The affine neighborhood's canonical map to its spectrum respects the complex structure
induced by the exact component coordinates. -/
lemma neighborhoodToSpecΓ_over :
    C.componentNeighborhood.toScheme.toSpecΓ ≫
        ComplexPoint.affineSpecStructureMap Γ(C.componentNeighborhood.toScheme, ⊤) =
      C.neighborhoodStructureMap := by
  let φ : ↧ℂ ⟶ Γ(C.componentNeighborhood.toScheme, ⊤) :=
    CommRingCat.ofHom MvPolynomial.C ≫
      CommRingCat.ofHom C.coordinateRingHomOnNeighborhood
  exact ext_to_Spec ((ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ).trans
    C.C_comp_coordinateRingHomOnNeighborhood)

/-- The canonical affine-spectrum isomorphism, bundled over `Spec ℂ`. -/
def neighborhoodToSpecΓIso : C.neighborhoodScheme ≅
    Over.mk (ComplexPoint.affineSpecStructureMap Γ(C.componentNeighborhood.toScheme, ⊤)) := by
  letI : IsAffine C.componentNeighborhood.toScheme :=
    C.componentNeighborhood_isAffine
  letI : IsIso C.componentNeighborhood.toScheme.toSpecΓ :=
    IsAffine.affine
  exact Over.isoMk (asIso C.componentNeighborhood.toScheme.toSpecΓ)
    C.neighborhoodToSpecΓ_over

/-- Complex points of the affine component neighborhood as complex algebra homomorphisms on its
coordinate ring. -/
def neighborhoodPointAlgHomHomeomorph :
    @Homeomorph
      (ComplexPoint C.neighborhoodScheme)
      (Γ(C.componentNeighborhood.toScheme, ⊤) →ₐ[ℂ] ℂ)
      Point.analyticTopology
      (ComplexPoint.affineAlgebraHomTopology Γ(C.componentNeighborhood.toScheme, ⊤)) :=
  (Point.isoMapHomeomorph C.neighborhoodToSpecΓIso).trans
    (ComplexPoint.affineSpecHomeomorph Γ(C.componentNeighborhood.toScheme, ⊤))

/-- The affine algebra-homomorphism coordinate of a neighborhood point evaluates global
regular sections in the usual way. -/
lemma neighborhoodPointAlgHomHomeomorph_apply
    (z : ComplexPoint C.neighborhoodScheme)
    (r : Γ(C.componentNeighborhood.toScheme, ⊤)) :
    C.neighborhoodPointAlgHomHomeomorph z r = Point.evaluate ⊤ r z := by
  change ComplexPoint.affineSpecEquiv Γ(C.componentNeighborhood.toScheme, ⊤)
      (Point.isoMapHomeomorph C.neighborhoodToSpecΓIso z) r = _
  rw [ComplexPoint.affineSpecEquiv_apply, Point.isoMapHomeomorph_apply,
    Point.evaluate_map]
  change Point.evaluate ⊤
      (C.componentNeighborhood.toScheme.toSpecΓ.appTop
        ((Scheme.ΓSpecIso (.of Γ(C.componentNeighborhood.toScheme, ⊤))).inv r)) z = _
  rw [Scheme.toSpecΓ_appTop]
  have h := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso (.of Γ(C.componentNeighborhood.toScheme, ⊤))).inv_hom_id) r
  exact congrArg (fun s ↦ Point.evaluate ⊤ s z) h

/-- The local analytic chart supplied by the exact étale component coordinates. -/
def neighborhoodProjectionChart :
    OpenPartialHomeomorph
      (ComplexPoint C.neighborhoodScheme)
      (Fin n → ℂ) :=
  C.neighborhoodPointAlgHomHomeomorph.toOpenPartialHomeomorph |>.trans
    (ComplexAlgHom.etaleAlgHomProjectionChart
      Γ(C.componentNeighborhood.toScheme, ⊤)
      (C.neighborhoodPointAlgHomHomeomorph C.neighborhoodPoint))

/-- The selected smooth point belongs to the source of the exact analytic component chart. -/
lemma neighborhoodPoint_mem_projectionChart_source :
    C.neighborhoodPoint ∈ C.neighborhoodProjectionChart.source := by
  exact ⟨by simp, ComplexAlgHom.mem_etaleAlgHomProjectionChart_source
    Γ(C.componentNeighborhood.toScheme, ⊤)
      (C.neighborhoodPointAlgHomHomeomorph C.neighborhoodPoint)⟩

/-- On its source, the component chart is exactly restriction of a complex point along the
retained polynomial coordinate map, followed by evaluation on the coordinate variables. -/
lemma neighborhoodProjectionChart_apply_of_mem
    (z : ComplexPoint C.neighborhoodScheme)
    (hz : z ∈ C.neighborhoodProjectionChart.source) :
    C.neighborhoodProjectionChart z =
      ComplexAlgHom.mvPolynomialAlgHomHomeomorph n
        (ComplexAlgHom.etaleBaseAlgHom Γ(C.componentNeighborhood.toScheme, ⊤)
          (C.neighborhoodPointAlgHomHomeomorph z)) := by
  exact ComplexAlgHom.etaleAlgHomProjectionChart_apply_of_mem (n := n)
    Γ(C.componentNeighborhood.toScheme, ⊤)
      (C.neighborhoodPointAlgHomHomeomorph C.neighborhoodPoint)
      (C.neighborhoodPointAlgHomHomeomorph z) hz.2

/-- Evaluation of a global section of the affine component neighborhood is analytic along the
inverse of its exact projection chart. -/
lemma analyticAt_neighborhoodProjectionChart_symm_evaluate_top
    {w : Fin n → ℂ} (hw : w ∈ C.neighborhoodProjectionChart.target)
    (r : Γ(C.componentNeighborhood.toScheme, ⊤)) :
    AnalyticAt ℂ (fun v ↦ Point.evaluate ⊤ r
      (C.neighborhoodProjectionChart.symm v)) w := by
  let u := C.neighborhoodPointAlgHomHomeomorph C.neighborhoodPoint
  have hw' : w ∈ (ComplexAlgHom.etaleAlgHomProjectionChart
      Γ(C.componentNeighborhood.toScheme, ⊤) u).target := by
    rw [neighborhoodProjectionChart, OpenPartialHomeomorph.trans_target] at hw
    exact hw.1
  have h := ComplexAlgHom.analyticAt_etaleAlgHomProjectionChart_symm_apply
    Γ(C.componentNeighborhood.toScheme, ⊤) u hw' r
  have h' : AnalyticAt ℂ (fun v ↦ C.neighborhoodPointAlgHomHomeomorph
      (C.neighborhoodProjectionChart.symm v) r) w := by
    apply h.congr
    filter_upwards with v
    simp only [neighborhoodProjectionChart, OpenPartialHomeomorph.coe_trans_symm,
      Function.comp_apply, Homeomorph.toOpenPartialHomeomorph_symm_apply]
    rw [Homeomorph.apply_symm_apply]
  simpa only [C.neighborhoodPointAlgHomHomeomorph_apply] using h'

/-- Evaluation of an arbitrary regular section defined near the inverse-chart point is analytic
there.  The proof shrinks inside the affine neighborhood to a principal open and represents the
section by a quotient of global sections. -/
lemma analyticAt_neighborhoodProjectionChart_symm_evaluate
    {w : Fin n → ℂ} (hw : w ∈ C.neighborhoodProjectionChart.target)
    (W : C.componentNeighborhood.toScheme.Opens) (s : Γ(C.componentNeighborhood.toScheme, W))
    (hW : C.neighborhoodProjectionChart.symm w ∈ Point.overOpen W) :
    AnalyticAt ℂ (fun v ↦ Point.evaluate W s
      (C.neighborhoodProjectionChart.symm v)) w := by
  let Y := C.neighborhoodScheme
  let : IsAffine Y.left := C.componentNeighborhood_isAffine
  let y : ComplexPoint Y := C.neighborhoodProjectionChart.symm w
  obtain ⟨g, hgW, hyg⟩ :=
    (isAffineOpen_top Y.left).exists_basicOpen_le
      (V := W) ⟨y.underlying, hW⟩ trivial
  let t : Γ(Y.left, Y.left.basicOpen g) := Y.left.presheaf.map (homOfLE hgW).op s
  obtain ⟨k, a, hquot⟩ :=
    ComplexPoint.exists_evaluate_affine_basicOpen_eq_div (X := Y) g t
  have hyg' : y ∈ Point.overOpen (Y.left.basicOpen g) := hyg
  have hgzero : Point.evaluate ⊤ g y ≠ 0 :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero g y trivial).mp hyg'
  have ha := C.analyticAt_neighborhoodProjectionChart_symm_evaluate_top hw a
  have hg := C.analyticAt_neighborhoodProjectionChart_symm_evaluate_top hw g
  have hrat : AnalyticAt ℂ
      (fun v ↦ Point.evaluate ⊤ a (C.neighborhoodProjectionChart.symm v) /
        Point.evaluate ⊤ g (C.neighborhoodProjectionChart.symm v) ^ k) w :=
    ha.div (hg.pow k) (pow_ne_zero k hgzero)
  apply hrat.congr
  have hcontinuous : ContinuousAt C.neighborhoodProjectionChart.symm w :=
    C.neighborhoodProjectionChart.continuousAt_symm hw
  have heventually : C.neighborhoodProjectionChart.symm ⁻¹'
      Point.overOpen (Y.left.basicOpen g) ∈ 𝓝 w :=
    hcontinuous ((Point.isOpen_overOpen (Y.left.basicOpen g)).mem_nhds hyg')
  filter_upwards [heventually] with v hv
  let yv : ComplexPoint Y :=
    C.neighborhoodProjectionChart.symm v
  have hres := Point.evaluate_res hgW s yv hv
  exact (hres.trans (hquot yv hv)).symm

end CycleComponentSeparateLocalCoordinates
end AlgebraicGeometry
end
