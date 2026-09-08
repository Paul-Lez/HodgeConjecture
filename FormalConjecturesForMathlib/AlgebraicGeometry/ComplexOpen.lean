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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexPoints

/-!
# Complex points of open subschemes

Analytification respects restriction to an open subscheme. More precisely, complex points of an
open subscheme are canonically homeomorphic to the corresponding open subspace of the complex
points of the ambient scheme. In particular, an open immersion of this form induces an open
embedding on complex points.
-/

@[expose] public section

open CategoryTheory Topology

namespace AlgebraicGeometry.ComplexPoint

noncomputable section

noncomputable local instance {Y : Scheme} {f : Y ⟶ Spec (.of ℂ)} :
    TopologicalSpace (ComplexPoint Y f) := analyticTopology

variable {X : Scheme} (U : X.Opens) (structureMap : X ⟶ Spec (.of ℂ))

/-- The structure morphism on an open subscheme. -/
abbrev openStructureMap : U.toScheme ⟶ Spec (.of ℂ) :=
  U.ι ≫ structureMap

/-- The image of a complex point lying in `U` is contained in the image of its inclusion. -/
lemma point_range_subset (z : ComplexPoint X structureMap) (hz : z ∈ overOpen U) :
    Set.range z.1 ⊆ Set.range U.ι := by
  rintro y ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  have hx : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
  subst x
  exact hz

/-- A complex point in an open set factors through the corresponding open subscheme. -/
def liftToOpen (z : ComplexPoint X structureMap) (hz : z ∈ overOpen U) :
    Spec (.of ℂ) ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι z.1 (point_range_subset U structureMap z hz)

@[reassoc (attr := simp)]
lemma liftToOpen_fac (z : ComplexPoint X structureMap) (hz : z ∈ overOpen U) :
    liftToOpen U structureMap z hz ≫ U.ι = z.1 :=
  IsOpenImmersion.lift_fac _ _ _

/-- A point of `X` lying in `U`, regarded as a complex point of the open subscheme `U`. -/
def asOpenPoint (z : ComplexPoint X structureMap) (hz : z ∈ overOpen U) :
    ComplexPoint U.toScheme (openStructureMap U structureMap) :=
  ⟨liftToOpen U structureMap z hz, by
    change liftToOpen U structureMap z hz ≫ (U.ι ≫ structureMap) = 𝟙 _
    rw [← Category.assoc, liftToOpen_fac, z.2]⟩

/-- Mapping a point lifted to an open subscheme back to the ambient scheme recovers the original
complex point. -/
@[simp]
lemma map_asOpenPoint (z : ComplexPoint X structureMap) (hz : z ∈ overOpen U) :
    map U.ι rfl (asOpenPoint U structureMap z hz) = z := by
  apply Subtype.ext
  exact liftToOpen_fac U structureMap z hz

/-- Complex points of an open subscheme are the ambient complex points lying in the open. -/
def openEquiv :
    ComplexPoint U.toScheme (openStructureMap U structureMap) ≃
      {z : ComplexPoint X structureMap // z ∈ overOpen U} where
  toFun z := ⟨map U.ι rfl z, by
    change (map U.ι rfl z).underlying ∈ U
    rw [underlying_map]
    exact z.underlying.property⟩
  invFun z := asOpenPoint U structureMap z.1 z.2
  left_inv z := by
    apply Subtype.ext
    symm
    apply IsOpenImmersion.lift_uniq U.ι (map U.ι rfl z).1
    simp [map]
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact liftToOpen_fac U structureMap z.1 z.2

@[simp]
lemma openEquiv_coe (z : ComplexPoint U.toScheme (openStructureMap U structureMap)) :
    (openEquiv U structureMap z).1 = map U.ι rfl z :=
  rfl

/-- The map from an open subscheme to its ambient open subspace is continuous. -/
lemma continuous_openEquiv :
    @Continuous
      (ComplexPoint U.toScheme (openStructureMap U structureMap))
      {z : ComplexPoint X structureMap // z ∈ overOpen U}
      analyticTopology (TopologicalSpace.induced Subtype.val analyticTopology)
      (openEquiv U structureMap) := by
  exact @Continuous.subtype_mk
    (ComplexPoint X structureMap)
    (ComplexPoint U.toScheme (openStructureMap U structureMap))
    analyticTopology analyticTopology
    (fun z ↦ z ∈ overOpen U) (map U.ι rfl)
    (continuous_map U.ι rfl) _

/-- Evaluation is unchanged when both a point and a section are transported across equal opens. -/
lemma evaluate_eq {Y : Scheme} {structureMapY : Y ⟶ Spec (.of ℂ)}
    {V W : Y.Opens} (e : V = W) (t : Γ(Y, V)) (z : ComplexPoint Y structureMapY) :
    evaluate V t z = evaluate W (Y.presheaf.map (eqToHom e.symm).op t) z := by
  subst e
  simp

/-- Evaluation commutes with the equivalence between an open subscheme and its ambient open. -/
lemma evaluate_openEquiv {V : U.toScheme.Opens} (t : Γ(U.toScheme, V))
    (z : ComplexPoint U.toScheme (openStructureMap U structureMap)) :
    evaluate (U.ι ''ᵁ V) ((U.ι.appIso V).inv t) (map U.ι rfl z) =
      evaluate V t z := by
  rw [evaluate_map]
  let e : U.ι ⁻¹ᵁ U.ι ''ᵁ V = V := U.ι.preimage_image_eq V
  let q := U.ι.app (U.ι ''ᵁ V) ((U.ι.appIso V).inv t)
  have hq : q = U.toScheme.presheaf.map (eqToHom e).op t := by
    change ((U.ι.appIso V).inv ≫ U.ι.app (U.ι ''ᵁ V)) t = _
    rw [U.ι.appIso_inv_app]
  calc
    evaluate (U.ι ⁻¹ᵁ U.ι ''ᵁ V) q z =
        evaluate V (U.toScheme.presheaf.map (eqToHom e.symm).op q) z :=
      evaluate_eq e q z
    _ = evaluate V t z := by
      congr 2
      rw [hq]
      change (U.toScheme.presheaf.map (eqToHom e).op ≫
        U.toScheme.presheaf.map (eqToHom e.symm).op) t = t
      rw [← Functor.map_comp]
      simp
      rfl

/-- The inverse map from the ambient open subspace is continuous. -/
lemma continuous_openEquiv_symm :
    @Continuous
      {z : ComplexPoint X structureMap // z ∈ overOpen U}
      (ComplexPoint U.toScheme (openStructureMap U structureMap))
      (TopologicalSpace.induced Subtype.val analyticTopology) analyticTopology
      (openEquiv U structureMap).symm := by
  rw [continuous_generateFrom_iff]
  rintro W ⟨V, t, O, hO, rfl⟩
  let A : Set (ComplexPoint X structureMap) := overOpen (U.ι ''ᵁ V) ∩
    evaluate (U.ι ''ᵁ V) ((U.ι.appIso V).inv t) ⁻¹' O
  have hA : @IsOpen (ComplexPoint X structureMap) analyticTopology A :=
    isOpen_overOpen_inter_preimage _ _ _ hO
  rw [show (openEquiv U structureMap).symm ⁻¹'
      (overOpen V ∩ evaluate V t ⁻¹' O) = Subtype.val ⁻¹' A by
    ext y
    let z := (openEquiv U structureMap).symm y
    have hy : openEquiv U structureMap z = y :=
      (openEquiv U structureMap).apply_symm_apply y
    rw [← hy]
    simp only [Set.mem_preimage, Equiv.symm_apply_apply, Set.mem_inter_iff]
    change (z ∈ overOpen V ∧ evaluate V t z ∈ O) ↔
      (map U.ι rfl z ∈ overOpen (U.ι ''ᵁ V) ∧
        evaluate (U.ι ''ᵁ V) ((U.ι.appIso V).inv t) (map U.ι rfl z) ∈ O)
    rw [evaluate_openEquiv]
    constructor
    · rintro ⟨hzV, ht⟩
      exact ⟨by simpa [overOpen] using hzV, ht⟩
    · rintro ⟨hzV, ht⟩
      exact ⟨by simpa [overOpen] using hzV, ht⟩]
  exact @isOpen_induced
    {z : ComplexPoint X structureMap // z ∈ overOpen U}
    (ComplexPoint X structureMap) analyticTopology Subtype.val A hA

/-- Analytification of an open subscheme is the corresponding analytic open subspace. -/
def openHomeomorph :
    @Homeomorph
      (ComplexPoint U.toScheme (openStructureMap U structureMap))
      {z : ComplexPoint X structureMap // z ∈ overOpen U}
      analyticTopology (TopologicalSpace.induced Subtype.val analyticTopology) where
  toEquiv := openEquiv U structureMap
  continuous_toFun := continuous_openEquiv U structureMap
  continuous_invFun := continuous_openEquiv_symm U structureMap

/-- Inclusion of an open subscheme induces an open embedding on complex points. -/
lemma isOpenEmbedding_map_open :
    IsOpenEmbedding (map U.ι rfl :
      ComplexPoint U.toScheme (openStructureMap U structureMap) → ComplexPoint X structureMap) := by
  have hU : IsOpen (overOpen U : Set (ComplexPoint X structureMap)) := isOpen_overOpen U
  have h := hU.isOpenEmbedding_subtypeVal.comp (openHomeomorph U structureMap).isOpenEmbedding
  simpa [Function.comp_def, openHomeomorph, openEquiv] using h

end


end AlgebraicGeometry.ComplexPoint
