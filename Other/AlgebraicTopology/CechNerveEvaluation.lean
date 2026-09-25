/-
Copyright 2026 Paul Lezeau and The Formal Conjectures Authors.

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

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
This module is adapted from Paul Lezeau's `sphere-six-complex`, file
`BoundarySevenCechRowIdentificationsProof.lean`, commit
`b200b3fa92c64b73f3f212026f191f85364f05e3`.

# Evaluating an augmented Čech nerve of simplicial sets

Limits of simplicial sets are computed degreewise.  Consequently, evaluation in a fixed
simplicial degree commutes canonically with the wide pullbacks defining a Čech nerve.  The
degreewise isomorphisms are natural in the Čech direction and extend to an isomorphism of
augmented simplicial objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

namespace AlgebraicTopology

/-- Evaluate an arrow of simplicial sets in one simplicial degree. -/
public noncomputable def cechPresentationEvaluationArrow
    (A : Arrow SSet) (q : ℕ) : Arrow (Type 0) :=
  Arrow.mk (A.hom.app (Opposite.op (SimplexCategory.mk q)))

/-- Evaluation identifies the wide-cospan diagram defining an `SSet` Čech level with the
wide-cospan diagram of the evaluated arrow. -/
public noncomputable def cechPresentationWideCospanEvaluationIso
    (A : Arrow SSet) (p q : ℕ) :
    WidePullbackShape.wideCospan A.right
        (fun _ : Fin (p + 1) ↦ A.left) (fun _ ↦ A.hom) ⋙
          (evaluation SimplexCategoryᵒᵖ (Type 0)).obj
            (Opposite.op (SimplexCategory.mk q)) ≅
      WidePullbackShape.wideCospan
        ((cechPresentationEvaluationArrow A q).right)
        (fun _ : Fin (p + 1) ↦ (cechPresentationEvaluationArrow A q).left)
        (fun _ ↦ (cechPresentationEvaluationArrow A q).hom) :=
  NatIso.ofComponents
    (fun x ↦ by cases x <;> exact Iso.refl _)
    (fun f ↦ by cases f <;> rfl)

/-- Evaluation in simplicial degree `q` commutes with the wide pullback defining Čech level
`p`. -/
public noncomputable def cechPresentationEvaluationIso
    (A : Arrow SSet) (p q : ℕ) :
    (A.augmentedCechNerve.left.obj
        (Opposite.op (SimplexCategory.mk p))).obj
          (Opposite.op (SimplexCategory.mk q)) ≅
      (cechPresentationEvaluationArrow A q).augmentedCechNerve.left.obj
        (Opposite.op (SimplexCategory.mk p)) := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type 0)).obj
    (Opposite.op (SimplexCategory.mk q))
  let D := WidePullbackShape.wideCospan A.right
    (fun _ : Fin (p + 1) ↦ A.left) (fun _ ↦ A.hom)
  change E.obj (widePullback A.right (fun _ : Fin (p + 1) ↦ A.left)
      (fun _ ↦ A.hom)) ≅
    widePullback (E.obj A.right) (fun _ : Fin (p + 1) ↦ E.obj A.left)
      (fun _ ↦ E.map A.hom)
  exact preservesLimitIso E D ≪≫ HasLimit.isoOfNatIso
    (cechPresentationWideCospanEvaluationIso A p q)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
public theorem cechPresentationEvaluationIso_hom_π
    (A : Arrow SSet) (p q : ℕ) (i : Fin (p + 1)) :
    (cechPresentationEvaluationIso A p q).hom ≫
        WidePullback.π
          (fun _ : Fin (p + 1) ↦
            (cechPresentationEvaluationArrow A q).hom) i =
      ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.π (fun _ : Fin (p + 1) ↦ A.hom) i) ≫
        (cechPresentationWideCospanEvaluationIso A p q).hom.app (some i) := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type 0)).obj
    (Opposite.op (SimplexCategory.mk q))
  let D := WidePullbackShape.wideCospan A.right
    (fun _ : Fin (p + 1) ↦ A.left) (fun _ ↦ A.hom)
  let B := cechPresentationEvaluationArrow A q
  let D' := WidePullbackShape.wideCospan B.right
    (fun _ : Fin (p + 1) ↦ B.left) (fun _ ↦ B.hom)
  change ((preservesLimitIso E D ≪≫ HasLimit.isoOfNatIso
      (cechPresentationWideCospanEvaluationIso A p q)).hom) ≫
      limit.π D' (some i) = E.map (limit.π D (some i)) ≫
        (cechPresentationWideCospanEvaluationIso A p q).hom.app (some i)
  dsimp only [D']
  rw [Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π
    (cechPresentationWideCospanEvaluationIso A p q) (some i), ← Category.assoc,
    preservesLimitIso_hom_π]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
public theorem cechPresentationEvaluationIso_hom_base
    (A : Arrow SSet) (p q : ℕ) :
    (cechPresentationEvaluationIso A p q).hom ≫
        WidePullback.base
          (fun _ : Fin (p + 1) ↦ (cechPresentationEvaluationArrow A q).hom) =
      ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.base (fun _ : Fin (p + 1) ↦ A.hom)) ≫
        (cechPresentationWideCospanEvaluationIso A p q).hom.app none := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type 0)).obj
    (Opposite.op (SimplexCategory.mk q))
  let D := WidePullbackShape.wideCospan A.right
    (fun _ : Fin (p + 1) ↦ A.left) (fun _ ↦ A.hom)
  let B := cechPresentationEvaluationArrow A q
  let D' := WidePullbackShape.wideCospan B.right
    (fun _ : Fin (p + 1) ↦ B.left) (fun _ ↦ B.hom)
  change ((preservesLimitIso E D ≪≫ HasLimit.isoOfNatIso
      (cechPresentationWideCospanEvaluationIso A p q)).hom) ≫
      limit.π D' none = E.map (limit.π D none) ≫
        (cechPresentationWideCospanEvaluationIso A p q).hom.app none
  dsimp only [D']
  rw [Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π
    (cechPresentationWideCospanEvaluationIso A p q) none, ← Category.assoc,
    preservesLimitIso_hom_π]

set_option backward.isDefEq.respectTransparency false in
public theorem cechPresentationEvaluation_map_π_comp_diagramIso
    (A : Arrow SSet) (p q : ℕ) (i : Fin (p + 1)) :
    ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.π (fun _ : Fin (p + 1) ↦ A.hom) i) ≫
        (cechPresentationWideCospanEvaluationIso A p q).hom.app (some i) =
      ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.π (fun _ : Fin (p + 1) ↦ A.hom) i) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
public theorem cechPresentationEvaluation_map_base_comp_diagramIso
    (A : Arrow SSet) (p q : ℕ) :
    ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.base (fun _ : Fin (p + 1) ↦ A.hom)) ≫
        (cechPresentationWideCospanEvaluationIso A p q).hom.app none =
      ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.base (fun _ : Fin (p + 1) ↦ A.hom)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
public theorem cechPresentationEvaluationIso_naturality
    (A : Arrow SSet) (q : ℕ) {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (A.augmentedCechNerve.left.map f) ≫
        (cechPresentationEvaluationIso A b.unop.len q).hom =
      (cechPresentationEvaluationIso A a.unop.len q).hom ≫
        (cechPresentationEvaluationArrow A q).augmentedCechNerve.left.map f := by
  let B := cechPresentationEvaluationArrow A q
  let D := WidePullbackShape.wideCospan B.right
    (fun _ : Fin (b.unop.len + 1) ↦ B.left) (fun _ ↦ B.hom)
  refine limit.hom_ext (F := D) fun j => ?_
  cases j with
  | some i =>
    rw [Category.assoc, cechPresentationEvaluationIso_hom_π,
      cechPresentationEvaluation_map_π_comp_diagramIso, ← Functor.map_comp]
    change ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (A.cechNerve.map f ≫
            WidePullback.π (fun _ : Fin (b.unop.len + 1) ↦ A.hom) i) =
      (cechPresentationEvaluationIso A a.unop.len q).hom ≫
        ((cechPresentationEvaluationArrow A q).cechNerve.map f ≫
          WidePullback.π
            (fun _ : Fin (b.unop.len + 1) ↦
              (cechPresentationEvaluationArrow A q).hom) i)
    simp only [Arrow.cechNerve_map, WidePullback.lift_π]
    rw [cechPresentationEvaluationIso_hom_π,
      cechPresentationEvaluation_map_π_comp_diagramIso]
  | none =>
    rw [Category.assoc, cechPresentationEvaluationIso_hom_base,
      cechPresentationEvaluation_map_base_comp_diagramIso, ← Functor.map_comp]
    change ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (A.cechNerve.map f ≫
            WidePullback.base (fun _ : Fin (b.unop.len + 1) ↦ A.hom)) =
      (cechPresentationEvaluationIso A a.unop.len q).hom ≫
        ((cechPresentationEvaluationArrow A q).cechNerve.map f ≫
          WidePullback.base
            (fun _ : Fin (b.unop.len + 1) ↦
              (cechPresentationEvaluationArrow A q).hom))
    simp only [Arrow.cechNerve_map, WidePullback.lift_base]
    rw [cechPresentationEvaluationIso_hom_base,
      cechPresentationEvaluation_map_base_comp_diagramIso]

/-- The Čech-level evaluation isomorphisms assemble into a natural isomorphism in the Čech
direction. -/
public noncomputable def cechPresentationSimplicialEvaluationIso
    (A : Arrow SSet) (q : ℕ) :
    A.augmentedCechNerve.left ⋙
        (evaluation SimplexCategoryᵒᵖ (Type 0)).obj
          (Opposite.op (SimplexCategory.mk q)) ≅
      (cechPresentationEvaluationArrow A q).augmentedCechNerve.left :=
  NatIso.ofComponents
    (fun a ↦ cechPresentationEvaluationIso A a.unop.len q)
    (fun f ↦ cechPresentationEvaluationIso_naturality A q f)

/-- Evaluation of an `SSet`-level augmented Čech nerve is canonically the augmented Čech nerve
of the evaluated arrow. -/
public noncomputable def cechPresentationAugmentedEvaluationIso
    (A : Arrow SSet) (q : ℕ) :
    ((SimplicialObject.Augmented.whiskering SSet (Type 0)).obj
        ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
          (Opposite.op (SimplexCategory.mk q)))).obj A.augmentedCechNerve ≅
      (cechPresentationEvaluationArrow A q).augmentedCechNerve :=
  Comma.isoMk
    (cechPresentationSimplicialEvaluationIso A q)
    (Iso.refl _)
    (by
      apply NatTrans.ext
      funext a
      simp only [NatTrans.comp_app, Functor.id_map]
      dsimp only [cechPresentationSimplicialEvaluationIso,
        SimplicialObject.Augmented.whiskering,
        SimplicialObject.Augmented.whiskeringObj]
      change (cechPresentationEvaluationIso A a.unop.len q).hom ≫
          WidePullback.base
            (fun _ : Fin (a.unop.len + 1) ↦
              (cechPresentationEvaluationArrow A q).hom) =
        ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
            (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.base (fun _ : Fin (a.unop.len + 1) ↦ A.hom))
      rw [cechPresentationEvaluationIso_hom_base,
        cechPresentationEvaluation_map_base_comp_diagramIso])

end AlgebraicTopology
