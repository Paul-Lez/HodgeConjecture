/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Additive

/-!
# Applying an additive functor commutes with extension of a complex

The comparison is the identity in retained degrees and the canonical isomorphism between
zero objects in newly inserted degrees. In particular it fixes the normalization when
regrading a chain complex by `n ↦ -n` before or after a sheaf functor.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.Additive]
  {I J : Type*} {c : ComplexShape I} {c' : ComplexShape J}
  (K : HomologicalComplex C c) (e : c.Embedding c')

/-- Degreewise comparison: identity on retained degrees, canonical zero-object comparison
on inserted degrees. -/
def mapExtendXIso (a : Option I) :
    F.obj (extend.X K a) ≅ extend.X ((F.mapHomologicalComplex c).obj K) a :=
  match a with
  | some _ => Iso.refl _
  | none => (F.map_isZero (Limits.isZero_zero C)).isoZero

@[reassoc]
lemma mapExtendXIso_hom_d (a b : Option I) :
    (mapExtendXIso F K a).hom ≫ extend.d ((F.mapHomologicalComplex c).obj K) a b =
      F.map (extend.d K a b) ≫ (mapExtendXIso F K b).hom := by
  cases a <;> cases b <;>
    simp [mapExtendXIso, extend.d, Functor.mapHomologicalComplex_obj_d]

/-- The canonical chain-complex comparison between functorial mapping and extension. -/
def mapExtendIso :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  Hom.isoOfComponents (fun j => mapExtendXIso F K (e.r j)) (by
    intro j k hjk
    exact mapExtendXIso_hom_d F K (e.r j) (e.r k))

/-- In an old degree the comparison is the identity through the canonical extension
identifications, including any grading transports. -/
lemma mapExtendIso_hom_f {i : I} {j : J} (h : e.f i = j) :
    (mapExtendIso F K e).hom.f j =
      F.map (K.extendXIso e h).hom ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv := by
  change (mapExtendXIso F K (e.r j)).hom =
    F.map (extend.XIso K (e.r_eq_some h)).hom ≫
      (extend.XIso ((F.mapHomologicalComplex c).obj K) (e.r_eq_some h)).inv
  have H (a : Option I) (ha : a = some i) :
      (mapExtendXIso F K a).hom = F.map (extend.XIso K ha).hom ≫
        (extend.XIso ((F.mapHomologicalComplex c).obj K) ha).inv := by
    subst a
    simp [mapExtendXIso, extend.XIso]
    rfl
  exact H _ _

/-- Naturality of the degreewise comparison in a chain map. -/
lemma mapExtendXIso_hom_mapX {L : HomologicalComplex C c} (f : K ⟶ L) (a : Option I) :
    F.map (extend.mapX f a) ≫ (mapExtendXIso F L a).hom =
      (mapExtendXIso F K a).hom ≫ extend.mapX ((F.mapHomologicalComplex c).map f) a := by
  cases a <;> simp [mapExtendXIso, extend.mapX]

/-- Mapping and extension commute on actual chain maps, with the canonical normalization. -/
@[reassoc]
lemma mapExtendIso_naturality {L : HomologicalComplex C c} (f : K ⟶ L) :
    (F.mapHomologicalComplex c').map (extendMap f e) ≫ (mapExtendIso F L e).hom =
      (mapExtendIso F K e).hom ≫ extendMap ((F.mapHomologicalComplex c).map f) e := by
  ext j
  exact mapExtendXIso_hom_mapX F K f (e.r j)

/-- Compatibility with a natural transformation of additive coefficient functors. -/
@[reassoc]
lemma mapExtendIso_natTrans {G : C ⥤ D} [G.Additive] (a : F ⟶ G) :
    (a.mapHomologicalComplex c').app (K.extend e) ≫ (mapExtendIso G K e).hom =
      (mapExtendIso F K e).hom ≫ extendMap ((a.mapHomologicalComplex c).app K) e := by
  ext j
  change a.app (extend.X K (e.r j)) ≫ (mapExtendXIso G K (e.r j)).hom =
    (mapExtendXIso F K (e.r j)).hom ≫
      extend.mapX ((a.mapHomologicalComplex c).app K) (e.r j)
  cases hr : e.r j with
  | none => exact (F.map_isZero (Limits.isZero_zero C)).eq_of_src _ _
  | some n => simp [mapExtendXIso, extend.X, extend.mapX]

/-- The comparison for the identity coefficient functor is the actual identity. -/
@[simp]
lemma mapExtendIso_id : (mapExtendIso (𝟭 C) K e).hom = 𝟙 (K.extend e) := by
  ext j
  change (mapExtendXIso (𝟭 C) K (e.r j)).hom = 𝟙 (extend.X K (e.r j))
  cases hr : e.r j with
  | none => exact (Limits.isZero_zero C).eq_of_src _ _
  | some n => rfl

end HomologicalComplex
