/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.UnitExtensionIntegerStalk
public import Other.AlgebraicGeometry.HolomorphicUnitTransition

/-!
# Corrected local lifts relating two unit-sheaf extensions

Two extensions of the constant integer sheaf by the sheaf of holomorphic units have the same
class as soon as one can choose local lifts of the integer section `1` in the second extension
whose differences reproduce the transition sections of the first one. This file records that
data as `CorrectedLifts` together with the elementary restriction calculus used later.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open HolomorphicUnitExtension

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance unitExtensionCorrectedLiftsTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

/-- Restriction of a section of an additive sheaf on the analytic space. -/
abbrev sres (F : AnalyticAdditiveSheaf X) {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U)
    (s : F.obj.obj (op U)) : F.obj.obj (op V) :=
  F.obj.map (homOfLE h).op s

@[simp]
theorem sres_self {F : AnalyticAdditiveSheaf X} {U : Opens (TopCat.of (ComplexPoint X))}
    (s : F.obj.obj (op U)) : sres F le_rfl s = s := by
  change F.obj.map (𝟙 (op U)) s = s
  rw [F.obj.map_id]
  rfl

theorem sres_sres {F : AnalyticAdditiveSheaf X} {U V W : Opens (TopCat.of (ComplexPoint X))}
    (hVU : V ≤ U) (hWV : W ≤ V) (s : F.obj.obj (op U)) :
    sres F hWV (sres F hVU s) = sres F (hWV.trans hVU) s := by
  show F.obj.map (homOfLE hWV).op (F.obj.map (homOfLE hVU).op s) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem sres_hom {F G : AnalyticAdditiveSheaf X} (f : F ⟶ G)
    {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U) (s : F.obj.obj (op U)) :
    sres G h (f.hom.app (op U) s) = f.hom.app (op V) (sres F h s) :=
  (ConcreteCategory.congr_hom (f.hom.naturality (homOfLE h).op) s).symm

theorem germ_sres {F : AnalyticAdditiveSheaf X} {U V : Opens (TopCat.of (ComplexPoint X))}
    (h : V ≤ U) (s : F.obj.obj (op U)) (x : ComplexPoint X) (hx : x ∈ V) :
    F.presheaf.germ V x hx (sres F h s) = F.presheaf.germ U x (h hx) s :=
  F.presheaf.germ_res_apply (homOfLE h) x hx s

theorem germ_hom {F G : AnalyticAdditiveSheaf X} (f : F ⟶ G)
    {U : Opens (TopCat.of (ComplexPoint X))} (s : F.obj.obj (op U)) (x : ComplexPoint X)
    (hx : x ∈ U) :
    G.presheaf.germ U x hx (f.hom.app (op U) s) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.hom (F.presheaf.germ U x hx s) :=
  (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx f.hom s).symm

theorem sres_add {F : AnalyticAdditiveSheaf X} {U V : Opens (TopCat.of (ComplexPoint X))}
    (h : V ≤ U) (s t : F.obj.obj (op U)) : sres F h (s + t) = sres F h s + sres F h t :=
  map_add _ _ _

theorem sres_zsmul {F : AnalyticAdditiveSheaf X} {U V : Opens (TopCat.of (ComplexPoint X))}
    (h : V ≤ U) (n : ℤ) (s : F.obj.obj (op U)) : sres F h (n • s) = n • sres F h s :=
  map_zsmul _ _ _

theorem hom_add {F G : AnalyticAdditiveSheaf X} (f : F ⟶ G)
    {U : Opens (TopCat.of (ComplexPoint X))} (s t : F.obj.obj (op U)) :
    f.hom.app (op U) (s + t) = f.hom.app (op U) s + f.hom.app (op U) t :=
  map_add _ _ _

theorem hom_zsmul {F G : AnalyticAdditiveSheaf X} (f : F ⟶ G)
    {U : Opens (TopCat.of (ComplexPoint X))} (n : ℤ) (s : F.obj.obj (op U)) :
    f.hom.app (op U) (n • s) = n • f.hom.app (op U) s :=
  map_zsmul _ _ _

theorem germ_add {F : AnalyticAdditiveSheaf X} {U : Opens (TopCat.of (ComplexPoint X))}
    (s t : F.obj.obj (op U)) (x : ComplexPoint X) (hx : x ∈ U) :
    F.presheaf.germ U x hx (s + t) = F.presheaf.germ U x hx s + F.presheaf.germ U x hx t :=
  map_add _ _ _

theorem germ_zsmul {F : AnalyticAdditiveSheaf X} {U : Opens (TopCat.of (ComplexPoint X))}
    (n : ℤ) (s : F.obj.obj (op U)) (x : ComplexPoint X) (hx : x ∈ U) :
    F.presheaf.germ U x hx (n • s) = n • F.presheaf.germ U x hx s :=
  map_zsmul _ _ _

theorem sres_integerOneRestrict {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U) :
    sres (constantIntegerSheaf X) h (integerOneRestrict X U) = integerOneRestrict X V :=
  integerOneRestrict_map X h

theorem germ_integerOneRestrict (W : Opens (TopCat.of (ComplexPoint X))) (x : ComplexPoint X)
    (hxW : x ∈ W) :
    (constantIntegerSheaf X).presheaf.germ W x hxW (integerOneRestrict X W) =
      (constantIntegerSheaf X).presheaf.germ ⊤ x True.intro (integerOneSection (X := X)) :=
  germ_sres (F := constantIntegerSheaf X) le_top (integerOneSection (X := X)) x hxW

/-- Consecutive maps of an extension annihilate sections. -/
theorem inclusion_projection_apply (E : HolomorphicUnitExtension X d)
    {U : Opens (TopCat.of (ComplexPoint X))} (a : (holomorphicUnitSheaf X d).obj.obj (op U)) :
    E.projection.hom.app (op U) (E.inclusion.hom.app (op U) a) = 0 := by
  have h := congrArg (fun f : holomorphicUnitSheaf X d ⟶ constantIntegerSheaf X =>
    f.hom.app (op U) a) E.zero
  simp at h
  exact h

/-- Local lifts of `1` in `E'` whose differences are the transition sections of `E`. -/
structure CorrectedLifts (E E' : HolomorphicUnitExtension X d) where
  /-- The common lifting neighbourhoods. -/
  opens : ComplexPoint X → Opens (TopCat.of (ComplexPoint X))
  /-- Each neighbourhood contains its point. -/
  mem_opens (z : ComplexPoint X) : z ∈ opens z
  /-- Each neighbourhood is a lifting neighbourhood for `E`. -/
  le_opens (z : ComplexPoint X) : opens z ≤ E.localLifts.opens z
  /-- The corrected lift of `1` in `E'`. -/
  lift (z : ComplexPoint X) : E'.middle.obj.obj (op (opens z))
  /-- Each corrected lift lifts the section `1`. -/
  map_lift (z : ComplexPoint X) :
    E'.projection.hom.app (op (opens z)) (lift z) = integerOneRestrict X (opens z)
  /-- The differences of the corrected lifts are the transition sections of `E`. -/
  sub_lift (z w : ComplexPoint X) (V : Opens (TopCat.of (ComplexPoint X)))
    (hz : V ≤ opens z) (hw : V ≤ opens w) :
    sres E'.middle hz (lift z) - sres E'.middle hw (lift w) =
      E'.inclusion.hom.app (op V)
        (E.localLifts.transition E.shortExact z w V (hz.trans (le_opens z))
          (hw.trans (le_opens w)))

namespace CorrectedLifts

variable {E E' : HolomorphicUnitExtension X d} (c : CorrectedLifts E E')

/-- The chosen lift of `1` in `E`, restricted to the common neighbourhood. -/
def source (z : ComplexPoint X) : E.middle.obj.obj (op (c.opens z)) :=
  E.localLifts.restrictLift z (c.opens z) (c.le_opens z)

theorem map_source (z : ComplexPoint X) :
    E.projection.hom.app (op (c.opens z)) (c.source z) = integerOneRestrict X (c.opens z) :=
  E.localLifts.map_restrictLift z (c.opens z) (c.le_opens z)

theorem sres_source (z : ComplexPoint X) {V : Opens (TopCat.of (ComplexPoint X))}
    (hz : V ≤ c.opens z) :
    sres E.middle hz (c.source z) =
      E.localLifts.restrictLift z V (hz.trans (c.le_opens z)) :=
  E.localLifts.restrictLift_restrict z (c.le_opens z) hz

theorem sub_source (z w : ComplexPoint X) (V : Opens (TopCat.of (ComplexPoint X)))
    (hz : V ≤ c.opens z) (hw : V ≤ c.opens w) :
    sres E.middle hz (c.source z) - sres E.middle hw (c.source w) =
      E.inclusion.hom.app (op V)
        (E.localLifts.transition E.shortExact z w V (hz.trans (c.le_opens z))
          (hw.trans (c.le_opens w))) := by
  rw [c.sres_source z hz, c.sres_source w hw]
  exact (E.localLifts.transition_spec E.shortExact z w V _ _).symm


/-- The local model of a section of the middle sheaf of `E` in the frame at `z`. -/
def sourceModel (z : ComplexPoint X) {U : Opens (TopCat.of (ComplexPoint X))}
    (hU : U ≤ c.opens z) (n : ℤ) (a : (holomorphicUnitSheaf X d).obj.obj (op U)) :
    E.middle.obj.obj (op U) :=
  E.inclusion.hom.app (op U) a + n • sres E.middle hU (c.source z)

/-- The corresponding local model in the middle sheaf of `E'`. -/
def targetModel (z : ComplexPoint X) {U : Opens (TopCat.of (ComplexPoint X))}
    (hU : U ≤ c.opens z) (n : ℤ) (a : (holomorphicUnitSheaf X d).obj.obj (op U)) :
    E'.middle.obj.obj (op U) :=
  E'.inclusion.hom.app (op U) a + n • sres E'.middle hU (c.lift z)

theorem map_sourceModel (z : ComplexPoint X) {U : Opens (TopCat.of (ComplexPoint X))}
    (hU : U ≤ c.opens z) (n : ℤ) (a : (holomorphicUnitSheaf X d).obj.obj (op U)) :
    E.projection.hom.app (op U) (c.sourceModel z hU n a) = n • integerOneRestrict X U := by
  unfold sourceModel
  rw [hom_add, inclusion_projection_apply, zero_add, hom_zsmul, ← sres_hom, c.map_source,
    sres_integerOneRestrict]

theorem map_targetModel (z : ComplexPoint X) {U : Opens (TopCat.of (ComplexPoint X))}
    (hU : U ≤ c.opens z) (n : ℤ) (a : (holomorphicUnitSheaf X d).obj.obj (op U)) :
    E'.projection.hom.app (op U) (c.targetModel z hU n a) = n • integerOneRestrict X U := by
  unfold targetModel
  rw [hom_add, inclusion_projection_apply, zero_add, hom_zsmul, ← sres_hom, c.map_lift,
    sres_integerOneRestrict]

theorem sres_sourceModel (z : ComplexPoint X) {U V : Opens (TopCat.of (ComplexPoint X))}
    (hU : U ≤ c.opens z) (hVU : V ≤ U) (n : ℤ)
    (a : (holomorphicUnitSheaf X d).obj.obj (op U)) :
    sres E.middle hVU (c.sourceModel z hU n a) =
      c.sourceModel z (hVU.trans hU) n (sres (holomorphicUnitSheaf X d) hVU a) := by
  unfold sourceModel
  rw [sres_add, sres_hom, sres_zsmul, sres_sres]

theorem sres_targetModel (z : ComplexPoint X) {U V : Opens (TopCat.of (ComplexPoint X))}
    (hU : U ≤ c.opens z) (hVU : V ≤ U) (n : ℤ)
    (a : (holomorphicUnitSheaf X d).obj.obj (op U)) :
    sres E'.middle hVU (c.targetModel z hU n a) =
      c.targetModel z (hVU.trans hU) n (sres (holomorphicUnitSheaf X d) hVU a) := by
  unfold targetModel
  rw [sres_add, sres_hom, sres_zsmul, sres_sres]

theorem sourceModel_add (z : ComplexPoint X) {U : Opens (TopCat.of (ComplexPoint X))}
    (hU : U ≤ c.opens z) (n n' : ℤ)
    (a a' : (holomorphicUnitSheaf X d).obj.obj (op U)) :
    c.sourceModel z hU n a + c.sourceModel z hU n' a' = c.sourceModel z hU (n + n') (a + a') := by
  unfold sourceModel
  rw [hom_add, add_zsmul]
  abel

theorem targetModel_add (z : ComplexPoint X) {U : Opens (TopCat.of (ComplexPoint X))}
    (hU : U ≤ c.opens z) (n n' : ℤ)
    (a a' : (holomorphicUnitSheaf X d).obj.obj (op U)) :
    c.targetModel z hU n a + c.targetModel z hU n' a' = c.targetModel z hU (n + n') (a + a') := by
  unfold targetModel
  rw [hom_add, add_zsmul]
  abel

theorem sourceModel_base (z w : ComplexPoint X) {U : Opens (TopCat.of (ComplexPoint X))}
    (hUz : U ≤ c.opens z) (hUw : U ≤ c.opens w) (n : ℤ)
    (a : (holomorphicUnitSheaf X d).obj.obj (op U)) :
    c.sourceModel z hUz n a = c.sourceModel w hUw n
      (a + n • E.localLifts.transition E.shortExact z w U (hUz.trans (c.le_opens z))
        (hUw.trans (c.le_opens w))) := by
  have h := c.sub_source z w U hUz hUw
  unfold sourceModel
  rw [hom_add, hom_zsmul, ← h, smul_sub]
  abel

theorem targetModel_base (z w : ComplexPoint X) {U : Opens (TopCat.of (ComplexPoint X))}
    (hUz : U ≤ c.opens z) (hUw : U ≤ c.opens w) (n : ℤ)
    (a : (holomorphicUnitSheaf X d).obj.obj (op U)) :
    c.targetModel z hUz n a = c.targetModel w hUw n
      (a + n • E.localLifts.transition E.shortExact z w U (hUz.trans (c.le_opens z))
        (hUw.trans (c.le_opens w))) := by
  have h := c.sub_lift z w U hUz hUw
  unfold targetModel
  rw [hom_add, hom_zsmul, ← h, smul_sub]
  abel

/-- Every section of the middle sheaf of `E` is, near each point, a local model. -/
theorem exists_sourceModel (z : ComplexPoint X) {V : Opens (TopCat.of (ComplexPoint X))}
    (s : E.middle.obj.obj (op V)) (x : ComplexPoint X) (hxV : x ∈ V) (hxz : x ∈ c.opens z) :
    ∃ (U : Opens (TopCat.of (ComplexPoint X))) (_ : x ∈ U) (hUV : U ≤ V) (hUz : U ≤ c.opens z)
      (n : ℤ) (a : (holomorphicUnitSheaf X d).obj.obj (op U)),
      sres E.middle hUV s = c.sourceModel z hUz n a := by
  obtain ⟨U₀, hxU₀, hU₀V, n, hn⟩ :=
    exists_zsmul_integerOneSection X V (E.projection.hom.app (op V) s) x hxV
  refine ⟨U₀ ⊓ c.opens z, ⟨hxU₀, hxz⟩, inf_le_left.trans hU₀V, inf_le_right, n, ?_⟩
  have hn' : sres (constantIntegerSheaf X) hU₀V (E.projection.hom.app (op V) s) =
      n • integerOneRestrict X U₀ := hn
  have hres : sres (constantIntegerSheaf X) (inf_le_left.trans hU₀V : U₀ ⊓ c.opens z ≤ V)
      (E.projection.hom.app (op V) s) = n • integerOneRestrict X (U₀ ⊓ c.opens z) := by
    rw [← sres_sres (F := constantIntegerSheaf X) hU₀V
      (inf_le_left : U₀ ⊓ c.opens z ≤ U₀), hn', sres_zsmul, sres_integerOneRestrict]
  have hproj : E.projection.hom.app (op (U₀ ⊓ c.opens z))
      (sres E.middle (inf_le_left.trans hU₀V) s -
        n • sres E.middle (inf_le_right : U₀ ⊓ c.opens z ≤ c.opens z) (c.source z)) = 0 := by
    rw [map_sub, ← sres_hom, hom_zsmul, ← sres_hom, c.map_source, sres_integerOneRestrict, hres,
      sub_self]
  obtain ⟨a, ha⟩ := TopCat.Sheaf.sections_exact E.shortComplex E.shortExact (U₀ ⊓ c.opens z) _ hproj
  refine ⟨a, ?_⟩
  have ha' : E.inclusion.hom.app (op (U₀ ⊓ c.opens z)) a =
      sres E.middle (inf_le_left.trans hU₀V) s -
        n • sres E.middle (inf_le_right : U₀ ⊓ c.opens z ≤ c.opens z) (c.source z) := ha
  unfold sourceModel
  rw [ha']
  abel

/-- Local models with the same germ in `E` have the same germ in `E'`. -/
theorem germ_targetModel_eq (x : ComplexPoint X) {U U' : Opens (TopCat.of (ComplexPoint X))}
    (hxU : x ∈ U) (hxU' : x ∈ U') (hU : U ≤ c.opens x) (hU' : U' ≤ c.opens x) (n n' : ℤ)
    (a : (holomorphicUnitSheaf X d).obj.obj (op U))
    (a' : (holomorphicUnitSheaf X d).obj.obj (op U'))
    (h : E.middle.presheaf.germ U x hxU (c.sourceModel x hU n a) =
      E.middle.presheaf.germ U' x hxU' (c.sourceModel x hU' n' a')) :
    E'.middle.presheaf.germ U x hxU (c.targetModel x hU n a) =
      E'.middle.presheaf.germ U' x hxU' (c.targetModel x hU' n' a') := by
  obtain ⟨W, hxW, iU, iU', hW⟩ := E.middle.presheaf.germ_eq x hxU hxU' _ _ h
  have hW' : c.sourceModel x (iU.le.trans hU) n (sres (holomorphicUnitSheaf X d) iU.le a) =
      c.sourceModel x (iU'.le.trans hU') n' (sres (holomorphicUnitSheaf X d) iU'.le a') := by
    rw [← c.sres_sourceModel, ← c.sres_sourceModel]
    exact hW
  have hn : n = n' := by
    have hp := congrArg (E.projection.hom.app (op W)) hW'
    rw [c.map_sourceModel, c.map_sourceModel] at hp
    have hg := congrArg ((constantIntegerSheaf X).presheaf.germ W x hxW) hp
    rw [germ_zsmul, germ_zsmul, germ_integerOneRestrict] at hg
    refine integerOneSection_zsmul_germ_injective X x ?_
    exact (germ_zsmul (F := constantIntegerSheaf X) n (integerOneSection (X := X)) x
      True.intro).trans (hg.trans (germ_zsmul (F := constantIntegerSheaf X) n'
        (integerOneSection (X := X)) x True.intro).symm)
  subst hn
  have hincl : E.inclusion.hom.app (op W) (sres (holomorphicUnitSheaf X d) iU.le a) =
      E.inclusion.hom.app (op W) (sres (holomorphicUnitSheaf X d) iU'.le a') :=
    add_right_cancel hW'
  have ha := TopCat.Sheaf.sections_injective E.shortComplex E.shortExact W hincl
  rw [← germ_sres iU.le (c.targetModel x hU n a) x hxW,
    ← germ_sres iU'.le (c.targetModel x hU' n a') x hxW,
    c.sres_targetModel, c.sres_targetModel, ha]

end CorrectedLifts

end AlgebraicGeometry.ComplexPoint
