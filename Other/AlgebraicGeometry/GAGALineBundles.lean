/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.LefschetzOneOneReduction
public import Other.AlgebraicGeometry.ProjectiveAnalytificationConnected
public import Other.AlgebraicGeometry.AnalytificationRestriction
public import Other.TauCeti.SheafOfModules.InvertibleFinitePresentation

/-!
# The line-bundle endpoint of projective GAGA

This file records the formal endpoint needed by the line-bundle GAGA argument.  In particular,
it verifies directly that a globally trivial holomorphic line bundle has the required algebraic
model, with the algebraic structure sheaf as model. It also proves the full algebraization
statement in dimension zero by showing that an invertible sheaf on a one-point space is globally
trivial. The positive-dimensional case still requires the projective GAGA input described in
`docs/GAGA_HANDOFF.md`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SheafOfModules

universe u v

/-- Restriction of sheaves of modules to the top open is an equivalence. -/
noncomputable def overTopEquivalence {T : Type u} [TopologicalSpace T]
    (R : Sheaf (Opens.grothendieckTopology T) RingCat.{v}) :
    SheafOfModules R ≌ SheafOfModules (R.over (⊤ : Opens T)) := by
  let e : Over (⊤ : Opens T) ≌ Opens T :=
    Over.equivalenceOfIsTerminal (Limits.isTerminalTop : Limits.IsTerminal (⊤ : Opens T))
  letI : e.functor.IsContinuous
      ((Opens.grothendieckTopology T).over ⊤) (Opens.grothendieckTopology T) := by
    change (Over.forget (⊤ : Opens T)).IsContinuous
      ((Opens.grothendieckTopology T).over ⊤) (Opens.grothendieckTopology T)
    infer_instance
  letI : e.functor.IsCocontinuous
      ((Opens.grothendieckTopology T).over ⊤) (Opens.grothendieckTopology T) := by
    change (Over.forget (⊤ : Opens T)).IsCocontinuous
      ((Opens.grothendieckTopology T).over ⊤) (Opens.grothendieckTopology T)
    infer_instance
  letI : e.inverse.IsContinuous
      (Opens.grothendieckTopology T) ((Opens.grothendieckTopology T).over ⊤) := by
    exact e.toAdjunction.isContinuous_of_isCocontinuous _ _
  refine pushforwardPushforwardEquivalence e (𝟙 _) (𝟙 R) (by
    ext X x
    change R.obj.map (𝟙 X) x = x
    simp) ?_
  ext X x
  change R.obj.map (𝟙 (Opposite.op X.unop.left)) x = x
  rw [R.obj.map_id]
  rfl

end SheafOfModules

namespace TauCeti.SheafOfModules

universe u v u₁

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}] [Limits.HasBinaryProducts C]

/-- The tensor unit is an invertible sheaf: identify it with the free sheaf on one generator. -/
theorem unit_isInvertible : IsInvertible (_root_.SheafOfModules.unit R) := by
  exact IsInvertible.of_iso (h := inferInstance) (freePUnitIsoUnit R)

section Subsingleton

universe w

variable {T : Type w} [TopologicalSpace T] [Nonempty T] [Subsingleton T]
  (S : Sheaf (Opens.grothendieckTopology T) RingCat.{u})
  [∀ U : Opens T,
    HasWeakSheafify ((Opens.grothendieckTopology T).over U) AddCommGrpCat.{u}]
  [∀ U : Opens T,
    ((Opens.grothendieckTopology T).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Every invertible sheaf of modules on a nonempty subsingleton topological space is globally
trivial. A member of any trivializing cover contains the unique point, hence is the top open;
`SheafOfModules.overTopEquivalence` then lifts that local trivialization globally. -/
noncomputable def isInvertibleIsoUnit (M : SheafOfModules.{u} S) [IsInvertible M] :
    _root_.SheafOfModules.unit S ≅ M := by
  let t := LocalTrivializations.ofIsInvertible M
  have ht : IsOpenCover t.X := (Opens.coversTop_iff T t.X).mp t.coversTop
  let x : T := Classical.choice (inferInstance : Nonempty T)
  let i : t.I := Classical.choose (ht.exists_mem x)
  have hxi : x ∈ t.X i := Classical.choose_spec (ht.exists_mem x)
  have hi : t.X i = ⊤ := by
    apply top_unique
    intro y _
    rw [Subsingleton.elim y x]
    exact hxi
  let e := t.iso i
  rw [hi] at e
  exact (_root_.SheafOfModules.overTopEquivalence S).functor.preimageIso
    ((freePUnitIsoUnit (S.over (⊤ : Opens T))).symm ≪≫ e)

end Subsingleton

end TauCeti.SheafOfModules

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

omit [IsIntegral X.left] [IsProjective X.hom] in
/-- Analytification carries the standard algebraic free rank-one module to the standard
holomorphic free rank-one module. This is the free-object half of preservation of local
trivializations. -/
noncomputable def moduleAnalytificationFreePUnitIso (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] :
    (moduleAnalytification X d).obj
        (SheafOfModules.free (R := X.left.ringCatSheaf) PUnit) ≅
      SheafOfModules.free (R := holomorphicRingSheaf X d) PUnit :=
  (moduleAnalytification X d).mapIso
      (TauCeti.SheafOfModules.freePUnitIsoUnit X.left.ringCatSheaf) ≪≫
    moduleAnalytificationUnitIso X d ≪≫
      (TauCeti.SheafOfModules.freePUnitIsoUnit (holomorphicRingSheaf X d)).symm

omit [IsIntegral X.left] [IsProjective X.hom] in
/-- A chosen algebraic global rank-one trivialization analytifies to a holomorphic one. -/
noncomputable def moduleAnalytificationIsoOfFreePUnitIso (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (L : X.left.Modules)
    (e : SheafOfModules.free (R := X.left.ringCatSheaf) PUnit ≅ L) :
    SheafOfModules.free (R := holomorphicRingSheaf X d) PUnit ≅
      (moduleAnalytification X d).obj L :=
  (moduleAnalytificationFreePUnitIso X d).symm ≪≫
    (moduleAnalytification X d).mapIso e

omit [IsProjective X.hom] in
/-- An analytic line bundle is a finitely presented module sheaf. This is the first coherence
property required by the classical GAGA route, and follows from the rank-one local bases. -/
theorem analyticLineBundle_isFinitePresentation
    (M : SheafOfModules.{0} (holomorphicRingSheaf X (dim X.left)))
    (hM : TauCeti.SheafOfModules.IsInvertible M) : M.IsFinitePresentation := by
  let : TauCeti.SheafOfModules.IsInvertible M := hM
  infer_instance

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- An algebraic line bundle is a finitely presented module sheaf. -/
theorem algebraicLineBundle_isFinitePresentation
    (L : X.left.Modules) (hL : TauCeti.SheafOfModules.IsInvertible L) :
    L.IsFinitePresentation := by
  let : TauCeti.SheafOfModules.IsInvertible L := hL
  exact TauCeti.SheafOfModules.IsInvertible.isFinitePresentation

omit [IsProjective X.hom] in
/-- A globally trivial holomorphic line bundle has the algebraic structure sheaf as a GAGA
model.  This is the terminal gluing step of the general line-bundle argument. -/
theorem analyticLineBundle_algebraizes_of_iso_unit
    (M : SheafOfModules.{0} (holomorphicRingSheaf X (dim X.left)))
    (e : SheafOfModules.unit (holomorphicRingSheaf X (dim X.left)) ≅ M) :
    ∃ L : X.left.Modules, TauCeti.SheafOfModules.IsInvertible L ∧
      Nonempty ((moduleAnalytification X (dim X.left)).obj L ≅ M) := by
  let L : X.left.Modules := SheafOfModules.unit X.left.ringCatSheaf
  refine ⟨L, ?_, ?_⟩
  · exact TauCeti.SheafOfModules.unit_isInvertible X.left.ringCatSheaf
  · exact ⟨moduleAnalytificationUnitIso X (dim X.left) ≪≫ e⟩

omit [IsProjective X.hom] in
/-- If the analytification has at most one point, every analytic line bundle algebraizes. Smooth
integrality supplies a complex point, so the analytic space is in fact a one-point space. -/
theorem analyticLineBundlesAlgebraize_of_subsingleton
    [Subsingleton (ComplexPoint X)] : AnalyticLineBundlesAlgebraize X := by
  intro M hM
  let : TauCeti.SheafOfModules.IsInvertible M := hM
  exact analyticLineBundle_algebraizes_of_iso_unit X M
    (TauCeti.SheafOfModules.isInvertibleIsoUnit
      (holomorphicRingSheaf X (dim X.left)) M)

/-- Projective GAGA for line bundles in dimension zero. The analytification has exactly one point,
so every invertible analytic sheaf is globally trivial and the algebraic structure sheaf is a
model. -/
theorem analyticLineBundlesAlgebraize_of_dimension_eq_zero
    (hd : dim X.left = 0) : AnalyticLineBundlesAlgebraize X := by
  let : Subsingleton (ComplexPoint X) :=
    subsingletonComplexPointOfDimensionEqZero X (dim X.left) hd
  exact analyticLineBundlesAlgebraize_of_subsingleton X

end AlgebraicGeometry.ComplexPoint
