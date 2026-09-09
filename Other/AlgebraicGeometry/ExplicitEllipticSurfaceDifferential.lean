/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurfacePullback
public import Other.Algebra.DeRham.KaehlerWedge

/-!
# A holomorphic two-form on the actual elliptic self-product

On each of the four product charts, the two pulled-back regular elliptic differentials
are wedged and evaluated as holomorphic forms. Their restriction identities provide the
gluing condition for the actual holomorphic de Rham sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] regularSectionAlgebra

local instance surfaceSectionAlgebra (V : surface.Opens) : Algebra ℂ Γ(surface, V) :=
  regularSectionAlgebra (Over.mk surfaceToBase) V

instance surfaceOver_smooth : SmoothOfRelativeDimension 2 (Over.mk surfaceToBase).hom :=
  inferInstanceAs (SmoothOfRelativeDimension 2 surfaceToBase)

/-- The two affine coordinates used for the invariant differential, with the finite chart first. -/
def differentialChartIndex : Fin 2 → Fin 3 := ![2, 1]

def indexedCurveDifferential :
    (i : Fin 2) → KaehlerDifferential ℂ Γ(curve, chart (differentialChartIndex i)) :=
  Fin.cases curveZDifferential (Fin.cases curveYDifferential (fun i => i.elim0))

def surfacePulledCurveDifferential (f : surface ⟶ curve)
    (hbase : f ≫ curveToBase = surfaceToBase) (i : Fin 2)
    (V : surface.Opens) (h : V ≤ f ⁻¹ᵁ chart (differentialChartIndex i)) :
    KaehlerDifferential ℂ Γ(surface, V) :=
  surfaceDifferentialPullback f hbase _ V h (indexedCurveDifferential i)

/-- The pulled-back invariant form is independent of the chosen affine formula. -/
theorem surfacePulledCurveDifferential_eq (f : surface ⟶ curve)
    (hbase : f ≫ curveToBase = surfaceToBase) (i j : Fin 2)
    (V : surface.Opens) (hi : V ≤ f ⁻¹ᵁ chart (differentialChartIndex i))
    (hj : V ≤ f ⁻¹ᵁ chart (differentialChartIndex j)) :
    surfacePulledCurveDifferential f hbase i V hi =
      surfacePulledCurveDifferential f hbase j V hj := by
  fin_cases i <;> fin_cases j
  · rfl
  · exact surfaceDifferentialPullback_overlap f hbase V hi hj
  · exact (surfaceDifferentialPullback_overlap f hbase V hj hi).symm
  · rfl

/-- The four actual product opens of the surface. -/
def surfaceDifferentialOpen (ij : Fin 2 × Fin 2) : surface.Opens :=
  pullback.fst curveToBase curveToBase ⁻¹ᵁ chart (differentialChartIndex ij.1) ⊓
    pullback.snd curveToBase curveToBase ⁻¹ᵁ chart (differentialChartIndex ij.2)

/-- The local algebraic two-form, already defined on every smaller product-chart open. -/
def surfaceLocalTwoFormOn (ij : Fin 2 × Fin 2) (V : surface.Opens)
    (h : V ≤ surfaceDifferentialOpen ij) : Algebra.DeRham.Form ℂ Γ(surface, V) 2 :=
  Algebra.DeRham.kaehlerWedge ℂ Γ(surface, V)
    (surfacePulledCurveDifferential (pullback.fst curveToBase curveToBase) rfl ij.1 V
      (h.trans inf_le_left))
    (surfacePulledCurveDifferential (pullback.snd curveToBase curveToBase)
      pullback.condition.symm ij.2 V (h.trans inf_le_right))

/-- The algebraic local two-forms agree on every actual common product-chart open. -/
theorem surfaceLocalTwoFormOn_eq (ij kl : Fin 2 × Fin 2) (V : surface.Opens)
    (hij : V ≤ surfaceDifferentialOpen ij) (hkl : V ≤ surfaceDifferentialOpen kl) :
    surfaceLocalTwoFormOn ij V hij = surfaceLocalTwoFormOn kl V hkl := by
  exact congrArg₂ (fun a b => Algebra.DeRham.kaehlerWedge ℂ Γ(surface, V) a b)
    (surfacePulledCurveDifferential_eq (pullback.fst curveToBase curveToBase) rfl
      ij.1 kl.1 V (hij.trans inf_le_left) (hkl.trans inf_le_left))
    (surfacePulledCurveDifferential_eq (pullback.snd curveToBase curveToBase)
      pullback.condition.symm ij.2 kl.2 V (hij.trans inf_le_right) (hkl.trans inf_le_right))

/-- The local algebraic wedges commute with restriction to smaller opens of the surface. -/
theorem surfaceLocalTwoFormOn_restrict (ij : Fin 2 × Fin 2) {V W : surface.Opens}
    (hV : V ≤ surfaceDifferentialOpen ij) (hWV : W ≤ V) :
    Algebra.DeRham.map ℂ (regularSectionRestriction (Over.mk surfaceToBase) hWV) 2
        (surfaceLocalTwoFormOn ij V hV) =
      surfaceLocalTwoFormOn ij W (hWV.trans hV) := by
  let : Algebra Γ(surface, V) Γ(surface, W) :=
    (regularSectionRestriction (Over.mk surfaceToBase) hWV).toRingHom.toAlgebra
  let : IsScalarTower ℂ Γ(surface, V) Γ(surface, W) :=
    IsScalarTower.of_algebraMap_eq'
      (regularSectionRestriction (Over.mk surfaceToBase) hWV).comp_algebraMap.symm
  have hk := Algebra.DeRham.kaehlerWedge_map ℂ Γ(surface, V) Γ(surface, W)
    (surfacePulledCurveDifferential (pullback.fst curveToBase curveToBase) rfl ij.1 V
      (hV.trans inf_le_left))
    (surfacePulledCurveDifferential (pullback.snd curveToBase curveToBase)
      pullback.condition.symm ij.2 V (hV.trans inf_le_right))
  have hf := surfaceDifferentialPullback_restrict
    (pullback.fst curveToBase curveToBase) rfl _ (hV.trans inf_le_left) hWV
    (indexedCurveDifferential ij.1)
  have hg := surfaceDifferentialPullback_restrict
    (pullback.snd curveToBase curveToBase) pullback.condition.symm _
    (hV.trans inf_le_right) hWV (indexedCurveDifferential ij.2)
  exact hk.symm.trans (congrArg₂
    (fun a b => Algebra.DeRham.kaehlerWedge ℂ Γ(surface, W) a b) hf hg)

abbrev surfaceAnalyticOpen (V : surface.Opens) := regularAnalyticOpen (Over.mk surfaceToBase) V

/-- Evaluation of the actual local algebraic wedge as a holomorphic two-form. -/
def surfaceLocalHolomorphicTwoFormOn (ij : Fin 2 × Fin 2) (V : surface.Opens)
    (h : V ≤ surfaceDifferentialOpen ij) :
    HolomorphicForm (Over.mk surfaceToBase) 2 (.op (surfaceAnalyticOpen V)) 2 :=
  regularFormToHolomorphicForm (Over.mk surfaceToBase) 2 V 2 (surfaceLocalTwoFormOn ij V h)

theorem surfaceLocalHolomorphicTwoFormOn_restrict (ij : Fin 2 × Fin 2) {V W : surface.Opens}
    (hV : V ≤ surfaceDifferentialOpen ij) (hWV : W ≤ V) :
    holomorphicFormRestriction (Over.mk surfaceToBase) 2
        (regularAnalyticRestriction (Over.mk surfaceToBase) hWV).op 2
        (surfaceLocalHolomorphicTwoFormOn ij V hV) =
      surfaceLocalHolomorphicTwoFormOn ij W (hWV.trans hV) := by
  have hr := regularFormToHolomorphicForm_restrict (Over.mk surfaceToBase) 2 hWV 2
    (surfaceLocalTwoFormOn ij V hV)
  exact hr.trans (congrArg (regularFormToHolomorphicForm (Over.mk surfaceToBase) 2 W 2)
    (surfaceLocalTwoFormOn_restrict ij hV hWV))

theorem surfaceLocalHolomorphicTwoFormOn_eq (ij kl : Fin 2 × Fin 2) (V : surface.Opens)
    (hij : V ≤ surfaceDifferentialOpen ij) (hkl : V ≤ surfaceDifferentialOpen kl) :
    surfaceLocalHolomorphicTwoFormOn ij V hij = surfaceLocalHolomorphicTwoFormOn kl V hkl :=
  congrArg (regularFormToHolomorphicForm (Over.mk surfaceToBase) 2 V 2)
    (surfaceLocalTwoFormOn_eq ij kl V hij hkl)

abbrev surfaceHolomorphicTwoFormSheaf := holomorphicDeRhamSheaf (Over.mk surfaceToBase) 2 2

/-- The local wedge as a section of the actual holomorphic two-form sheaf. -/
def surfaceLocalSheafTwoFormOn (ij : Fin 2 × Fin 2) (V : surface.Opens)
    (h : V ≤ surfaceDifferentialOpen ij) :
    surfaceHolomorphicTwoFormSheaf.obj.obj (.op (surfaceAnalyticOpen V)) :=
  (toSheafify (Opens.grothendieckTopology _)
      (holomorphicDeRhamPresheaf (Over.mk surfaceToBase) 2 2)).app
    (.op (surfaceAnalyticOpen V)) (surfaceLocalHolomorphicTwoFormOn ij V h)

theorem surfaceLocalSheafTwoFormOn_restrict (ij : Fin 2 × Fin 2) {V W : surface.Opens}
    (hV : V ≤ surfaceDifferentialOpen ij) (hWV : W ≤ V) :
    surfaceHolomorphicTwoFormSheaf.obj.map
        (regularAnalyticRestriction (Over.mk surfaceToBase) hWV).op
        (surfaceLocalSheafTwoFormOn ij V hV) =
      surfaceLocalSheafTwoFormOn ij W (hWV.trans hV) := by
  let η := toSheafify (Opens.grothendieckTopology _)
    (holomorphicDeRhamPresheaf (Over.mk surfaceToBase) 2 2)
  have hn := congrArg (fun g => g (surfaceLocalHolomorphicTwoFormOn ij V hV))
    (η.naturality (regularAnalyticRestriction (Over.mk surfaceToBase) hWV).op)
  exact hn.symm.trans (congrArg (η.app (.op (surfaceAnalyticOpen W)))
    (surfaceLocalHolomorphicTwoFormOn_restrict ij hV hWV))

theorem surfaceLocalSheafTwoFormOn_eq (ij kl : Fin 2 × Fin 2) (V : surface.Opens)
    (hij : V ≤ surfaceDifferentialOpen ij) (hkl : V ≤ surfaceDifferentialOpen kl) :
    surfaceLocalSheafTwoFormOn ij V hij = surfaceLocalSheafTwoFormOn kl V hkl :=
  congrArg ((toSheafify (Opens.grothendieckTopology _)
    (holomorphicDeRhamPresheaf (Over.mk surfaceToBase) 2 2)).app (.op (surfaceAnalyticOpen V)))
    (surfaceLocalHolomorphicTwoFormOn_eq ij kl V hij hkl)

/-- The analytic product-chart opens cover every complex point of the actual surface. -/
theorem surfaceDifferentialOpen_analytic_cover :
    (⨆ ij : Fin 2 × Fin 2, surfaceAnalyticOpen (surfaceDifferentialOpen ij)) = ⊤ := by
  apply top_unique
  intro z _
  have hc (x : curve) : x ∈ chart 2 ∨ x ∈ chart 1 := by
    have hx : x ∈ chart 1 ⊔ chart 2 := by rw [chart_one_sup_chart_two]; trivial
    exact hx.elim Or.inr Or.inl
  rcases hc (pullback.fst curveToBase curveToBase z.underlying) with h₁ | h₁ <;>
    rcases hc (pullback.snd curveToBase curveToBase z.underlying) with h₂ | h₂
  · exact (le_iSup (fun ij => surfaceAnalyticOpen (surfaceDifferentialOpen ij)) (0, 0)) ⟨h₁, h₂⟩
  · exact (le_iSup (fun ij => surfaceAnalyticOpen (surfaceDifferentialOpen ij)) (0, 1)) ⟨h₁, h₂⟩
  · exact (le_iSup (fun ij => surfaceAnalyticOpen (surfaceDifferentialOpen ij)) (1, 0)) ⟨h₁, h₂⟩
  · exact (le_iSup (fun ij => surfaceAnalyticOpen (surfaceDifferentialOpen ij)) (1, 1)) ⟨h₁, h₂⟩

/-- The product of the two elliptic invariant forms defines an actual global holomorphic section. -/
theorem exists_surfaceGlobalHolomorphicTwoForm :
    ∃ s : surfaceHolomorphicTwoFormSheaf.obj.obj (.op ⊤), ∀ ij : Fin 2 × Fin 2,
      surfaceHolomorphicTwoFormSheaf.obj.map (homOfLE
          (show surfaceAnalyticOpen (surfaceDifferentialOpen ij) ≤ ⊤ from le_top)).op s =
        surfaceLocalSheafTwoFormOn ij (surfaceDifferentialOpen ij) le_rfl := by
  let U (ij : Fin 2 × Fin 2) := surfaceAnalyticOpen (surfaceDifferentialOpen ij)
  let sf (ij : Fin 2 × Fin 2) := surfaceLocalSheafTwoFormOn ij (surfaceDifferentialOpen ij) le_rfl
  have hc : TopCat.Presheaf.IsCompatible surfaceHolomorphicTwoFormSheaf.obj U sf := by
    intro ij kl
    have h₁ := surfaceLocalSheafTwoFormOn_restrict ij le_rfl
      (show surfaceDifferentialOpen ij ⊓ surfaceDifferentialOpen kl ≤
        surfaceDifferentialOpen ij from inf_le_left)
    have h₂ := surfaceLocalSheafTwoFormOn_restrict kl le_rfl
      (show surfaceDifferentialOpen ij ⊓ surfaceDifferentialOpen kl ≤
        surfaceDifferentialOpen kl from inf_le_right)
    exact h₁.trans ((surfaceLocalSheafTwoFormOn_eq ij kl
      (surfaceDifferentialOpen ij ⊓ surfaceDifferentialOpen kl)
      inf_le_left inf_le_right).trans h₂.symm)
  obtain ⟨s, hs, _⟩ := surfaceHolomorphicTwoFormSheaf.existsUnique_gluing' U ⊤
    (fun _ => homOfLE le_top) surfaceDifferentialOpen_analytic_cover.ge sf hc
  exact ⟨s, hs⟩

/-- The holomorphic two-form obtained by gluing the four explicit product-chart formulas. -/
def surfaceGlobalHolomorphicTwoForm : surfaceHolomorphicTwoFormSheaf.obj.obj (.op ⊤) :=
  exists_surfaceGlobalHolomorphicTwoForm.choose

theorem surfaceGlobalHolomorphicTwoForm_restrict (ij : Fin 2 × Fin 2) :
    surfaceHolomorphicTwoFormSheaf.obj.map (homOfLE
        (show surfaceAnalyticOpen (surfaceDifferentialOpen ij) ≤ ⊤ from le_top)).op
        surfaceGlobalHolomorphicTwoForm =
      surfaceLocalSheafTwoFormOn ij (surfaceDifferentialOpen ij) le_rfl :=
  exists_surfaceGlobalHolomorphicTwoForm.choose_spec ij

end AlgebraicGeometry.ExplicitEllipticCandidate
