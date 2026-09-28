/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveChartMultiplierGrowth

/-!
# Locality on the standard charts of `ℙᴺ(ℂ)`

The `i`-th homogeneous chart is parametrised bijectively by `ℂᴺ` through `chartPointIn`, so a
section of the holomorphic structure sheaf on a chart is determined by its chart expression.  The
charts cover `ℙᴺ(ℂ)`, so a morphism out of `𝒪(−a)^an` whose chart multipliers all vanish is zero.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexProjectiveSpace

open ComplexPoint Other.ProjectiveChart

variable {N : ℕ}

/-- The chart parametrisation is surjective onto the chart. -/
theorem surjective_chartPointIn (i : Fin (N + 1)) : Function.Surjective (chartPointIn N i) := by
  intro y
  have hy : (y : ComplexPoint (projectiveSpaceOver N)) ∈ complexPointChartSet i := by
    have := y.2
    rwa [← coe_chartOpen N i]
  obtain ⟨p, hp, hpy⟩ := hy
  obtain ⟨z, rfl⟩ := hp
  exact ⟨z, Subtype.ext hpy⟩

/-- A section of the holomorphic structure sheaf on a chart is determined by its chart
expression. -/
theorem holSection_ext (i : Fin (N + 1))
    {u v : (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj (op (chartOpen N i))}
    (h : ∀ z : Fin N → ℂ, chartFun N i u z = chartFun N i v z) : u = v := by
  apply Subtype.ext
  funext y
  obtain ⟨z, rfl⟩ := surjective_chartPointIn i y
  exact h z

/-- Every point of `ℙᴺ(ℂ)` lies in one of the standard charts. -/
theorem exists_mem_chartOpen (x : ComplexPoint (projectiveSpaceOver N)) :
    ∃ i : Fin (N + 1), x ∈ chartOpen N i := by
  obtain ⟨i, hxi⟩ : ∃ i : Fin (N + 1), x ∈ complexPointChartSet i := by
    have hx : x ∈ ⋃ i : Fin (N + 1), complexPointChartSet i := by
      rw [iUnion_complexPointChartSet]
      trivial
    simpa using hx
  exact ⟨i, by rwa [← coe_chartOpen N i] at hxi⟩

set_option maxHeartbeats 1000000 in
/-- **Locality.**  A morphism out of `𝒪(−a)^an` whose value on every canonical chart frame
vanishes is zero. -/
theorem hom_eq_zero_of_anChartFrame {a : ℕ}
    {M' : SheafOfModules.{0} (holomorphicRingSheaf (projectiveSpaceOver N) N)}
    (ψ : analyticTwist N a ⟶ M')
    (hz : ∀ i : Fin (N + 1), ψ.val.app (op (chartOpen N i)) (anChartFrame N a i) = 0) :
    ψ = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  refine TopCat.Presheaf.IsSheaf.section_ext (F := M'.val.presheaf) M'.isSheaf (U := V)
    (t := 0) ?_
  intro x hx
  obtain ⟨i, hxi⟩ := exists_mem_chartOpen x
  refine ⟨V.unop ⊓ chartOpen N i, inf_le_left, ⟨hx, hxi⟩, ?_⟩
  obtain ⟨r, hr⟩ := (holomorphicGenerates_anChartFrame N a i).exists_smul_eq
    (inf_le_right : V.unop ⊓ chartOpen N i ≤ chartOpen N i)
    (ComplexPoint.holRes (analyticTwist N a) (inf_le_left : V.unop ⊓ chartOpen N i ≤ V.unop) s)
  have hnat : M'.val.presheaf.map (homOfLE (inf_le_left :
        V.unop ⊓ chartOpen N i ≤ V.unop)).op (ψ.val.app V s) =
      ψ.val.app (op (V.unop ⊓ chartOpen N i))
        (ComplexPoint.holRes (analyticTwist N a) inf_le_left s) :=
    (PresheafOfModules.naturality_apply ψ.val (homOfLE (inf_le_left :
      V.unop ⊓ chartOpen N i ≤ V.unop)).op s).symm
  rw [hnat, ← hr, (ψ.val.app (op (V.unop ⊓ chartOpen N i))).hom.map_smul,
    ComplexPoint.holRes_app ψ (inf_le_right : V.unop ⊓ chartOpen N i ≤ chartOpen N i)
      (anChartFrame N a i) |>.symm, hz i]
  have hz0 : ComplexPoint.holRes M' (inf_le_right : V.unop ⊓ chartOpen N i ≤ chartOpen N i)
      (0 : M'.val.obj (op (chartOpen N i))) = 0 :=
    (M'.val.map (homOfLE (inf_le_right :
      V.unop ⊓ chartOpen N i ≤ chartOpen N i)).op).hom.map_zero
  rw [hz0, smul_zero]
  exact ((M'.val.presheaf.map (homOfLE (inf_le_left :
    V.unop ⊓ chartOpen N i ≤ V.unop)).op).hom.map_zero).symm

end AlgebraicGeometry.ComplexProjectiveSpace
