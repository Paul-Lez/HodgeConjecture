/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.TheoremBBox
public import Other.Oka.AnalyticSpace.CoherentSectionModel

/-!
# Open boxes with rational corners

`Complex.ratBox a b` is the open box `∏ᵢ (aᵢ.1, bᵢ.1) × (aᵢ.2, bᵢ.2) ⊆ ℂ^ι` with rational corners.
They form a countable family, and every point of an open `O ⊆ ℂ^ι` lies in a rational box whose
closure is compact and contained in a bigger rational box inside `O`
(`Complex.exists_ratBox_subset`). The structure sheaf is acyclic on (chart images of) open boxes
(`ComplexAnalytic.structureAcyclic_chartOpen_ratBox`), by Theorem B for boxes.
-/

@[expose] public section

universe u

open TopologicalSpace Set Topology Metric

namespace Complex

variable {ι : Type u} [Fintype ι]

/-- The corners of a rational box, as complex numbers. -/
def ratCorner (a : ι → ℚ × ℚ) : ι → ℂ := fun i ↦ ⟨(a i).1, (a i).2⟩

/-- The open box with rational corners `a`, `b`. -/
def ratBox (a b : ι → ℚ × ℚ) : Opens (ι → ℂ) :=
  ⟨openBox (ratCorner a) (ratCorner b),
    isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo.reProdIm isOpen_Ioo⟩

lemma mem_ratBox {a b : ι → ℚ × ℚ} {w : ι → ℂ} :
    w ∈ ratBox a b ↔ ∀ i, ((a i).1 : ℝ) < (w i).re ∧ (w i).re < (b i).1 ∧
      ((a i).2 : ℝ) < (w i).im ∧ (w i).im < (b i).2 := by
  change w ∈ openBox _ _ ↔ _
  simp only [openBox, mem_pi, mem_univ, forall_const, mem_reProdIm, mem_Ioo, ratCorner]
  exact forall_congr' fun i ↦ by tauto

lemma coe_ratBox (a b : ι → ℚ × ℚ) :
    (ratBox a b : Set (ι → ℂ)) = openBox (ratCorner a) (ratCorner b) :=
  rfl

private lemma exists_rat_four (x ε : ℝ) (hε : 0 < ε) : ∃ q₁ q₂ q₃ q₄ : ℚ,
    x - ε / 2 < q₁ ∧ (q₁ : ℝ) < x - ε / 4 ∧ x - ε / 4 < q₂ ∧ (q₂ : ℝ) < x ∧
      x < q₃ ∧ (q₃ : ℝ) < x + ε / 4 ∧ x + ε / 4 < q₄ ∧ (q₄ : ℝ) < x + ε / 2 := by
  obtain ⟨q₁, h₁, h₁'⟩ := exists_rat_btwn (show x - ε / 2 < x - ε / 4 by linarith)
  obtain ⟨q₂, h₂, h₂'⟩ := exists_rat_btwn (show x - ε / 4 < x by linarith)
  obtain ⟨q₃, h₃, h₃'⟩ := exists_rat_btwn (show x < x + ε / 4 by linarith)
  obtain ⟨q₄, h₄, h₄'⟩ := exists_rat_btwn (show x + ε / 4 < x + ε / 2 by linarith)
  exact ⟨q₁, q₂, q₃, q₄, h₁, h₁', h₂, h₂', h₃, h₃', h₄, h₄'⟩

/-- **Rational boxes form a basis with compact shrinkings**: every point `z` of an open `O`
lies in a rational box `B'` of compact closure contained in a rational box `B ⊆ O`. -/
theorem exists_ratBox_subset {O : Set (ι → ℂ)} (hO : IsOpen O) {z : ι → ℂ} (hz : z ∈ O) :
    ∃ a b a' b' : ι → ℚ × ℚ, z ∈ ratBox a' b' ∧
      IsCompact (closure (ratBox a' b' : Set (ι → ℂ))) ∧
      closure (ratBox a' b' : Set (ι → ℂ)) ⊆ ratBox a b ∧ (ratBox a b : Set (ι → ℂ)) ⊆ O := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO z hz
  choose r₁ r₂ r₃ r₄ hr using fun i ↦ exists_rat_four (z i).re ε hε
  choose s₁ s₂ s₃ s₄ hs using fun i ↦ exists_rat_four (z i).im ε hε
  let a : ι → ℚ × ℚ := fun i ↦ (r₁ i, s₁ i)
  let b : ι → ℚ × ℚ := fun i ↦ (r₄ i, s₄ i)
  let a' : ι → ℚ × ℚ := fun i ↦ (r₂ i, s₂ i)
  let b' : ι → ℚ × ℚ := fun i ↦ (r₃ i, s₃ i)
  -- the closed box around `B'`
  let K : Set (ι → ℂ) := {w | ∀ i, ((r₂ i : ℝ) ≤ (w i).re ∧ (w i).re ≤ r₃ i) ∧
    ((s₂ i : ℝ) ≤ (w i).im ∧ (w i).im ≤ s₃ i)}
  have hK : IsClosed K := by
    simp only [K, setOf_forall, setOf_and]
    refine isClosed_iInter fun i ↦ ((isClosed_le continuous_const ?_).inter
      (isClosed_le ?_ continuous_const)).inter
      ((isClosed_le continuous_const ?_).inter (isClosed_le ?_ continuous_const)) <;> fun_prop
  have hBK : (ratBox a' b' : Set (ι → ℂ)) ⊆ K := fun w hw i ↦ by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := mem_ratBox.1 hw i
    exact ⟨⟨h₁.le, h₂.le⟩, ⟨h₃.le, h₄.le⟩⟩
  have hKB : K ⊆ ratBox a b := fun w hw ↦ mem_ratBox.2 fun i ↦ by
    obtain ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ := hw i
    obtain ⟨-, hr₁, hr₂, -, -, hr₃, hr₄, -⟩ := hr i
    obtain ⟨-, hs₁, hs₂, -, -, hs₃, hs₄, -⟩ := hs i
    exact ⟨by simp only [a]; linarith, by simp only [b]; linarith, by simp only [a]; linarith,
      by simp only [b]; linarith⟩
  have hBball : (ratBox a b : Set (ι → ℂ)) ⊆ ball z ε := fun w hw ↦ by
    rw [mem_ball, dist_pi_lt_iff hε]
    intro i
    obtain ⟨h₁, h₂, h₃, h₄⟩ := mem_ratBox.1 hw i
    obtain ⟨hr₁, -, -, -, -, -, -, hr₄⟩ := hr i
    obtain ⟨hs₁, -, -, -, -, -, -, hs₄⟩ := hs i
    simp only [a, b] at h₁ h₂ h₃ h₄
    rw [Complex.dist_eq]
    calc ‖w i - z i‖ ≤ |(w i - z i).re| + |(w i - z i).im| := Complex.norm_le_abs_re_add_abs_im _
      _ < ε / 2 + ε / 2 := by
        rw [Complex.sub_re, Complex.sub_im]
        gcongr
        · exact abs_lt.2 ⟨by linarith, by linarith⟩
        · exact abs_lt.2 ⟨by linarith, by linarith⟩
      _ = ε := by ring
  have hcl : closure (ratBox a' b' : Set (ι → ℂ)) ⊆ ratBox a b :=
    (closure_minimal hBK hK).trans hKB
  refine ⟨a, b, a', b', mem_ratBox.2 fun i ↦ ?_, ?_, hcl, hBball.trans hball⟩
  · obtain ⟨-, -, hr₂, hr₂', hr₃, hr₃', -, -⟩ := hr i
    obtain ⟨-, -, hs₂, hs₂', hs₃, hs₃', -, -⟩ := hs i
    exact ⟨hr₂', hr₃, hs₂', hs₃⟩
  · exact Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (isBounded_ball.subset (hcl.trans hBball))

end Complex

namespace ComplexAnalytic

/-- **Theorem B on chart images of boxes**: the structure sheaf of an analytic space is acyclic
on the image of a (rational) open box under a chart. -/
lemma structureAcyclic_chartOpen_ratBox {Z : AnalyticSpace.{u}} {n : ℕ}
    (φ : AnalyticSpace.complexAffineSpace.{u} n ⟶ Z)
    [AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion φ.toLRSHom]
    (a b : ULift.{u} (Fin n) → ℚ × ℚ) : StructureAcyclic (chartOpen φ (Complex.ratBox a b)) :=
  fun q hq ↦ AlgebraicGeometry.LocallyRingedSpace.subsingleton_H_structureSheafAb_of_image_eq
    φ.toLRSHom (Complex.ratBox a b) rfl q
    (Complex.TheoremB.subsingleton_H_restrictOpen_structureSheafAb_openBox
      (Complex.ratCorner a) (Complex.ratCorner b) (Complex.coe_ratBox a b) hq)

end ComplexAnalytic

end
