import Other.AlgebraicGeometry.ExplicitEllipticSurfaceCotangentGeneration

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

attribute [local instance] regularSectionAlgebra

noncomputable local instance testAlg (V : surface.Opens) : Algebra ℂ Γ(surface, V) :=
  regularSectionAlgebra (Over.mk surfaceToBase) V

local instance testBaseAffine : IsAffine base :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of ℂ)))

local instance testBaseTopAffine : IsAffine (⊤ : base.Opens).toScheme :=
  isAffineOpen_top base

example (ij : Fin 2 × Fin 2)
    (w : KaehlerDifferential ℂ Γ(surface, surfaceDifferentialOpen ij)) :
    ∃ a b : Γ(surface, surfaceDifferentialOpen ij),
      a • surfaceChartPulledDifferential 0 ij +
        b • surfaceChartPulledDifferential 1 ij = w := by
  let P : Subring Γ(surface, surfaceDifferentialOpen ij) :=
    { carrier := {x | ∃ a b : Γ(surface, surfaceDifferentialOpen ij),
          a • surfaceChartPulledDifferential 0 ij +
            b • surfaceChartPulledDifferential 1 ij =
              KaehlerDifferential.D ℂ Γ(surface, surfaceDifferentialOpen ij) x}
      zero_mem' := ⟨0, 0, by simp⟩
      one_mem' := ⟨0, 0, by simp⟩
      add_mem' := by
        rintro x y ⟨a, b, hab⟩ ⟨c, d, hcd⟩
        refine ⟨a + c, b + d, ?_⟩
        rw [add_smul, add_smul, map_add]
        rw [← hab, ← hcd]
        abel
      neg_mem' := by
        rintro x ⟨a, b, hab⟩
        refine ⟨-a, -b, ?_⟩
        rw [neg_smul, neg_smul, map_neg, ← hab]
        abel
      mul_mem' := by
        rintro x y ⟨a, b, hab⟩ ⟨c, d, hcd⟩
        refine ⟨x * c + y * a, x * d + y * b, ?_⟩
        rw [add_smul, add_smul, mul_smul, mul_smul, mul_smul, mul_smul,
          Derivation.leibniz, ← hab, ← hcd]
        simp only [smul_add]
        abel }
  have hP : P = ⊤ := by
    apply CommRingCat.subring_eq_top_of_isPushout
      (surfaceDifferentialChart_section_isPushout ij)
    · intro x
      obtain ⟨a, ha⟩ := exists_surfaceChart_D_fstPullback_eq_smul ij x
      have heq :
          surfaceSectionPullback (pullback.fst curveToBase curveToBase) rfl
              (chart (differentialChartIndex ij.1)) (surfaceDifferentialOpen ij)
              inf_le_left x =
            (pullback.fst curveToBase curveToBase).appLE
              (chart (differentialChartIndex ij.1)) (surfaceDifferentialOpen ij)
              inf_le_left x := by
        rfl
      exact ⟨a, 0, by
        simpa [P, heq] using ha⟩
    · intro x
      obtain ⟨b, hb⟩ := exists_surfaceChart_D_sndPullback_eq_smul ij x
      have heq :
          surfaceSectionPullback (pullback.snd curveToBase curveToBase)
              pullback.condition.symm (chart (differentialChartIndex ij.2))
              (surfaceDifferentialOpen ij) inf_le_right x =
            (pullback.snd curveToBase curveToBase).appLE
              (chart (differentialChartIndex ij.2)) (surfaceDifferentialOpen ij)
              inf_le_right x := by
        rfl
      exact ⟨0, b, by
        simpa [P, heq] using hb⟩
  have hD (x : Γ(surface, surfaceDifferentialOpen ij)) :
      ∃ a b : Γ(surface, surfaceDifferentialOpen ij),
        a • surfaceChartPulledDifferential 0 ij +
          b • surfaceChartPulledDifferential 1 ij =
            KaehlerDifferential.D ℂ Γ(surface, surfaceDifferentialOpen ij) x := by
    have hx : x ∈ P := by rw [hP]; trivial
    exact hx
  have hw : w ∈ Submodule.span Γ(surface, surfaceDifferentialOpen ij)
      (Set.range (KaehlerDifferential.D ℂ
        Γ(surface, surfaceDifferentialOpen ij))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  let Q : KaehlerDifferential ℂ Γ(surface, surfaceDifferentialOpen ij) → Prop :=
    fun z ↦ ∃ a b : Γ(surface, surfaceDifferentialOpen ij),
      a • surfaceChartPulledDifferential 0 ij +
        b • surfaceChartPulledDifferential 1 ij = z
  refine Submodule.span_induction (p := fun z _ ↦ Q z) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨x, rfl⟩
    exact hD x
  · exact ⟨0, 0, by simp⟩
  · rintro x y _ _ ⟨a, b, hab⟩ ⟨c, d, hcd⟩
    refine ⟨a + c, b + d, ?_⟩
    rw [add_smul, add_smul]
    calc
      _ = (a • surfaceChartPulledDifferential 0 ij +
            b • surfaceChartPulledDifferential 1 ij) +
          (c • surfaceChartPulledDifferential 0 ij +
            d • surfaceChartPulledDifferential 1 ij) := by abel
      _ = x + y := by rw [hab, hcd]
  · rintro c x _ ⟨a, b, hab⟩
    exact ⟨c * a, c * b, by rw [mul_smul, mul_smul, ← smul_add, hab]⟩

end AlgebraicGeometry.ExplicitEllipticCandidate
