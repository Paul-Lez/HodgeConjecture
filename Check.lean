import Other.AlgebraicGeometry.ProjectiveHolomorphicFunctions

@[expose] noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff BigOperators

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  [IsProjective X.hom] [IsIntegral X.left]

example (a : Γ(X.left, ⊤)) : ∃ c : ℂ, a = constantRegularSection X c := by
  let f : C^ω⟮𝓘(ℂ, Fin d → ℂ), ComplexPoint X; ℂ⟯ :=
    ⟨fun z ↦ Point.evaluate ⊤ a z,
      fun z ↦ contMDiffAt_evaluate X d ⊤ a z trivial⟩
  let F : Finset ℂ := (globalHolomorphic_range_finite X d f).toFinset
  let p : Γ(X.left, ⊤) := ∏ c ∈ F, (a - constantRegularSection X c)
  have hpOpen : X.left.basicOpen p = ⊥ := by
    apply le_antisymm
    · intro x hx
      letI : LocallyOfFiniteType X.hom := inferInstance
      letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
      obtain ⟨y, hy, hyClosed⟩ := nonempty_inter_closedPoints
        (X := X.left) (Z := (X.left.basicOpen p : Set X.left))
        ⟨x, hx⟩ (X.left.basicOpen p).isOpen.isLocallyClosed
      let q := (pointEquivClosedPoint X.hom).symm ⟨y, hyClosed⟩
      let z : ComplexPoint X := Over.homMk q.1 q.2
      have hq := (pointEquivClosedPoint X.hom).apply_symm_apply ⟨y, hyClosed⟩
      have hzUnderlying : z.underlying = y := congrArg Subtype.val hq
      have hzOpen : z ∈ Point.overOpen (X.left.basicOpen p) := by
        change z.underlying ∈ X.left.basicOpen p
        rw [hzUnderlying]
        exact hy
      have hpNe : Point.evaluate ⊤ p z ≠ 0 :=
        (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero p z trivial).mp hzOpen
      have hzF : Point.evaluate ⊤ a z ∈ F := by
        change Point.evaluate ⊤ a z ∈
          (globalHolomorphic_range_finite X d f).toFinset
        rw [Set.Finite.mem_toFinset]
        exact ⟨z, rfl⟩
      apply hpNe
      rw [← Point.evaluationHom_hom_apply ⊤ ⟨z, trivial⟩]
      simp only [p, map_prod, map_sub, evaluate_constantRegularSection]
      exact Finset.prod_eq_zero_iff.mpr ⟨Point.evaluate ⊤ a z, hzF, sub_self _⟩
    · exact bot_le
  have hp : p = 0 := Scheme.eq_zero_of_basicOpen_eq_bot p hpOpen
  rw [p, Finset.prod_eq_zero_iff] at hp
  obtain ⟨c, -, hc⟩ := hp
  exact ⟨c, sub_eq_zero.mp hc⟩

end AlgebraicGeometry.ComplexPoint
