import Other.AlgebraicGeometry.ExplicitEllipticSurfaceTopFormCech

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

@[expose] noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (X : Over (Spec (.of ℂ))) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

attribute [local instance] regularSectionAlgebra

local instance checkRegularSectionAlgebra (U : X.left.Opens) :
    Algebra ℂ Γ(X.left, U) := regularSectionAlgebra X U

theorem check_regularFunctionMul_regularKaehlerWedge
    (U : X.left.Opens) (a b : Γ(X.left, U))
    (w z : KaehlerDifferential ℂ Γ(X.left, U)) :
    holomorphicFormFunctionMul X d (.op (regularAnalyticOpen X U)) 2
        (regularToHolomorphicAlgHom X d U (a * b))
        (regularFormToHolomorphicForm X d U 2
          (Algebra.DeRham.kaehlerWedge ℂ Γ(X.left, U) w z)) =
      regularFormToHolomorphicForm X d U 2
        (Algebra.DeRham.kaehlerWedge ℂ Γ(X.left, U) (a • w) (b • z)) := by
  obtain ⟨v, rfl⟩ :=
    KaehlerDifferential.linearCombination_surjective ℂ Γ(X.left, U) w
  obtain ⟨u, rfl⟩ :=
    KaehlerDifferential.linearCombination_surjective ℂ Γ(X.left, U) z
  induction v using Finsupp.induction with
  | zero => simp [Algebra.DeRham.kaehlerWedge]
  | single_add e c v he hc ih =>
    simp only [map_add, Finsupp.linearCombination_single, smul_add,
      LinearMap.add_apply]
    rw [ih]
    congr 1
    clear ih
    induction u using Finsupp.induction with
    | zero => simp [Algebra.DeRham.kaehlerWedge]
    | single_add g f u hg hf ih' =>
      simp only [map_add, Finsupp.linearCombination_single, smul_add,
        LinearMap.add_apply]
      rw [ih']
      congr 1
      clear ih'
      rw [smul_smul, smul_smul,
        Algebra.DeRham.kaehlerWedge_smul_D_smul_D,
        Algebra.DeRham.kaehlerWedge_smul_D_smul_D]
      simp only [regularFormToHolomorphicForm, LinearMap.comp_apply,
        Algebra.DeRham.map_mk]
      change holomorphicFormFunctionMul X d
          (.op (regularAnalyticOpen X U)) 2
          (regularToHolomorphicAlgHom X d U (a * b))
          ((holomorphicFormRelations X d
            (.op (regularAnalyticOpen X U)) 2).mkQ
              (Finsupp.single
                (regularToHolomorphicAlgHom X d U (c * f),
                  fun i => regularToHolomorphicAlgHom X d U (![e, g] i)) 1)) = _
      rw [holomorphicFormFunctionMul_mk]
      apply congrArg
      rw [rawHolomorphicFormFunctionMul_single]
      congr 2
      · simp only [map_mul]
        ring

end

end AlgebraicGeometry.ComplexPoint
