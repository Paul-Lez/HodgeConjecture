/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveTwistMultiplyTransport

/-!
# Two tools for the reconstruction with complex coefficients

* `Scheme.Modules.globalSmulHom M c` — multiplication by a global regular function, as an
  endomorphism of a sheaf of modules on a scheme.  Composing the multiplication morphisms of
  `ProjectiveSpectrumTwistMultiply.lean` with these makes the assignment
  "form ↦ morphism of twists" complex-linear, which is what is needed because `ℙᴺ_ℂ` is a base
  change of `Proj ℤ[X]` and the forms produced by the `H⁰` comparison have complex coefficients.
* `Other.ProjectiveChart.eval_deh` — the evaluation of a dehomogenisation:
  `eval z (deh ℂ i Q) = eval (insertNth i 1 z) Q`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The section rings of the `RingCat`-valued structure sheaf are commutative. -/
theorem ringCatSheaf_mul_comm {U : (TopologicalSpace.Opens X)ᵒᵖ}
    (x y : X.ringCatSheaf.obj.obj U) : x * y = y * x :=
  mul_comm (G := X.presheaf.obj U) x y

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by a global regular function, as an endomorphism of a sheaf of modules. -/
def globalSmulHom (M : X.Modules) (c : X.ringCatSheaf.obj.obj (op ⊤)) : M ⟶ M :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun x =>
            X.ringCatSheaf.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op c • x
          map_add' := fun x y => smul_add _ _ _
          map_smul' := fun r x => by
            show X.ringCatSheaf.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op c • (r • x) =
              r • (X.ringCatSheaf.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op c • x)
            rw [smul_smul, smul_smul,
              ringCatSheaf_mul_comm (X := X)
                (X.ringCatSheaf.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op c) r] }
     naturality := fun {U V} f => by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro x
       show X.ringCatSheaf.obj.map (homOfLE (le_top : V.unop ≤ ⊤)).op c • M.val.map f x =
         M.val.map f (X.ringCatSheaf.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op c • x)
       rw [M.val.map_smul]
       congr 1
       rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
       rfl }⟩

set_option backward.isDefEq.respectTransparency false in
theorem globalSmulHom_app (M : X.Modules) (c : X.ringCatSheaf.obj.obj (op ⊤)) (U : X.Opens)
    (x : M.val.obj (op U)) :
    (globalSmulHom M c).app U x =
      X.ringCatSheaf.obj.map (homOfLE (le_top : U ≤ ⊤)).op c • x := rfl

end AlgebraicGeometry.Scheme.Modules

namespace Other.ProjectiveChart

open MvPolynomial

/-- **Evaluation of a dehomogenisation.**  Setting `Xᵢ = 1` and the remaining variables to `z` is
evaluation of the original form at `insertNth i 1 z`. -/
theorem eval_deh {N : ℕ} (i : Fin (N + 1)) (z : Fin N → ℂ)
    (Q : MvPolynomial (Fin (N + 1)) ℂ) :
    MvPolynomial.eval z (deh ℂ i Q) =
      MvPolynomial.eval (i.insertNth (1 : ℂ) z) Q := by
  have hcomp : ((MvPolynomial.eval z).comp (deh ℂ i) :
        MvPolynomial (Fin (N + 1)) ℂ →+* ℂ) =
      MvPolynomial.eval (i.insertNth (1 : ℂ) z) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro l
      refine Fin.succAboveCases i ?_ ?_ l
      · simp
      · intro j
        simp
  exact DFunLike.congr_fun hcomp Q

end Other.ProjectiveChart
