/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SchemePullbackSection
public import Other.AlgebraicGeometry.AnalyticSectionOfAlgebraic

/-!
# Inverse image of sections is natural in the sheaf of modules

A morphism of sheaves of modules commutes with the formation of inverse-image sections, both for
inverse image along a morphism of schemes (`Scheme.Modules.pullbackSection_map`) and for
analytification (`ComplexPoint.analyticSection_map`).  Both are the naturality of the unit of the
corresponding adjunction, read on sections.

These are what turn an *algebraic* identity `ψ(g) = u • g'` between local sections into the
corresponding identity for the analytified morphism and frames, which is how one checks that the
analytification of a reconstructed algebraic morphism has prescribed chart multipliers.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- **Naturality of inverse image on sections.** -/
theorem pullbackSection_map (f : X ⟶ Y) {M M' : Y.Modules} (ψ : M ⟶ M') (U : Y.Opens)
    (g : Γ(M, U)) :
    pullbackSection f M' U (ψ.app U g) =
      ((Scheme.Modules.pullback f).map ψ).app (f ⁻¹ᵁ U) (pullbackSection f M U g) := by
  have hnat := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality ψ
  exact congrArg
    (fun h : M ⟶ (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M') =>
      h.app U g) hnat

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- **Naturality of analytification on sections.** -/
theorem analyticSection_map {L L' : X.left.Modules} (ψ : L ⟶ L') (U : X.left.Opens)
    (g : Γ(L, U)) :
    analyticSection X d L' U (ψ.app U g) =
      ((moduleAnalytification X d).map ψ).val.app (op (analyticOpen X U))
        (analyticSection X d L U g) := by
  have hnat := (moduleAnalytificationAdjunction X d).unit.naturality ψ
  exact congrArg
    (fun h : L ⟶ (holomorphicModulePushforward X d).obj ((moduleAnalytification X d).obj L') =>
      h.app U g) hnat

end AlgebraicGeometry.ComplexPoint
