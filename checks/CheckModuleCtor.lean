import Other.AlgebraicGeometry.HolomorphicFormFunctionMultiplication

open CategoryTheory TopologicalSpace
open AlgebraicGeometry ComplexPoint

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ))) (d p : ℕ)
  [SmoothOfRelativeDimension d X.hom]

#synth SMul (OpenHolomorphicFunctions X d (.op ⊤))
  (HolomorphicForm X d (.op ⊤) p)

end AlgebraicGeometry.ComplexPoint

#check Module.ofMinimalAxioms
#check Module.mk
