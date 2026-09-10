import Other.AlgebraicGeometry.ExplicitEllipticSurfaceDoubleDlog

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.ExplicitEllipticCandidate
open AlgebraicGeometry.ComplexPoint

#check Abelian.Ext.instZero
#check instZeroExt
#check Abelian.Ext.zero
#check Abelian.Ext.mk₀_zero
#synth Zero (Abelian.Ext.{1}
  (constantIntegerSheaf (Over.mk surfaceToBase))
  surfaceCechHolomorphicFunctionSheaf 2)

#synth Zero (Abelian.Ext.{1}
  (constantIntegerSheaf surfaceVariety)
  surfaceCechHolomorphicFunctionSheaf 2)
