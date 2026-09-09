/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import HodgeConjecture.Statement

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "Reading the formalization" =>

The object of study is a smooth projective integral scheme $`X` over $`\mathbb C`. In Lean the
base is not implicit: it is a morphism `structureMap : X ⟶ Spec ℂ`, accompanied by the propositions
`Smooth structureMap` and `IsProjective structureMap`. A codimension is a natural number `p`, while
cohomological degrees are integers. Thus the class of a codimension-$`p` cycle lives in degree
`2 * (p : ℤ)`.

The end product has a deliberately small type.

```lean
#check HodgeConjecture
#check AlgebraicGeometry.ComplexPoint.hodgeClasses
#check AlgebraicGeometry.ComplexPoint.algebraicCycleClassSpan
```

Mathematically it is the inclusion

$$`\operatorname{Hdg}^p(X;\mathbb Q)
  \subseteq
  \langle \operatorname{cl}_X(Z)\mid Z\subseteq X\text{ irreducible},
  \operatorname{codim}_X Z=p\rangle_{\mathbb Q}.`

The definitions behind this compact formula follow the next pipeline.

1. Build the analytic space $`X(\mathbb C)`, its holomorphic de Rham complex, and the comparison
   from rational constant-sheaf cohomology.
2. Define $`F^p` by truncating the de Rham complex, then pull that filtration back to rational
   cohomology to obtain $`\operatorname{Hdg}^p`.
3. Represent an irreducible subvariety by the closure of a scheme point of coheight $`p`.
4. On its smooth locus, glue the local complex-normal orientation coclasses in degree $`2p`.
5. Extend the normalized coclass uniquely across the singular boundary using purity, a finite
   smooth filtration, and the nested-support localization sequence.
6. Compare that supported class with ambient chain-sheaf Borel--Moore homology and then forget
   support to ordinary rational cohomology.
7. Extend additively over integral cycles and by scalars over rational cycles; the final statement
   uses the span of the actual component values.

# What is constructed, and what remains

The current statement imports the constructed sheaf cycle-class development. In particular, an
arbitrary component may be singular: its supported class, ordinary class, and corresponding
ambient-supported Borel--Moore class are terms, not fields of a hypothesis package.

Three boundaries nevertheless matter.

* The Borel--Moore group is an *ambient-supported* chain-sheaf group
  $`H_i^{\mathrm{BM}}(Z\subset X;\mathbb Q)`. The code does not yet identify it with an intrinsic
  compactification-independent Borel--Moore homology of $`Z`.
* The constructed linear map is defined on rational algebraic *cycles*. It has not yet been proved
  to kill principal divisors, so it is not yet a map out of the rational Chow group.
* The repository defines the conjectural inclusion but does not prove it. Nor does the present
  construction yet prove that every component class belongs to the Hodge subspace; that is the
  classical cycle-class/Hodge-type theorem needed for equivalent surjectivity formulations.

# Degree and support conventions

For a complex manifold of complex dimension $`d`, the real dimension is $`2d`. If $`Z` has complex
codimension $`p`, its top-dimensional degree is $`2(d-p)`. Smooth-ambient
Alexander--Poincaré duality gives

$$`H^{\mathrm{BM}}_{2(d-p)}(Z\subset X;\mathbb Q)
  \simeq H_Z^{2d-2(d-p)}(X;\mathbb Q)=H_Z^{2p}(X;\mathbb Q).`

This arithmetic explains the `2 * (d - p)` and `2 * p` indices in the implementation. A supported
class lies in $`H_Z^{2p}(X;\mathbb Q)`; only after applying `forgetSupport` does it lie in the
ordinary group $`H^{2p}(X;\mathbb Q)` used by the conjecture.
