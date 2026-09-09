/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import HodgeGuide.Overview
import HodgeGuide.HodgeSide
import HodgeGuide.CycleSide
import HodgeGuide.FundamentalClass
import HodgeGuide.Statement
import HodgeGuide.References

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Hodge Conjecture Formalization" =>

%%%
authors := ["The HodgeConjecture contributors"]
%%%

This is a mathematical and Lean guide to the formalization in the
[`HodgeConjecture`](https://github.com/Paul-Lez/HodgeConjecture) repository.
It follows the construction rather than the directory tree: rational classes are compared with
filtered holomorphic de Rham cohomology; each irreducible component receives an exactly normalized
supported class and the corresponding ambient Borel--Moore fundamental class; and the two sides
meet in one inclusion of rational subspaces.

The guide distinguishes two questions that are easy to conflate. The component class used in the
statement is constructed for arbitrary codimension, including singular components. What is not yet
proved is that the resulting map on cycles descends through rational equivalence, or that its values
are Hodge classes. Those are the remaining comparison theorems, not hidden arguments to the
definition.

{include 1 HodgeGuide.Overview}

{include 1 HodgeGuide.HodgeSide}

{include 1 HodgeGuide.CycleSide}

{include 1 HodgeGuide.FundamentalClass}

{include 1 HodgeGuide.Statement}

{include 1 HodgeGuide.References}
