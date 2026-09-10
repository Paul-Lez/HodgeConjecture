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

This guide explains the statement of the Hodge conjecture formalized in the
[`HodgeConjecture`](https://github.com/Paul-Lez/HodgeConjecture) repository: the mathematics behind
each definition, the Lean declarations that implement it, and the points where the implementation
departs from the textbook presentation. It follows the construction rather than the directory
tree. The Hodge side compares rational cohomology with the Hodge filtration on holomorphic de Rham
cohomology; the cycle side attaches a cohomology class to every irreducible subvariety; and the
statement is the inclusion of one rational subspace in the other.

The conjecture is stated, not proved. A few classical theorems surrounding the statement are not
yet formalized either; {ref "scope-and-status"}[Scope and status] lists them.

The Lean snippets in this guide are elaborated when the site is built, so every declaration shown
here exists in the repository with the displayed type. The site is generated with
[Verso](https://github.com/leanprover/verso).

{include 1 HodgeGuide.Overview}

{include 1 HodgeGuide.HodgeSide}

{include 1 HodgeGuide.CycleSide}

{include 1 HodgeGuide.FundamentalClass}

{include 1 HodgeGuide.Statement}

{include 1 HodgeGuide.References}
