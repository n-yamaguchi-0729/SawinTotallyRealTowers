/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# An explicit affine strict-normal-crossings chart

This file fixes the lightweight local-algebra data used by the one-point
inertia theorem.  The chart is a proposition, not a typeclass or a structure,
so merely carrying it does not enlarge instance search.

The boundary components are explicitly labelled by the first `r` members of
a finite regular system of parameters.  Their primality records that the
labelled local branches are irreducible.  The boundary equation is associated
to their product, as in the usual definition of a strict normal-crossings
divisor.
-/

namespace EtaleFundamentalGroups

open scoped BigOperators

universe u

/-- The indices of the first `r` members of a `d`-element parameter family. -/
def boundaryIndices (d r : ℕ) : Finset (Fin d) :=
  Finset.univ.filter fun i ↦ i.1 < r

/-- The product of the parameter functions labelling the boundary branches. -/
def boundaryProduct {R : Type u} [CommMonoid R] {d : ℕ}
    (t : Fin d → R) (r : ℕ) : R :=
  ∏ i ∈ boundaryIndices d r, t i

/-- A finite family is a regular system of parameters when it is a regular
sequence and generates the maximal ideal. -/
abbrev IsRegularSystemOfParameters
    {R : Type u} [CommRing R] [IsLocalRing R] {d : ℕ}
    (t : Fin d → R) : Prop :=
  AlgebraicGeometry.Scheme.IsRegularSystemOfParameters t

/-- An explicit split strict-normal-crossings equation in a local ring.

`t` is the full regular system of parameters, the first `r` parameters label
the irreducible local boundary branches, and `f` is a local equation of their
reduced union.  Primality is included as primitive branch data; it is supplied
geometrically by the irreducible regular components in a strict chart rather
than by a later ramification conclusion.  Regularity of each branch quotient
is imposed scheme-theoretically, at every specialization of the local chart;
this is the algebraic content of saying that the boundary components, rather
than only their closed-point local rings, are regular. -/
def IsSplitStrictNormalCrossingsAt
    {R : Type u} [CommRing R] [IsLocalRing R] {d : ℕ}
    (f : R) (t : Fin d → R) (r : ℕ) : Prop :=
  0 < r ∧ r ≤ d ∧ IsRegularSystemOfParameters t ∧
    (∀ i : Fin d, i.1 < r → Prime (t i)) ∧
    Associated f (boundaryProduct t r) ∧
    (∀ i : Fin d, i.1 < r →
      IsRegularRing (R ⧸ Ideal.span {t i}))

end EtaleFundamentalGroups
