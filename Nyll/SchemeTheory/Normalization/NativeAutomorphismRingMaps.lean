/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.NormalizationAutomorphismGroupMap
import Nyll.SchemeTheory.Normalization.ScalarRestrictionGroupMap
import Mathlib.Algebra.Category.Ring.Basic

/-!
# Ring maps underlying normalization automorphisms

Defines the underlying ring maps of coefficient and Galois automorphisms, together with the
inclusion of the normalization into its ambient algebra.
-/

namespace SchemeTheory

universe u v

/-- The individual actual coefficient automorphism as a ring map. -/
def commAlgAutomorphismRingHom (A : Type u) [CommRing A] (C : CommAlgCat.{v} A)
    (g : commAlgAutomorphismGroup A C) : C →+* C := g.toRingHom

/-- The individual actual field automorphism as a ring map. -/
def galoisAutomorphismRingHom (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] (g : Gal(L/K)) : L →+* L :=
  g.toRingHom

/-- The native normalization coefficient inclusion into its ambient algebra. -/
def normalizationAmbientRingHom (A : Type u) [CommRing A] (C : CommAlgCat.{v} A) :
    normalizationCommAlgCat A C →+* C :=
  (integralClosure A C).toSubring.subtype

end SchemeTheory
