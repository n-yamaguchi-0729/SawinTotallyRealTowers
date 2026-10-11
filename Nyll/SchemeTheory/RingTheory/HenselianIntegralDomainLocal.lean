/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.HenselianFiniteDomainLocal
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Integral domains over Henselian local rings are local

Each element belongs to a finite simple subalgebra. That subalgebra is a
domain and is local by the existing finite-domain Henselian theorem. Its
unit alternative maps into the original integral domain.
-/

namespace SchemeTheory

universe u v

/-- An integral algebra which is a domain over a Henselian local ring is
local. No module-finiteness assumption on the full algebra is needed. -/
theorem isLocalRing_of_integral_domain_henselian
    (R : Type u) (B : Type v) [CommRing R] [HenselianLocalRing R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.IsIntegral R B] :
    IsLocalRing B := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro b
  let C : Subalgebra R B := Algebra.adjoin R {b}
  have : Module.Finite R C :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral b)
  have : IsLocalRing C := isLocalRing_of_finite_domain_henselian R C
  let c : C := ⟨b, Algebra.subset_adjoin (Set.mem_singleton b)⟩
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with hc | hc
  · exact Or.inl (hc.map C.val.toRingHom)
  · exact Or.inr (hc.map C.val.toRingHom)

end SchemeTheory
