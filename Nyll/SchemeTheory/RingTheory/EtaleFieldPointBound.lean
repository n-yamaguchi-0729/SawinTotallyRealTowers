/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.SetTheory.Cardinal.Finite


/-!
# Uniform bounds for field-valued points on étale charts

Maps from a standard étale algebra to a field inject into the roots of its
defining monic polynomial. The existing standard-étale hom equivalence and
root-cardinality theorem therefore give actual finiteness and a numerical
bound independent of the target field and of its algebra structure.

The local structure theorem supplies such a principal chart at every prime
of an arbitrary étale algebra. The chart and bound are chosen before the
target field. No tensor-product decomposition or assumed fiber comparison
is introduced. Finite-cover aggregation and conversion to cardinalities of
scheme-theoretic geometric fibers remain subsequent steps toward 09Z0.
-/

noncomputable section

universe u v w

namespace StandardEtalePair

/-- Field-valued points of a standard étale algebra form a finite set of
cardinality at most the degree of its defining monic polynomial. -/
theorem fieldHom_finite_and_card_le
    {R : Type u} [CommRing R] (P : StandardEtalePair R)
    (K : Type v) [Field K] [Algebra R K] :
    Finite (P.Ring →ₐ[R] K) ∧ Nat.card (P.Ring →ₐ[R] K) ≤ P.f.natDegree := by
  let ι : (P.Ring →ₐ[R] K) → P.f.rootSet K := fun φ =>
    ⟨(P.homEquiv φ).1, P.monic_f.mem_rootSet.mpr (P.homEquiv φ).2.1⟩
  have hι : Function.Injective ι := by
    intro φ ψ h
    apply P.homEquiv.injective
    exact Subtype.ext (congrArg (fun z : P.f.rootSet K => z.val) h)
  have hfinite : Finite (P.Ring →ₐ[R] K) := Finite.of_injective ι hι
  have hcard : Nat.card (P.Ring →ₐ[R] K) ≤ Nat.card (P.f.rootSet K) :=
    Nat.card_le_card_of_injective ι hι
  exact ⟨hfinite, hcard.trans (P.f.ncard_rootSet_le K)⟩

end StandardEtalePair

namespace Algebra.Etale

/-- Every prime of an étale algebra has a principal neighborhood with a
finite bound on all field-valued points. Both the neighborhood and the bound
are independent of the field and its map from the base ring. -/
theorem exists_local_uniform_fieldHom_bound
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Etale R S]
    (Q : Ideal S) [Q.IsPrime] :
    ∃ s : S, s ∉ Q ∧ ∃ N : ℕ,
      ∀ (K : Type w) [Field K] [Algebra R K],
        Finite (Localization.Away s →ₐ[R] K) ∧
          Nat.card (Localization.Away s →ₐ[R] K) ≤ N := by
  obtain ⟨s, hs, hstandard⟩ := IsEtaleAt.exists_isStandardEtale (R := R) Q
  obtain ⟨P⟩ := hstandard.nonempty_standardEtalePresentation
  refine ⟨s, hs, P.f.natDegree, ?_⟩
  intro K _ _
  let e : (Localization.Away s →ₐ[R] K) ≃ (P.Ring →ₐ[R] K) :=
    AlgEquiv.arrowCongr P.equivRing (AlgEquiv.refl : K ≃ₐ[R] K)
  obtain ⟨hfinite, hcard⟩ := P.P.fieldHom_finite_and_card_le K
  have : Finite (P.Ring →ₐ[R] K) := hfinite
  refine ⟨Finite.of_injective e e.injective, ?_⟩
  exact (Nat.card_congr e).trans_le hcard

end Algebra.Etale
