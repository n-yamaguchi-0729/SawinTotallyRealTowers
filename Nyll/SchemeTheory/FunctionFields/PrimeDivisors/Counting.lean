/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Dedekind
import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.PrimesOver

/-!
# Counting prime divisors over a base prime

A prime divisor finite on a Dedekind model has a nonzero prime center, and
that center determines the divisor.  Thus prime divisors whose centers lie
over a fixed base prime inject into the set of primes over that base prime.
The ramification--inertia count then bounds their number by the module rank.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace PrimeDivisorCounting

universe uK uR uS uF

variable {K : Type uK} {R : Type uR} {S : Type uS} {F : Type uF}
  [Field K] [CommRing R] [CommRing S] [Field F]
  [Algebra R S] [Algebra K S] [Algebra K F] [Algebra S F]
  [IsScalarTower K S F]

/--
A prime divisor finite on the model `S` whose center contracts to `p`.

The equality stored in `center_liesOver` is the defining property of the
collection being counted, rather than an auxiliary theorem used to force a
later proof.
-/
structure FiniteDivisorOver (p : Ideal R) where
  /-- The underlying prime divisor of the function field. -/
  divisor : FunctionFieldPrimeDivisor K F
  /-- The prime divisor is finite along the chosen map from the model S. -/
  finite :
    divisor.FiniteAlong (IsScalarTower.toAlgHom K S F)
  /-- The center on S contracts to the ideal p of R. -/
  center_liesOver :
    p =
      (divisor.centerAlong (IsScalarTower.toAlgHom K S F) finite).under R

namespace FiniteDivisorOver

variable {p : Ideal R}

/-- Equality of the underlying prime divisors determines bundled elements. -/
@[ext]
theorem ext
    {v₁ v₂ : FiniteDivisorOver (K := K) (S := S) (F := F) p}
    (h : v₁.divisor = v₂.divisor) :
    v₁ = v₂ := by
  rcases v₁ with ⟨v₁, hfinite₁, hover₁⟩
  rcases v₂ with ⟨v₂, hfinite₂, hover₂⟩
  change v₁ = v₂ at h
  subst v₂
  rfl

/-- The center as an element of the set of primes of `S` above `p`. -/
def centerMap
    (v : FiniteDivisorOver (K := K) (S := S) (F := F) p) :
    p.primesOver S :=
  ⟨v.divisor.centerAlong (IsScalarTower.toAlgHom K S F) v.finite,
    ⟨v.divisor.centerAlong_isPrime
        (IsScalarTower.toAlgHom K S F) v.finite,
      ⟨v.center_liesOver⟩⟩⟩

@[simp]
theorem centerMap_val
    (v : FiniteDivisorOver (K := K) (S := S) (F := F) p) :
    (v.centerMap : Ideal S) =
      v.divisor.centerAlong (IsScalarTower.toAlgHom K S F) v.finite :=
  rfl

/--
For a Dedekind model inside its fraction field, the center map is injective.
-/
theorem centerMap_injective
    [IsDedekindDomain S] [IsFractionRing S F] :
    Function.Injective
      (centerMap :
        FiniteDivisorOver (K := K) (S := S) (F := F) p →
          p.primesOver S) := by
  intro v₁ v₂ hcenter
  apply FiniteDivisorOver.ext
  apply v₁.divisor.eq_of_centerAlong_eq
      v₂.divisor v₁.finite v₂.finite
  exact congrArg Subtype.val hcenter

end FiniteDivisorOver

/--
The number of prime divisors finite on `S` and centered over `p` is at most
the rank of the finite flat extension `S / R`.
-/
theorem card_finiteDivisorOver_le_finrank
    [IsDomain R] [IsDedekindDomain S] [IsFractionRing S F]
    [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] :
    Nat.card (FiniteDivisorOver (K := K) (S := S) (F := F) p) ≤
      Module.finrank R S := by
  let : Fintype (p.primesOver S) :=
    (Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) p).fintype
  calc
    Nat.card (FiniteDivisorOver (K := K) (S := S) (F := F) p) ≤
        Nat.card (p.primesOver S) :=
      Nat.card_le_card_of_injective
        FiniteDivisorOver.centerMap
        FiniteDivisorOver.centerMap_injective
    _ ≤ Module.finrank R S :=
      PrimeCounting.card_primesOver_le_finrank p

end PrimeDivisorCounting
end Chapter06
end FieldArithmetic
