/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteUnramifiedTower
import Mathlib.NumberTheory.RamificationInertia.Unramified

set_option autoImplicit false

/-!
# Finite ramification support in number-field towers

The initial arithmetic group in the Sawin construction permits ramification
at specified finite places. This predicate retains the existing local
unramifiedness condition outside that set. Its tower lemmas work also for
extensions of even degree; real places are a separate condition.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u v w

namespace ClassFieldTower.Sawin

/-- All finite places above the complement of `S` are unramified.
Finiteness of `S` is unnecessary for the tower properties below. -/
def IsUnramifiedAtFinitePlacesOutside
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (S : Set (HeightOneSpectrum (𝓞 K))) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 L),
    finitePlaceBelow (K := K) P ∉ S →
      Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal

namespace IsUnramifiedAtFinitePlacesOutside

section Basic

variable {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- Enlarging the permitted ramification set preserves the condition. -/
theorem mono {S T : Set (HeightOneSpectrum (𝓞 K))}
    (hST : S ⊆ T) (h : IsUnramifiedAtFinitePlacesOutside K L S) :
    IsUnramifiedAtFinitePlacesOutside K L T := by
  intro P hP
  exact h P (fun hPS ↦ hP (hST hPS))

/-- Empty support recovers the existing finite-place predicate. -/
theorem empty_iff :
    IsUnramifiedAtFinitePlacesOutside K L ∅ ↔
      IsUnramifiedAtFinitePlaces K L := by
  constructor
  · intro h P
    exact h P (Set.notMem_empty (finitePlaceBelow (K := K) P))
  · intro h P _hP
    exact h P

end Basic

/-- The base field itself is a candidate for every support set. -/
theorem refl (K : Type u) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    IsUnramifiedAtFinitePlacesOutside K K S := by
  intro P _hP
  exact IsUnramifiedAtFinitePlaces.refl K P

section Tower

variable {k : Type u} {K : Type v} {F : Type w}
    [Field k] [NumberField k]
    [Field K] [NumberField K]
    [Field F] [NumberField F]
    [Algebra k K] [Algebra k F] [Algebra K F]
    [IsScalarTower k K F]

/-- Over an intermediate field, the permitted support is the set of places
above the original support. -/
theorem top (S : Set (HeightOneSpectrum (𝓞 k)))
    (h : IsUnramifiedAtFinitePlacesOutside k F S) :
    IsUnramifiedAtFinitePlacesOutside K F
      ((finitePlaceBelow (K := k) (L := K)) ⁻¹' S) := by
  intro P hP
  have hOutside : finitePlaceBelow (K := k) P ∉ S := by
    simpa only [Set.mem_preimage, finitePlaceBelow_finitePlaceBelow] using hP
  let : Algebra.IsUnramifiedAt (𝓞 k) P.asIdeal := h P hOutside
  exact Algebra.IsUnramifiedAt.of_restrictScalars (𝓞 k) P.asIdeal

/-- A finite intermediate number field inherits the same ramification
support on the base. A prime above each intermediate prime is supplied by
lying over, rather than assumed as extra input. -/
theorem bot (S : Set (HeightOneSpectrum (𝓞 k)))
    (h : IsUnramifiedAtFinitePlacesOutside k F S) :
    IsUnramifiedAtFinitePlacesOutside k K S := by
  intro q hq
  let : Module.Finite (𝓞 k) (𝓞 K) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite (K := k) (L := K)
  let : Module.Finite (𝓞 K) (𝓞 F) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite (K := K) (L := F)
  let : Module.Finite (𝓞 k) (𝓞 F) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite (K := k) (L := F)
  obtain ⟨⟨P, hPrime, hOver⟩⟩ := q.asIdeal.nonempty_primesOver (S := 𝓞 F)
  let : P.IsPrime := hPrime
  let : P.LiesOver q.asIdeal := hOver
  let Q : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := P
      isPrime := hPrime
      ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot q.ne_bot P }
  have hBelow : finitePlaceBelow (K := K) Q = q := by
    apply HeightOneSpectrum.ext
    exact (P.over_def q.asIdeal).symm
  have hOutside : finitePlaceBelow (K := k) Q ∉ S := by
    rw [← finitePlaceBelow_finitePlaceBelow (K := k) (M := K) Q, hBelow]
    exact hq
  let : Algebra.IsUnramifiedAt (𝓞 k) P := h Q hOutside
  exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 k) q.asIdeal P

end Tower

end IsUnramifiedAtFinitePlacesOutside

end ClassFieldTower.Sawin
