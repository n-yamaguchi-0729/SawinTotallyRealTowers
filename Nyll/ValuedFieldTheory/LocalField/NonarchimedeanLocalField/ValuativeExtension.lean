/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.Topology.Algebra.Valued.ValuativeRel
/-!
# Valuative extensions

Records when the valuation ring of an extension field is integral over the
base valuation ring, the hypothesis needed to restrict field norms integrally.
-/

@[expose] public section

namespace Valuation

/-- A nontrivial valuation stays nontrivial after passing to any valuation
which extends it along an algebra map. -/
theorem IsNontrivial.of_hasExtension
    {R A ΓR ΓA : Type*}
    [CommRing R] [Ring A]
    [LinearOrderedCommMonoidWithZero ΓR]
    [LinearOrderedCommMonoidWithZero ΓA]
    [Algebra R A]
    (vR : Valuation R ΓR) (vA : Valuation A ΓA)
    [vR.IsNontrivial] [vR.HasExtension vA] :
    vA.IsNontrivial := {
  exists_val_nontrivial := by
    rcases Valuation.IsNontrivial.exists_val_nontrivial
        (v := vR) with ⟨x, hx0, hx1⟩
    refine ⟨algebraMap R A x, ?_, ?_⟩
    · intro h
      have hm :
          vA (algebraMap R A x) =
            vA (algebraMap R A 0) := by
        simpa using h
      exact hx0 (by
        simpa using
          ((HasExtension.val_map_eq_iff vR vA x 0).1 hm))
    · intro h
      have hm :
          vA (algebraMap R A x) =
            vA (algebraMap R A 1) := by
        simpa using h
      exact hx1 (by
        simpa using
          ((HasExtension.val_map_eq_iff vR vA x 1).1 hm)) }

end Valuation

namespace LocalFieldTheory

noncomputable section

universe u v w

open scoped ValuativeRel

/-- A valued extension whose valuation integer ring in `L` is integral over the base integer ring.

This is the algebraic input used to restrict field norms to valuation integer rings. -/
class ValuativeExtension (K : Type u) (L : Type v) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L] : Prop where
  /-- Every target valuation integer is integral over the base valuation
  integers. -/
  integer_isIntegral : ∀ x : 𝒪[L], IsIntegral 𝒪[K] (x : L)

/-- An integral-closure identification of valuation rings makes the target valuation an extension of
the base valuation. -/
instance valuativeExtensionOfIsIntegralClosure
    (K : Type u) (L : Type v) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    ValuativeExtension K L where
  integer_isIntegral x :=
    (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).2 ⟨x, rfl⟩

/-- Integral-closure membership makes the intermediate valuation extend into
the given upper valuation, without replacing the upper field's topology. -/
theorem valuation_hasExtension_of_integralClosure_tower
    (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L]
    [ValuativeRel K] [ValuativeRel M] [ValuativeRel L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation M)]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[M] 𝒪[K] M] [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    (ValuativeRel.valuation M).HasExtension (ValuativeRel.valuation L) := by
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change algebraMap M L x ∈ 𝒪[L] ↔ x ∈ 𝒪[M]
  let f : M →ₐ[𝒪[K]] L := IsScalarTower.toAlgHom 𝒪[K] M L
  constructor
  · intro hx
    have hL : IsIntegral 𝒪[K] (f x) :=
      (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).2
        ⟨⟨algebraMap M L x, hx⟩, rfl⟩
    have hM : IsIntegral 𝒪[K] x := (isIntegral_algHom_iff f f.injective).mp hL
    obtain ⟨y, hy⟩ :=
      (IsIntegralClosure.isIntegral_iff (A := 𝒪[M]) (R := 𝒪[K]) (B := M)).1 hM
    exact hy ▸ y.property
  · intro hx
    have hM : IsIntegral 𝒪[K] x :=
      (IsIntegralClosure.isIntegral_iff (A := 𝒪[M]) (R := 𝒪[K]) (B := M)).2
        ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨y, hy⟩ :=
      (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).1
        (IsIntegral.map f hM)
    exact hy ▸ y.property

end
end LocalFieldTheory
