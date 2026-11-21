/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Main
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology

/-!
# Finite local reciprocity

The local class-field-axiom theorem on finite extensions of a local field.

Mathlib's local-field predicate is topology-first, while the local class-field-axiom theorem also
needs a compatible local-field structure on the finite extension.  This file
constructs that structure from the spectral norm.  In particular, the target
valuation ring is proved integral over the base valuation ring; no local-field
structure on the target is assumed.
-/

@[expose] public section

namespace LocalClassFieldTheory

open LocalFieldTheory

open ValuationTheory

open CyclicCohomology IntegralGroupCohomology.Universe



noncomputable section

open scoped NNReal ValuativeRel

universe u v

/-- The arithmetic finiteness, cardinality and vanishing results for the actual
integral Tate groups of field units. -/
structure UnitsTateCardinalityData
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Prop where
  /-- Finiteness of the degree-zero integral Tate group. -/
  finiteH0 : Finite (tate (Rep.ofAlgebraAutOnUnits K L) 0)
  /-- The degree-zero integral Tate group has order equal to the extension degree. -/
  cardH0 : Nat.card (tate (Rep.ofAlgebraAutOnUnits K L) 0) = Module.finrank K L
  /-- The degree-minus-one integral Tate object vanishes. -/
  isZeroHminusOne : CategoryTheory.Limits.IsZero (tate (Rep.ofAlgebraAutOnUnits K L) (-1))

namespace UnitsTateCardinalityData

section Integral

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Finiteness follows from vanishing of the same degree-minus-one integral group. -/
theorem finiteHminusOne (h : UnitsTateCardinalityData K L) :
    Finite (tate (Rep.ofAlgebraAutOnUnits K L) (-1)) := by
  let : Subsingleton (tate (Rep.ofAlgebraAutOnUnits K L) (-1)) :=
    ModuleCat.subsingleton_of_isZero h.isZeroHminusOne
  infer_instance

/-- Vanishing gives order one for the same degree-minus-one integral group. -/
theorem cardHminusOne (h : UnitsTateCardinalityData K L) :
    Nat.card (tate (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1 := by
  let : Subsingleton (tate (Rep.ofAlgebraAutOnUnits K L) (-1)) :=
    ModuleCat.subsingleton_of_isZero h.isZeroHminusOne
  exact Nat.card_unique

end Integral

section Original

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The original degree-zero Tate group is finite in universe zero. -/
theorem finiteH0_original (h : UnitsTateCardinalityData K L) :
    Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) :=
  (finite_tate_iff_original (Rep.ofAlgebraAutOnUnits K L) 0).mp h.finiteH0

/-- The original degree-zero Tate group has order equal to the extension degree. -/
theorem cardH0_original (h : UnitsTateCardinalityData K L) :
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) = Module.finrank K L :=
  (card_tate_eq_original (Rep.ofAlgebraAutOnUnits K L) 0).symm.trans h.cardH0

/-- The original degree-minus-one Tate group is finite in universe zero. -/
theorem finiteHminusOne_original (h : UnitsTateCardinalityData K L) :
    Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) :=
  (finite_tate_iff_original (Rep.ofAlgebraAutOnUnits K L) (-1)).mp h.finiteHminusOne

/-- The original degree-minus-one Tate group has order one. -/
theorem cardHminusOne_original (h : UnitsTateCardinalityData K L) :
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1 :=
  (card_tate_eq_original (Rep.ofAlgebraAutOnUnits K L) (-1)).symm.trans h.cardHminusOne

end Original

end UnitsTateCardinalityData

/-- The local class-field-axiom theorem for an arbitrary finite Galois extension of a
nonarchimedean local field.  All local-field data on the extension is
constructed from the spectral norm. -/
theorem finiteExtensionUnits_tate_card_of_generator
    (K L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (g : Gal(L/K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    UnitsTateCardinalityData K L := by
  let : NontriviallyNormedField L := finiteExtensionSpectralNormedField K L
  let : ValuativeRel L := finiteExtensionSpectralValuativeRel K L
  let : IsNonarchimedeanLocalField L := finiteExtensionSpectralIsNonarchimedeanLocalField K L
  let : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
    finiteExtensionSpectralValuation_hasExtension K L
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L := localCompleteDVF_integerRing_isIntegralClosure K L
  let : Module.Finite 𝒪[K] 𝒪[L] := localCompleteDVF_integerRing_moduleFinite K L
  let M := Rep.ofAlgebraAutOnUnits K L
  have hcard := localFieldUnits_integralTate_card_of_generator K L g hg
  refine ⟨Nat.finite_of_card_ne_zero (hcard.1.trans_ne Module.finrank_pos.ne'), hcard.1, ?_⟩
  let : Subsingleton (tate M (-1)) := (Nat.card_eq_one_iff_unique.mp hcard.2).1
  exact ModuleCat.isZero_of_subsingleton _

/-- Tower form of the local class-field-axiom theorem.  It is enough that the lower field of the
cyclic extension be finite over a nonarchimedean local field; its local-field
structure is again supplied by the spectral norm. -/
theorem finiteTowerUnits_tate_card_of_generator
    (k : Type u) (K L : Type v) [Field k] [Field K] [Field L]
    [Algebra k K] [FiniteDimensional k K]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (g : Gal(L/K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    UnitsTateCardinalityData K L := by
  let : NontriviallyNormedField K := finiteExtensionSpectralNormedField k K
  let : ValuativeRel K := finiteExtensionSpectralValuativeRel k K
  let : IsNonarchimedeanLocalField K := finiteExtensionSpectralIsNonarchimedeanLocalField k K
  exact finiteExtensionUnits_tate_card_of_generator K L g hg

end
end LocalClassFieldTheory
