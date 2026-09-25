/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalReciprocityCharacterFixedField
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalUnramifiedArtinKummerRange

set_option autoImplicit false
/-!
# Unramified local reciprocity and the valuation line

The roots-of-unity-free reciprocity pairing sends the intrinsic unramified
character space onto the valuation line in the dual of actual power classes.
The proof evaluates finite Artin reciprocity in the character's own
unramified fixed field.
-/

open scoped Topology ValuativeRel

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP LocalClassFieldTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (n : ℕ+) [Fact ((n : ℕ).Prime)]

local instance localReciprocityUnramifiedTopology : TopologicalSpace (ZMod (n : ℕ)) := ⊥
local instance localReciprocityUnramifiedDiscreteTopology : DiscreteTopology (ZMod (n : ℕ)) :=
  discreteTopology_bot _
local instance localReciprocityUnramifiedH1Module
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod (n : ℕ)) (ContinuousH1ZMod (p := (n : ℕ)) (G := G)) :=
  continuousH1ZModModule

/-- Every unramified character evaluates through normalized valuation.
The scalar is the finite character's actual arithmetic Frobenius value. -/
theorem localReciprocityH1PowerClassPairing_mem_valuation_range
    (chi : ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup K))
    (hchi : chi ∈ localStandardUnramifiedH1 K n) :
    localReciprocityH1PowerClassPairing K (n : ℕ) chi ∈
      LinearMap.range (localPowerClassValuationDualEmbedding K (n : ℕ)) := by
  let E := localReciprocityCharacterField K (n : ℕ) chi
  let : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  let : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  let : Module.Finite 𝒪[K] 𝒪[E] := localCompleteDVF_integerRing_moduleFinite K E
  let : IsUnramifiedValuedExtension K E :=
    localIntermediateField_isUnramified_of_inertia_le K E
      (localReciprocityCharacterField_inertia_le K (n : ℕ) chi hchi)
  let psi : Gal(E / K) →* Multiplicative (ZMod (n : ℕ)) :=
    localReciprocityFiniteCharacter K (n : ℕ) chi
  let c : ZMod (n : ℕ) := (psi (arithmeticFrobeniusOfUnramifiedValuation K E)).toAdd
  have hformula (a : Kˣ) :
      localReciprocityH1PowerClassPairing K (n : ℕ) chi
          (Additive.ofMul (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a)) =
        c * (valuationMap K (Additive.ofMul a) : ZMod (n : ℕ)) := by
    calc
      _ = (psi (abelianLocalArtinMap K E a)).toAdd :=
        (localReciprocityFiniteCharacter_artin K (n : ℕ) chi a).symm
      _ = _ := by
        rw [show abelianLocalArtinMap K E a = abelianLocalArtinMonoidHom K E a from
          DFunLike.congr_fun (abelianLocalArtinMap_toMonoidHom K E) a]
        rw [abelianLocalArtinMonoidHom_eq_frobenius_zpow K E, map_zpow]
        rw [toAdd_zpow, zsmul_eq_mul]
        exact mul_comm _ _
  refine ⟨c, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range x.toMul
  let qa : absolutePowerClassModP K (n : ℕ) :=
    Additive.ofMul
      (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a)
  have hqa : x = qa := congrArg Additive.ofMul ha.symm
  rw [hqa]
  change
    (localPowerClassValuationDualEmbedding K (n : ℕ) c) qa =
      (localReciprocityH1PowerClassPairing K (n : ℕ) chi) qa
  rw [localPowerClassValuationDualEmbedding_apply]
  change c * (valuationMap K (Additive.ofMul a) : ZMod (n : ℕ)) = _
  exact (hformula a).symm

/-- Evaluation on the normalized inverse uniformizer.  For an unramified
character this is its arithmetic Frobenius coordinate. -/
noncomputable def localReciprocityPrimeScalar
    (chi : ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup K)) :
    ZMod (n : ℕ) :=
  localReciprocityH1PowerClassPairing K (n : ℕ) chi
    (Additive.ofMul (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range
      (inverseIntegerRingUniformizerFieldUnit K)))

/-- The unramified reciprocity functional is its normalized Frobenius
coordinate times valuation modulo the coefficient prime. -/
theorem localReciprocityH1PowerClassPairing_eq_primeScalar_valuation
    (chi : ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup K))
    (hchi : chi ∈ localStandardUnramifiedH1 K n) :
    localReciprocityH1PowerClassPairing K (n : ℕ) chi =
      localPowerClassValuationDualEmbedding K (n : ℕ)
        (localReciprocityPrimeScalar K n chi) := by
  obtain ⟨c, hc⟩ := localReciprocityH1PowerClassPairing_mem_valuation_range K n chi hchi
  let qπ : absolutePowerClassModP K (n : ℕ) :=
    Additive.ofMul
      (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range
        (inverseIntegerRingUniformizerFieldUnit K))
  have hval : localPowerClassValuation K (n : ℕ)
      qπ = 1 := by
    dsimp only [qπ]
    rw [localPowerClassValuation_mk, valuationMap_apply,
      v_inverseIntegerRingUniformizerFieldUnit]
    exact Int.cast_one
  have hscalar : localReciprocityPrimeScalar K n chi = c := by
    change
      (localReciprocityH1PowerClassPairing K (n : ℕ) chi) qπ = c
    rw [← hc, localPowerClassValuationDualEmbedding_apply, hval, mul_one]
  rw [hscalar]
  exact hc.symm

/-- The unramified character space corresponds exactly to the valuation
line under local reciprocity, without a roots-of-unity hypothesis. -/
theorem localReciprocityH1PowerClassPairing_unramified_range :
    LinearMap.range
      ((localReciprocityH1PowerClassPairing K (n : ℕ)).comp
        (localStandardUnramifiedH1 K n).subtype) =
      LinearMap.range (localPowerClassValuationDualEmbedding K (n : ℕ)) := by
  apply le_antisymm
  · rintro phi ⟨chi, rfl⟩
    exact localReciprocityH1PowerClassPairing_mem_valuation_range K n chi.1 chi.property
  · obtain ⟨chi, hchi, hchi0⟩ := localStandardUnramifiedH1_exists_ne_zero K n
    obtain ⟨c, hc⟩ := localReciprocityH1PowerClassPairing_mem_valuation_range K n chi hchi
    have hc0 : c ≠ 0 := by
      intro hzero
      apply hchi0
      apply localReciprocityH1PowerClassPairing_injective K (n : ℕ)
      rw [← hc, hzero, map_zero, map_zero]
    rintro phi ⟨b, rfl⟩
    refine ⟨⟨(b / c) • chi, (localStandardUnramifiedH1 K n).smul_mem _ hchi⟩, ?_⟩
    change localReciprocityH1PowerClassPairing K (n : ℕ) ((b / c) • chi) =
      localPowerClassValuationDualEmbedding K (n : ℕ) b
    rw [map_smul, ← hc, ← map_smul]
    congr 1
    exact div_mul_cancel₀ b hc0

end ClassFieldTower.Martinet.Shafarevich
