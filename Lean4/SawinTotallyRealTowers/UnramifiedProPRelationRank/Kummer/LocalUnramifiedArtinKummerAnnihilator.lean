/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalUnramifiedArtinKummerRange

set_option autoImplicit false
/-!
# The annihilator of intrinsic unramified local H¹

The actual Artin--Kummer pairing, restricted to unramified classes in its
first argument, vanishes on precisely the valuation-zero Kummer classes.
This is the local kernel statement needed to assemble the empty-support
unramified local-to-global dual map.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP KummerTheory LocalClassFieldTheory

variable (K : Type) [Field K] [CharZero K]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (n : ℕ+) [Fact ((n : ℕ).Prime)]

local instance localUnramifiedArtinKummerAnnihilatorTopology :
    TopologicalSpace (ZMod (n : ℕ)) := ⊥
local instance localUnramifiedArtinKummerAnnihilatorDiscreteTopology :
    DiscreteTopology (ZMod (n : ℕ)) := discreteTopology_bot _
local instance localUnramifiedArtinKummerAnnihilatorModule
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod (n : ℕ)) (ContinuousH1ZMod (p := (n : ℕ)) (G := G)) :=
  continuousH1ZModModule

/-- Pair a local class against intrinsic unramified `H¹` using the actual
local Artin--Kummer pairing. -/
noncomputable def localArtinKummerUnramifiedDualRestriction
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup K) →ₗ[ZMod (n : ℕ)]
      Module.Dual (ZMod (n : ℕ)) (localStandardUnramifiedH1 K n) :=
  (localStandardUnramifiedH1 K n).subtype.dualMap.comp
    (localArtinKummerH1DualEmbedding K n hmu).flip

@[simp]
theorem localArtinKummerUnramifiedDualRestriction_apply
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (chi : ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup K))
    (u : localStandardUnramifiedH1 K n) :
    localArtinKummerUnramifiedDualRestriction K n hmu chi u =
      localArtinKummerH1DualEmbedding K n hmu u.1 chi := rfl

/-- Annihilating every unramified local class is equivalent to having
zero Kummer valuation. -/
theorem localArtinKummerUnramifiedDualRestriction_eq_zero_iff
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (chi : ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup K)) :
    localArtinKummerUnramifiedDualRestriction K n hmu chi = 0 ↔
      localStandardH1Valuation K n hmu chi = 0 := by
  constructor
  · intro hzero
    have hm : localStandardH1ValuationDualEmbedding K n hmu 1 ∈
        LinearMap.range ((localArtinKummerH1DualEmbedding K n hmu).comp
          (localStandardUnramifiedH1 K n).subtype) := by
      rw [localArtinKummerH1DualEmbedding_unramified_range]
      exact ⟨1, rfl⟩
    obtain ⟨u, hu⟩ := hm
    have heq := LinearMap.congr_fun hu chi
    have hz := LinearMap.congr_fun hzero u
    change localArtinKummerH1DualEmbedding K n hmu u.1 chi =
      localStandardH1ValuationDualEmbedding K n hmu 1 chi at heq
    change localArtinKummerH1DualEmbedding K n hmu u.1 chi = 0 at hz
    rw [heq, localStandardH1ValuationDualEmbedding_apply, one_mul] at hz
    exact hz
  · intro hzero
    apply LinearMap.ext
    intro u
    obtain ⟨c, hc⟩ := localArtinKummerH1DualEmbedding_mem_valuation_range
      K n hmu u.1 u.property
    have heq := LinearMap.congr_fun hc chi
    change localArtinKummerH1DualEmbedding K n hmu u.1 chi = 0
    rw [← heq, localStandardH1ValuationDualEmbedding_apply, hzero, mul_zero]

/-- The unramified Artin--Kummer annihilator is the valuation-zero subspace. -/
theorem localArtinKummerUnramifiedDualRestriction_ker
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    LinearMap.ker (localArtinKummerUnramifiedDualRestriction K n hmu) =
      LinearMap.ker (localStandardH1Valuation K n hmu) := by
  ext chi
  exact localArtinKummerUnramifiedDualRestriction_eq_zero_iff K n hmu chi

/-- Under Kummer theory, the local unramified annihilator condition is
exactly zero normalized valuation on power classes. -/
theorem localArtinKummerUnramifiedDualRestriction_kummer_eq_zero_iff
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (x : absolutePowerClassModP K (n : ℕ)) :
    localArtinKummerUnramifiedDualRestriction K n hmu
        (absoluteKummerContinuousH1LinearEquiv K (n : ℕ) hmu x) = 0 ↔
      localPowerClassValuation K (n : ℕ) x = 0 := by
  rw [localArtinKummerUnramifiedDualRestriction_eq_zero_iff]
  simp only [localStandardH1Valuation, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

end ClassFieldTower.Martinet.Shafarevich
