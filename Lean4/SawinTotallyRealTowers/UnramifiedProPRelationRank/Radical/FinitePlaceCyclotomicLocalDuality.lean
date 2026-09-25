/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceCyclotomicKummerH1
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalArtinKummerH1Duality

set_option autoImplicit false
/-!
# Artin--Kummer local duality at cyclotomic finite places

This file specializes the local Artin--Kummer `H¹` pairing to completions of
the cyclotomic base used in the ideal-radical construction.  The representative
formula is also stated for the natural `mu_p` Kummer class after the coefficient
trivialization comparison.
-/

open NumberField IsDedekindDomain
open scoped NumberField Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP KummerTheory

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ+) [Fact ((p : ℕ).Prime)]

local instance finitePlaceCyclotomicLocalDualityFiniteDimensional :
    FiniteDimensional F (FinitePlaceCyclotomicBase F (p : ℕ)) :=
  finiteDimensional_idealRadicalCyclotomicBase
    F (p : ℕ) (Fact.out : (p : ℕ).Prime)

local instance finitePlaceCyclotomicLocalDualityNumberField :
    NumberField (FinitePlaceCyclotomicBase F (p : ℕ)) :=
  NumberField.of_module_finite F (FinitePlaceCyclotomicBase F (p : ℕ))

local instance finitePlaceCyclotomicLocalDualityValuativeRel
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers
        (FinitePlaceCyclotomicBase F (p : ℕ)))) :
    ValuativeRel
      (v.adicCompletion (FinitePlaceCyclotomicBase F (p : ℕ))) :=
  finitePlaceAdicCompletionValuativeRel
    (FinitePlaceCyclotomicBase F (p : ℕ)) v

local instance finitePlaceCyclotomicLocalDualityIsNonarchimedeanLocalField
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers
        (FinitePlaceCyclotomicBase F (p : ℕ)))) :
    IsNonarchimedeanLocalField
      (v.adicCompletion (FinitePlaceCyclotomicBase F (p : ℕ))) :=
  finitePlaceAdicCompletionIsNonarchimedeanLocalField
    (FinitePlaceCyclotomicBase F (p : ℕ)) v

local instance finitePlaceCyclotomicLocalDualityH1Topology :
    TopologicalSpace (ZMod (p : ℕ)) := ⊥

local instance finitePlaceCyclotomicLocalDualityH1DiscreteTopology :
    DiscreteTopology (ZMod (p : ℕ)) :=
  discreteTopology_bot _

local instance finitePlaceCyclotomicLocalDualityH1Module
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod (p : ℕ))
      (ContinuousH1ZMod (p := (p : ℕ)) (G := G)) :=
  continuousH1ZModModule

/-- The local Artin--Kummer pairing on continuous `H¹` of a cyclotomic
finite-place completion. -/
noncomputable def finitePlaceCyclotomicArtinKummerH1DualEmbedding
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers
        (FinitePlaceCyclotomicBase F (p : ℕ)))) :
    ContinuousH1ZMod
        (p := (p : ℕ))
        (G := Field.absoluteGaloisGroup
          (v.adicCompletion (FinitePlaceCyclotomicBase F (p : ℕ)))) →ₗ[ZMod (p : ℕ)]
      Module.Dual (ZMod (p : ℕ))
        (ContinuousH1ZMod
          (p := (p : ℕ))
          (G := Field.absoluteGaloisGroup
            (v.adicCompletion (FinitePlaceCyclotomicBase F (p : ℕ))))) := by
  exact localArtinKummerH1DualEmbedding
    (v.adicCompletion (FinitePlaceCyclotomicBase F (p : ℕ))) p
    (finitePlaceCyclotomicCompletion_primitiveRoots_nonempty F (p : ℕ) v)

/-- On local Kummer classes, the specialized pairing is the original local
Hilbert pairing on completion power classes. -/
@[simp]
theorem finitePlaceCyclotomicArtinKummerH1DualEmbedding_kummer
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers
        (FinitePlaceCyclotomicBase F (p : ℕ))))
    (x y : FinitePlaceLocalPowerClassModP
      (FinitePlaceCyclotomicBase F (p : ℕ)) (p : ℕ) v) :
    finitePlaceCyclotomicArtinKummerH1DualEmbedding F p v
        (absoluteKummerContinuousH1LinearEquiv
          (v.adicCompletion (FinitePlaceCyclotomicBase F (p : ℕ)))
          (p : ℕ)
          (finitePlaceCyclotomicCompletion_primitiveRoots_nonempty
            F (p : ℕ) v) x)
        (absoluteKummerContinuousH1LinearEquiv
          (v.adicCompletion (FinitePlaceCyclotomicBase F (p : ℕ)))
          (p : ℕ)
          (finitePlaceCyclotomicCompletion_primitiveRoots_nonempty
            F (p : ℕ) v) y) =
      localHilbertDualEmbedding
        (v.adicCompletion (FinitePlaceCyclotomicBase F (p : ℕ))) p
        (finitePlaceCyclotomicCompletion_primitiveRoots_nonempty
          F (p : ℕ) v) x y := by
  exact localArtinKummerH1DualEmbedding_kummer
    (v.adicCompletion (FinitePlaceCyclotomicBase F (p : ℕ))) p
    (finitePlaceCyclotomicCompletion_primitiveRoots_nonempty F (p : ℕ) v) x y

/-- After the C03 coefficient trivialization, natural `mu_p` Kummer classes
pair by the usual local Hilbert symbol on representatives. -/
@[simp]
theorem finitePlaceCyclotomicArtinKummerH1DualEmbedding_muPKummerClass
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers
        (FinitePlaceCyclotomicBase F (p : ℕ))))
    (a b : (v.adicCompletion
      (FinitePlaceCyclotomicBase F (p : ℕ)))ˣ) :
    let L := v.adicCompletion (FinitePlaceCyclotomicBase F (p : ℕ))
    let hmu := finitePlaceCyclotomicCompletion_primitiveRoots_nonempty
      F (p : ℕ) v
    finitePlaceCyclotomicArtinKummerH1DualEmbedding F p v
        (absoluteMuPH1EquivContinuousH1ZMod L (p : ℕ) hmu
          (absoluteKummerMuPH1Class L (p : ℕ) a))
        (absoluteMuPH1EquivContinuousH1ZMod L (p : ℕ) hmu
          (absoluteKummerMuPH1Class L (p : ℕ) b)) =
      ((localNthRootsEquivMultiplicativeZMod L p hmu)
        (LocalClassFieldTheory.Kummer.localHilbertSymbol L p
          (Nat.cast_ne_zero.mpr p.ne_zero) hmu a b)).toAdd := by
  dsimp only
  rw [absoluteMuPH1EquivContinuousH1ZMod_kummerClass,
    absoluteMuPH1EquivContinuousH1ZMod_kummerClass]
  exact localArtinKummerH1DualEmbedding_mk
    (v.adicCompletion (FinitePlaceCyclotomicBase F (p : ℕ))) p
    (finitePlaceCyclotomicCompletion_primitiveRoots_nonempty F (p : ℕ) v) a b

/-- The specialized finite-place Artin--Kummer dual embedding is injective. -/
theorem finitePlaceCyclotomicArtinKummerH1DualEmbedding_injective
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers
        (FinitePlaceCyclotomicBase F (p : ℕ)))) :
    Function.Injective
      (finitePlaceCyclotomicArtinKummerH1DualEmbedding F p v) := by
  exact localArtinKummerH1DualEmbedding_injective
    (v.adicCompletion (FinitePlaceCyclotomicBase F (p : ℕ))) p
    (finitePlaceCyclotomicCompletion_primitiveRoots_nonempty F (p : ℕ) v)

end ClassFieldTower.Martinet.Shafarevich
