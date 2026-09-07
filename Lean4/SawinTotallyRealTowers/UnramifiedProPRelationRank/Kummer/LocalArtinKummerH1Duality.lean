import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPKummerComparison
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalHilbertKummerDual

set_option autoImplicit false
/-!
# Local Artin--Kummer duality on continuous H¹

The maximal local Kummer extension and the local Artin map give the local
Hilbert pairing on power classes.  This file transports that pairing across
the absolute Kummer equivalence to continuous additive `ZMod p` characters.

This is an Artin--Kummer duality statement.  It does not identify the pairing
with a cup product followed by a local invariant map.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory LocalClassFieldTheory LocalClassFieldTheory.Kummer
open ClassFieldTower.ProP

variable (L : Type) [Field L] [CharZero L]
variable [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
variable (n : ℕ+) [Fact ((n : ℕ).Prime)]

local instance localArtinKummerH1Topology : TopologicalSpace (ZMod (n : ℕ)) := ⊥

local instance localArtinKummerH1DiscreteTopology : DiscreteTopology (ZMod (n : ℕ)) :=
  discreteTopology_bot _

local instance localArtinKummerH1Module
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod (n : ℕ)) (ContinuousH1ZMod (p := (n : ℕ)) (G := G)) :=
  continuousH1ZModModule

/-- The maximal-local-Artin Kummer pairing, transported to continuous `H¹`
in both variables. -/
noncomputable def localArtinKummerH1DualEmbedding
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty) :
    ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup L) →ₗ[ZMod (n : ℕ)]
      Module.Dual (ZMod (n : ℕ))
        (ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup L)) := by
  let e := absoluteKummerContinuousH1LinearEquiv L (n : ℕ) hmu
  exact
    (e.symm.toLinearMap.dualMap.comp
      (localHilbertDualEmbedding L n hmu)).comp e.symm.toLinearMap

@[simp]
theorem localArtinKummerH1DualEmbedding_apply
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty)
    (chi psi : ContinuousH1ZMod
      (p := (n : ℕ)) (G := Field.absoluteGaloisGroup L)) :
    localArtinKummerH1DualEmbedding L n hmu chi psi =
      localHilbertDualEmbedding L n hmu
        ((absoluteKummerContinuousH1LinearEquiv L (n : ℕ) hmu).symm chi)
        ((absoluteKummerContinuousH1LinearEquiv L (n : ℕ) hmu).symm psi) :=
  rfl

/-- On Kummer classes, the transported pairing is the original local
Hilbert pairing on power classes. -/
@[simp]
theorem localArtinKummerH1DualEmbedding_kummer
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty)
    (a b : absolutePowerClassModP L (n : ℕ)) :
    localArtinKummerH1DualEmbedding L n hmu
        (absoluteKummerContinuousH1LinearEquiv L (n : ℕ) hmu a)
        (absoluteKummerContinuousH1LinearEquiv L (n : ℕ) hmu b) =
      localHilbertDualEmbedding L n hmu a b := by
  rw [localArtinKummerH1DualEmbedding_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- Representative formula: the Artin--Kummer `H¹` pairing is the local
Hilbert symbol, written additively using the chosen primitive root. -/
@[simp]
theorem localArtinKummerH1DualEmbedding_mk
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty) (a b : Lˣ) :
    localArtinKummerH1DualEmbedding L n hmu
        (absoluteKummerContinuousH1LinearEquiv L (n : ℕ) hmu
          (Additive.ofMul
            (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range a)))
        (absoluteKummerContinuousH1LinearEquiv L (n : ℕ) hmu
          (Additive.ofMul
            (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range b))) =
      ((localNthRootsEquivMultiplicativeZMod L n hmu)
        (localHilbertSymbol L n
          (Nat.cast_ne_zero.mpr n.ne_zero) hmu a b)).toAdd := by
  let qa : absolutePowerClassModP L (n : ℕ) :=
    Additive.ofMul
      (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range a)
  let qb : absolutePowerClassModP L (n : ℕ) :=
    Additive.ofMul
      (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range b)
  have hk := localArtinKummerH1DualEmbedding_kummer
    (L := L) (n := n) hmu qa qb
  have hd := localHilbertDualEmbedding_apply
    (L := L) (n := n) hmu qa qb
  change localArtinKummerH1DualEmbedding L n hmu
      (absoluteKummerContinuousH1LinearEquiv L (n : ℕ) hmu qa)
      (absoluteKummerContinuousH1LinearEquiv L (n : ℕ) hmu qb) = _
  rw [hk, hd]
  change
    ((localNthRootsEquivMultiplicativeZMod L n hmu)
      (localHilbertPairing L n
        (Nat.cast_ne_zero.mpr n.ne_zero) hmu
        (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range a)
        (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range b))).toAdd = _
  rw [localHilbertPairing_apply]

/-- Nondegeneracy of the local Hilbert pairing makes the transported
Artin--Kummer map injective. -/
theorem localArtinKummerH1DualEmbedding_injective
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty) :
    Function.Injective (localArtinKummerH1DualEmbedding L n hmu) := by
  let e := absoluteKummerContinuousH1LinearEquiv L (n : ℕ) hmu
  intro chi psi h
  have h' :
      localHilbertDualEmbedding L n hmu (e.symm chi) =
        localHilbertDualEmbedding L n hmu (e.symm psi) := by
    apply LinearMap.dualMap_injective_of_surjective e.symm.surjective
    exact h
  exact e.symm.injective (localHilbertDualEmbedding_injective L n hmu h')

end ClassFieldTower.Martinet.Shafarevich
