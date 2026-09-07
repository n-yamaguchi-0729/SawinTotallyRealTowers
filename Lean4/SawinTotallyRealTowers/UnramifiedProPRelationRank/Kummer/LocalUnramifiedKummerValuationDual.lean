import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalUnramifiedKummerHilbertValuation
import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup

set_option autoImplicit false
/-!
# The valuation dual of an unramified Kummer class

Unramified Hilbert characters are scalar multiples of reduced normalized
valuation. Nondegeneracy shows that the Frobenius scalar of a nonzero class
is nonzero, including at places above the Kummer exponent.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory LocalClassFieldTheory LocalClassFieldTheory.Kummer
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type) [Field K]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Valuation

variable (p : ℕ) [Fact p.Prime]

/-- Reduced normalized valuation on local power classes. -/
noncomputable def localPowerClassValuationMonoidHom :
    (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) →* Multiplicative (ZMod p) :=
  QuotientGroup.lift (powMonoidHom p : Kˣ →* Kˣ).range
    (valuationModDegreeMulHom K p) (by
      rintro _ ⟨x, rfl⟩
      rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow]
      apply Multiplicative.ofAdd.injective
      change p • (valuationModDegreeMulHom K p x).toAdd = 0
      simp)

/-- The reduced local valuation as a linear functional. -/
noncomputable def localPowerClassValuation :
    absolutePowerClassModP K p →ₗ[ZMod p] ZMod p := by
  letI : Module (ZMod p)
      (Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range)) :=
    additiveZModModuleOfPowEqOne p (absolutePowerClassQuotient_pow_eq_one K p)
  exact (localPowerClassValuationMonoidHom K p).toAdditiveLeft.toZModLinearMap p

@[simp]
theorem localPowerClassValuation_mk (a : Kˣ) :
    localPowerClassValuation K p
        (Additive.ofMul (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a)) =
      (valuationMap K (Additive.ofMul a) : ZMod p) := rfl

/-- Local valuation on power classes is onto. -/
theorem localPowerClassValuation_surjective :
    Function.Surjective (localPowerClassValuation K p) := by
  intro a
  obtain ⟨x, hx⟩ := valuationModDegree_surjective K p a
  refine ⟨Additive.ofMul
    (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range x.toMul), ?_⟩
  exact hx

/-- The one-dimensional valuation line in the dual of local power classes. -/
noncomputable def localPowerClassValuationDualEmbedding :
    ZMod p →ₗ[ZMod p] Module.Dual (ZMod p) (absolutePowerClassModP K p) :=
  (localPowerClassValuation K p).dualMap.comp (LinearMap.lsmul (ZMod p) (ZMod p))

@[simp]
theorem localPowerClassValuationDualEmbedding_apply
    (a : ZMod p) (x : absolutePowerClassModP K p) :
    localPowerClassValuationDualEmbedding K p a x =
      a * localPowerClassValuation K p x := rfl

/-- The valuation line is faithfully parametrized by `ZMod p`. -/
theorem localPowerClassValuationDualEmbedding_injective :
    Function.Injective (localPowerClassValuationDualEmbedding K p) := by
  intro a b h
  obtain ⟨x, hx⟩ := localPowerClassValuation_surjective K p 1
  have hv := LinearMap.congr_fun h x
  simpa only [localPowerClassValuationDualEmbedding_apply, hx, mul_one] using hv

end Valuation

variable [CharZero K]
variable (n : ℕ+) [Fact ((n : ℕ).Prime)]

/-- The scalar of an unramified Kummer Hilbert character in the normalized
valuation coordinate. -/
noncomputable def unramifiedChosenSimpleKummerFrobeniusScalar
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ)
    (ha : IsUnramifiedChosenSimpleKummer K n (Nat.cast_ne_zero.mpr n.ne_zero) a) :
    ZMod (n : ℕ) :=
  -((localNthRootsEquivMultiplicativeZMod K n hmu)
    (unramifiedChosenSimpleKummerFrobeniusRoot K n
      (Nat.cast_ne_zero.mpr n.ne_zero) hmu a ha)).toAdd

/-- The Hilbert dual functional of an unramified Kummer radical is its
Frobenius scalar times the reduced valuation. -/
theorem localHilbertDualEmbedding_mk_unramified
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ)
    (ha : IsUnramifiedChosenSimpleKummer K n (Nat.cast_ne_zero.mpr n.ne_zero) a) :
    localHilbertDualEmbedding K n hmu
        (Additive.ofMul
          (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a)) =
      localPowerClassValuationDualEmbedding K (n : ℕ)
        (unramifiedChosenSimpleKummerFrobeniusScalar K n hmu a ha) := by
  apply LinearMap.ext
  intro x
  let q : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := x.toMul
  change localHilbertDualEmbedding K n hmu
      (Additive.ofMul
        (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a))
      (Additive.ofMul q) =
    localPowerClassValuationDualEmbedding K (n : ℕ)
      (unramifiedChosenSimpleKummerFrobeniusScalar K n hmu a ha) (Additive.ofMul q)
  refine QuotientGroup.induction_on q ?_
  intro b
  change ((localNthRootsEquivMultiplicativeZMod K n hmu)
    (localHilbertPairing K n (Nat.cast_ne_zero.mpr n.ne_zero) hmu
      (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a)
      (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range b))).toAdd =
    unramifiedChosenSimpleKummerFrobeniusScalar K n hmu a ha *
      (valuationMap K (Additive.ofMul b) : ZMod (n : ℕ))
  rw [localHilbertPairing_apply, localHilbertSymbol_eq_unramifiedFrobenius_zpow
    K n (Nat.cast_ne_zero.mpr n.ne_zero) hmu a b ha, map_zpow,
    toAdd_zpow]
  simp only [unramifiedChosenSimpleKummerFrobeniusScalar, zsmul_eq_mul,
    Int.cast_neg, neg_mul, mul_neg, mul_comm]

/-- A nonzero unramified Kummer class has a nonzero Frobenius scalar. -/
theorem unramifiedChosenSimpleKummerFrobeniusScalar_ne_zero
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ)
    (ha : IsUnramifiedChosenSimpleKummer K n (Nat.cast_ne_zero.mpr n.ne_zero) a)
    (ha0 : QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a ≠ 1) :
    unramifiedChosenSimpleKummerFrobeniusScalar K n hmu a ha ≠ 0 := by
  intro hzero
  apply ha0
  have hclass := localHilbertDualEmbedding_mk_unramified K n hmu a ha
  rw [hzero, map_zero] at hclass
  have hclass0 := localHilbertDualEmbedding_injective K n hmu
    (hclass.trans (map_zero (localHilbertDualEmbedding K n hmu)).symm)
  exact congrArg (fun x : absolutePowerClassModP K (n : ℕ) ↦
    (show Additive (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) from x).toMul) hclass0

end ClassFieldTower.Martinet.Shafarevich
