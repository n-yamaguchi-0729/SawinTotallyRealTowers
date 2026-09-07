import GaloisCohomology.Kummer.Concrete.InfiniteCharacterEquiv
import GaloisCohomology.Kummer.Concrete.FiniteDualSeparation
import ValuedFieldTheory.LocalField.GroupTheory.PowerIndex
import Mathlib.FieldTheory.AbsoluteGaloisGroup

set_option autoImplicit false
/-!
# Absolute Kummer characters

For a field containing a primitive `n`-th root of unity, this file identifies
`K× / K×ⁿ` with continuous characters of the absolute Galois group.  The
target is first the discrete group of `n`-th roots of unity and is then
identified with the discrete multiplicative group underlying `ZMod n`.
-/

open scoped Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type*) [Field K]

private abbrev AbsoluteRadicalDatum (n : ℕ+) :=
  chosenFiniteKummerRadicalDatum (K := K) (L := AlgebraicClosure K) n

/-- Every base-field unit has an `n`-th root in the algebraic closure. -/
theorem finiteKummerRadicalSubgroup_algebraicClosure_eq_top (n : ℕ+) :
    finiteKummerRadicalSubgroup (K := K) (L := AlgebraicClosure K) n = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) (a : K)) n.pos
  have hβ_ne : β ≠ 0 := by
    intro hzero
    have hmap_zero : algebraMap K (AlgebraicClosure K) (a : K) = 0 := by
      rw [← hβ, hzero, zero_pow n.ne_zero]
    exact a.ne_zero ((algebraMap K (AlgebraicClosure K)).injective
      (hmap_zero.trans (map_zero (algebraMap K (AlgebraicClosure K))).symm))
  refine ⟨Units.mk0 β hβ_ne, ?_⟩
  apply Units.ext
  exact hβ

/-- The full unit group is multiplicatively equivalent to the actual radical
subgroup in the algebraic closure. -/
noncomputable def unitsEquivAbsoluteRadicalCarrier (n : ℕ+) :
    Kˣ ≃* (AbsoluteRadicalDatum K n).carrier :=
  Subgroup.topEquiv.symm.trans
    (MulEquiv.subgroupCongr
      (finiteKummerRadicalSubgroup_algebraicClosure_eq_top K n).symm)

private theorem map_powerRange_unitsEquivAbsoluteRadicalCarrier (n : ℕ+) :
    (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range.map
        (unitsEquivAbsoluteRadicalCarrier K n).toMonoidHom =
      (AbsoluteRadicalDatum K n).ambientNthPowersSubgroup := by
  ext a
  constructor
  · rintro ⟨x, ⟨b, rfl⟩, rfl⟩
    exact (AbsoluteRadicalDatum K n).mem_ambientNthPowersSubgroup_iff.mpr
      ⟨b, rfl⟩
  · intro ha
    obtain ⟨b, hb⟩ :=
      (AbsoluteRadicalDatum K n).mem_ambientNthPowersSubgroup_iff.mp ha
    let x : Kˣ := a.1
    have hx : x = b ^ (n : ℕ) := hb.symm
    refine ⟨x, ⟨b, hx.symm⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- The ordinary power-class group is canonically the radical quotient used
by the infinite Kummer character theorem over the algebraic closure. -/
noncomputable def absolutePowerClassEquivRadicalQuotient (n : ℕ+) :
    Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range ≃*
      (AbsoluteRadicalDatum K n).RadicalQuotient :=
  (QuotientGroup.congr
      (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range
      (AbsoluteRadicalDatum K n).ambientNthPowersSubgroup
      (unitsEquivAbsoluteRadicalCarrier K n)
      (map_powerRange_unitsEquivAbsoluteRadicalCarrier K n)).trans
    (AbsoluteRadicalDatum K n).radicalQuotientMulEquiv.symm

/-- Absolute Kummer theory with its natural roots-of-unity target. -/
noncomputable def absoluteKummerContinuousNthRootsCharacterEquiv
    [CharZero K]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range ≃*
      (Field.absoluteGaloisGroup K →ₜ*
        DiscreteNthRootsSubgroup (AlgebraicClosure K) (n : ℕ)) :=
    (absolutePowerClassEquivRadicalQuotient K n).trans
    (infiniteKummerContinuousCharacterEquivOfPrimitiveRoots
      (K := K) (Ω := AlgebraicClosure K) n hmu)

private noncomputable def nthRootsSubgroupEquivMultiplicativeZMod
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    nthRootsSubgroup (AlgebraicClosure K) (n : ℕ) ≃*
      Multiplicative (ZMod (n : ℕ)) := by
  letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let ζ : K := hmu.choose
  let hζ : IsPrimitiveRoot ζ (n : ℕ) :=
    (mem_primitiveRoots n.pos).mp hmu.choose_spec
  let hζunit := hζ.isUnit_unit' n.ne_zero
  exact
    (nthRootsSubgroupEquivOfPrimitiveRoots K (AlgebraicClosure K) n hmu).symm |>.trans
      ((nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)).trans
        ((MulEquiv.subgroupCongr hζunit.zpowers_eq.symm).trans
          hζunit.zmodEquivZPowers.symm.toMultiplicativeRight))

local instance discreteMultiplicativeZModTopologicalSpace (n : ℕ) :
    TopologicalSpace (Multiplicative (ZMod n)) := ⊥
local instance discreteMultiplicativeZModDiscreteTopology (n : ℕ) :
    DiscreteTopology (Multiplicative (ZMod n)) :=
  discreteTopology_bot _

private noncomputable def discreteNthRootsContinuousMulEquivMultiplicativeZMod
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    DiscreteNthRootsSubgroup (AlgebraicClosure K) (n : ℕ) ≃ₜ*
      Multiplicative (ZMod (n : ℕ)) where
  __ := nthRootsSubgroupEquivMultiplicativeZMod K n hmu
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

private def continuousCharacterCongrRight
    {G A B : Type*} [Group G] [TopologicalSpace G]
    [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B]
    (e : A ≃ₜ* B) :
    (G →ₜ* A) ≃* (G →ₜ* B) where
  toFun f :=
    ⟨e.toMulEquiv.toMonoidHom.comp f.toMonoidHom,
      e.continuous.comp f.continuous⟩
  invFun f :=
    ⟨e.symm.toMulEquiv.toMonoidHom.comp f.toMonoidHom,
      e.symm.continuous.comp f.continuous⟩
  left_inv f := by
    ext g
    exact e.symm_apply_apply (f g)
  right_inv f := by
    ext g
    exact e.apply_symm_apply (f g)
  map_mul' f g := by
    ext x
    exact map_mul e (f x) (g x)

/-- Absolute Kummer theory in the mod-`n` character convention used by the
continuous degree-one cohomology API. -/
noncomputable def absoluteKummerContinuousZModCharacterEquiv
    [CharZero K]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range ≃*
      (Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod (n : ℕ))) :=
  (absoluteKummerContinuousNthRootsCharacterEquiv K n hmu).trans
    (continuousCharacterCongrRight
      (discreteNthRootsContinuousMulEquivMultiplicativeZMod K n hmu))

end ClassFieldTower.Martinet.Shafarevich
