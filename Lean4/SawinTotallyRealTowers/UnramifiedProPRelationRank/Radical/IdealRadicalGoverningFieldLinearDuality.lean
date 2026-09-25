/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealRadicalGoverningField
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealRadicalCyclotomicModule
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalHilbertKummerDual

set_option autoImplicit false
/-!
# Linear Kummer duality for the ideal-radical governing field

The Kummer character isomorphism for the governing extension is linearized
over `ZMod p`.  Thus every governing automorphism gives a functional on the
cyclotomic restricted ideal radical, and the resulting linear map is faithful.
-/

open scoped NumberField IsMulCommutative

namespace ClassFieldTower.Martinet.Shafarevich

open NumberField KummerTheory

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

local instance : IsAbelianGalois
    (IdealRadicalCyclotomicBase F p Fact.out)
    (IdealRadicalGoverningField F p Fact.out) :=
  idealRadicalGoverningField_isAbelianGalois F p Fact.out

/-- The Galois group of the ideal-radical governing extension. -/
abbrev IdealRadicalGoverningGalois :=
  Gal(IdealRadicalGoverningField F p Fact.out /
    IdealRadicalCyclotomicBase F p Fact.out)

/-- The restricted radical paired with the ideal-radical governing group. -/
abbrev IdealRadicalCyclotomicRestrictedQuotient :=
  RestrictedRadicalQuotient (p.toPNat (Fact.out : p.Prime).pos)
    (idealRadicalCyclotomicKummerSubgroup F p Fact.out)

private theorem idealRadicalGoverningField_primitiveRoots_nonempty :
    (primitiveRoots p (IdealRadicalGoverningField F p Fact.out)).Nonempty := by
  let K := IdealRadicalCyclotomicBase F p Fact.out
  let E := IdealRadicalGoverningField F p Fact.out
  obtain ⟨zeta, hzeta⟩ :=
    idealRadicalCyclotomicBase_primitiveRoots_nonempty F p Fact.out
  refine ⟨algebraMap K E zeta, ?_⟩
  rw [mem_primitiveRoots (Fact.out : p.Prime).pos]
  exact ((mem_primitiveRoots (Fact.out : p.Prime).pos).mp hzeta).map_of_injective
    (algebraMap K E).injective

/-- The governing-field Kummer pairing with its root-of-unity values written
in `ZMod p`. -/
noncomputable def idealRadicalGoverningFieldPairingZMod :
    IdealRadicalGoverningGalois F p →*
      (IdealRadicalCyclotomicRestrictedQuotient F p →*
        Multiplicative (ZMod p)) := by
  let hp : p.Prime := Fact.out
  let n : ℕ+ := (p.toPNat hp.pos)
  let _ : Fact ((n : ℕ).Prime) :=
    ⟨by simpa [n, Nat.toPNat] using hp⟩
  let e := localNthRootsEquivMultiplicativeZMod
    (IdealRadicalGoverningField F p Fact.out) n
    (idealRadicalGoverningField_primitiveRoots_nonempty F p)
  let d := idealRadicalGoverningFieldCharacterDuality F p Fact.out
  exact
  { toFun := fun sigma => e.toMonoidHom.comp (d sigma)
    map_one' := by
      apply MonoidHom.ext
      intro q
      change e (d 1 q) = 1
      rw [map_one]
      exact e.map_one
    map_mul' := by
      intro sigma tau
      apply MonoidHom.ext
      intro q
      change e (d (sigma * tau) q) = e (d sigma q) * e (d tau q)
      rw [map_mul]
      exact e.map_mul _ _ }

/-- The exponent-`p` governing Galois group as a `ZMod p`-module. -/
@[reducible]
noncomputable def idealRadicalGoverningGaloisModPModule :
    Module (ZMod p) (Additive (IdealRadicalGoverningGalois F p)) :=
  additiveZModModuleOfPowEqOne p
    (idealRadicalGoverningField_galois_pow_eq_one F p Fact.out)

/-- The exponent-`p` governing Galois group as a module object. -/
noncomputable def idealRadicalGoverningGaloisModP : ModuleCat (ZMod p) := by
  letI : Module (ZMod p) (Additive (IdealRadicalGoverningGalois F p)) :=
    idealRadicalGoverningGaloisModPModule F p
  exact ModuleCat.of (ZMod p) (Additive (IdealRadicalGoverningGalois F p))

/-- Evaluation of a governing automorphism on the restricted radical, in
`ZMod p` coordinates. -/
noncomputable def idealRadicalGoverningFieldLinearFunctional
    (sigma : idealRadicalGoverningGaloisModP (F := F) p) :
    Module.Dual (ZMod p) (idealRadicalCyclotomicModP F p) := by
  letI : Module (ZMod p)
      (Additive (IdealRadicalCyclotomicRestrictedQuotient F p)) :=
    idealRadicalCyclotomicModPModule F p
  exact
    (idealRadicalGoverningFieldPairingZMod F p
      (Additive.toMul sigma)).toAdditiveLeft.toZModLinearMap p

/-- Kummer character duality, linearized over `ZMod p`. -/
noncomputable def idealRadicalGoverningFieldLinearDuality :
    idealRadicalGoverningGaloisModP (F := F) p →ₗ[ZMod p]
      Module.Dual (ZMod p) (idealRadicalCyclotomicModP F p) := by
  letI : Module (ZMod p) (Additive (IdealRadicalGoverningGalois F p)) :=
    idealRadicalGoverningGaloisModPModule F p
  letI : Module (ZMod p)
      (Additive (IdealRadicalCyclotomicRestrictedQuotient F p)) :=
    idealRadicalCyclotomicModPModule F p
  let f : Additive (IdealRadicalGoverningGalois F p) →+
      Module.Dual (ZMod p) (idealRadicalCyclotomicModP F p) :=
  { toFun := idealRadicalGoverningFieldLinearFunctional F p
    map_zero' := by
      apply LinearMap.ext
      intro q
      change
        (idealRadicalGoverningFieldPairingZMod F p 1
          (Additive.toMul q)).toAdd = 0
      rw [map_one]
      rfl
    map_add' := by
      intro sigma tau
      apply LinearMap.ext
      intro q
      change
        (idealRadicalGoverningFieldPairingZMod F p
          (Additive.toMul sigma * Additive.toMul tau)
          (Additive.toMul q)).toAdd =
        (idealRadicalGoverningFieldPairingZMod F p
          (Additive.toMul sigma) (Additive.toMul q)).toAdd +
        (idealRadicalGoverningFieldPairingZMod F p
          (Additive.toMul tau) (Additive.toMul q)).toAdd
      rw [map_mul]
      rfl }
  exact f.toZModLinearMap p

@[simp]
theorem idealRadicalGoverningFieldLinearDuality_apply
    (sigma : idealRadicalGoverningGaloisModP (F := F) p)
    (q : idealRadicalCyclotomicModP F p) :
    idealRadicalGoverningFieldLinearDuality F p sigma q =
      (idealRadicalGoverningFieldPairingZMod F p
        (Additive.toMul sigma) (Additive.toMul q)).toAdd :=
  rfl

/-- Root coordinates preserve the faithfulness of governing-field Kummer
character duality. -/
theorem idealRadicalGoverningFieldPairingZMod_injective :
    Function.Injective (idealRadicalGoverningFieldPairingZMod F p) := by
  intro sigma tau h
  let hp : p.Prime := Fact.out
  let n : ℕ+ := (p.toPNat hp.pos)
  let _ : Fact ((n : ℕ).Prime) :=
    ⟨by simpa [n, Nat.toPNat] using hp⟩
  let e := localNthRootsEquivMultiplicativeZMod
    (IdealRadicalGoverningField F p Fact.out) n
    (idealRadicalGoverningField_primitiveRoots_nonempty F p)
  let d := idealRadicalGoverningFieldCharacterDuality F p Fact.out
  apply d.injective
  apply MonoidHom.ext
  intro q
  apply e.injective
  exact DFunLike.congr_fun h q

/-- The linearized governing-field character map is injective. -/
theorem idealRadicalGoverningFieldLinearDuality_injective :
    Function.Injective (idealRadicalGoverningFieldLinearDuality F p) := by
  intro sigma tau h
  apply Additive.toMul.injective
  apply idealRadicalGoverningFieldPairingZMod_injective F p
  apply MonoidHom.ext
  intro q
  apply Multiplicative.toAdd.injective
  exact LinearMap.congr_fun h (Additive.ofMul q)

end

end ClassFieldTower.Martinet.Shafarevich
