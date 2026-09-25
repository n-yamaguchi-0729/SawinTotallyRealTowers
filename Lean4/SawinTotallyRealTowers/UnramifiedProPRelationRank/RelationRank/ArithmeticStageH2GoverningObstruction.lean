/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageH2EmbeddingProblem
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealRadicalGoverningFieldLinearDuality

set_option autoImplicit false
/-!
# Arithmetic-stage central obstructions and the governing field

The kernel of a finite arithmetic-stage degree-two embedding problem is the
lifted `ZMod p` coefficient.  Consequently, an actual character of the
cyclotomic ideal radical valued in that central kernel determines a unique
automorphism of the ideal-radical governing field.  The conversion is
injective and detects a nontrivial obstruction character.

This file only performs that canonical algebraic conversion.  It does not
assert that an arbitrary degree-two class supplies such a radical character;
constructing that character from local splittings and global reciprocity is
the remaining arithmetic duality step.
-/

open scoped NumberField IsMulCommutative Topology

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology ClassFieldTower.Martinet ClassFieldTower.ProP
open KummerTheory ProCGroups ProCGroups.ProC

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

local instance : IsAbelianGalois
    (IdealRadicalCyclotomicBase F p Fact.out)
    (IdealRadicalGoverningField F p Fact.out) :=
  idealRadicalGoverningField_isAbelianGalois F p Fact.out

private theorem arithmeticStageH2Projection_right_eq_one
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (x : (arithmeticStageH2Projection F p hpOdd U xU).ker) :
    x.1.right = 1 := by
  let e := openNormalQuotientContinuousEquivArithmeticStageGalois F p hpOdd U
  apply e.injective
  have hx := x.2
  change e x.1.right = 1 at hx
  simpa only [map_one] using hx

/-- The kernel of the arithmetic-stage projection is canonically the
coefficient group of the chosen degree-two cocycle extension. -/
noncomputable def arithmeticStageH2ProjectionKernelEquivCoefficient
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2) :
    (arithmeticStageH2Projection F p hpOdd U xU).ker ≃*
      Multiplicative (FreeProPH2Cocycle.A p) where
  toFun x := x.1.left
  invFun a := ⟨⟨a, 1⟩, by
    change
      openNormalQuotientContinuousEquivArithmeticStageGalois F p hpOdd U 1 = 1
    exact map_one _⟩
  left_inv x := by
    apply Subtype.ext
    apply H2CocycleExtension.ext
    · rfl
    · exact (arithmeticStageH2Projection_right_eq_one F p hpOdd U xU x).symm
  right_inv _ := rfl
  map_mul' x y := by
    change x.1.left + y.1.left +
        FreeProPH2Cocycle.normalizedCocycle
          (degreeTwoCocycleRepresentative xU) x.1.right y.1.right =
      x.1.left + y.1.left
    rw [arithmeticStageH2Projection_right_eq_one F p hpOdd U xU x,
      arithmeticStageH2Projection_right_eq_one F p hpOdd U xU y,
      FreeProPH2Cocycle.normalizedCocycle_one_left]
    simp

/-- A stage obstruction character is a radical character valued in the
central coefficient kernel of the arithmetic-stage embedding problem. -/
abbrev ArithmeticStageH2RadicalObstructionCharacter
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2) :=
  IdealRadicalCyclotomicRestrictedQuotient F p →*
    (arithmeticStageH2Projection F p hpOdd U xU).ker

private noncomputable def liftedCoefficientMulEquivZMod :
    Multiplicative (FreeProPH2Cocycle.A p) ≃*
      Multiplicative (ZMod p) :=
  AddEquiv.toMultiplicative
    (ULift.moduleEquiv (R := ZMod p)).toAddEquiv

private theorem governingFieldPrimitiveRootsNonempty :
    (primitiveRoots p (IdealRadicalGoverningField F p Fact.out)).Nonempty := by
  let K := IdealRadicalCyclotomicBase F p Fact.out
  let E := IdealRadicalGoverningField F p Fact.out
  obtain ⟨zeta, hzeta⟩ :=
    idealRadicalCyclotomicBase_primitiveRoots_nonempty F p Fact.out
  refine ⟨algebraMap K E zeta, ?_⟩
  rw [mem_primitiveRoots (Fact.out : p.Prime).pos]
  exact ((mem_primitiveRoots (Fact.out : p.Prime).pos).mp hzeta).map_of_injective
    (algebraMap K E).injective

/-- Coefficient coordinates of a central-kernel-valued obstruction character. -/
noncomputable def arithmeticStageH2RadicalObstructionCharacterZMod
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (chi : ArithmeticStageH2RadicalObstructionCharacter F p hpOdd U xU) :
    IdealRadicalCyclotomicRestrictedQuotient F p →*
      Multiplicative (ZMod p) :=
  (liftedCoefficientMulEquivZMod p).toMonoidHom.comp
    ((arithmeticStageH2ProjectionKernelEquivCoefficient F p hpOdd U xU).toMonoidHom.comp
      chi)

@[simp]
theorem arithmeticStageH2RadicalObstructionCharacterZMod_apply
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (chi : ArithmeticStageH2RadicalObstructionCharacter F p hpOdd U xU)
    (q : IdealRadicalCyclotomicRestrictedQuotient F p) :
    arithmeticStageH2RadicalObstructionCharacterZMod
        F p hpOdd U xU chi q =
      liftedCoefficientMulEquivZMod p
        (arithmeticStageH2ProjectionKernelEquivCoefficient
          F p hpOdd U xU (chi q)) :=
  rfl

/-- A kernel-valued obstruction character determines the unique governing
automorphism with the same Kummer character. -/
noncomputable def arithmeticStageH2ObstructionGoverningAutomorphism
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (chi : ArithmeticStageH2RadicalObstructionCharacter F p hpOdd U xU) :
    IdealRadicalGoverningGalois F p := by
  let hp : p.Prime := Fact.out
  let n : ℕ+ := p.toPNat hp.pos
  let : Fact ((n : ℕ).Prime) :=
    ⟨by simpa [n, Nat.toPNat] using hp⟩
  let eRootRaw := localNthRootsEquivMultiplicativeZMod
    (IdealRadicalGoverningField F p Fact.out) n
    (by simpa [n, Nat.toPNat] using governingFieldPrimitiveRootsNonempty F p)
  let eRoot :
      nthRootsSubgroup (IdealRadicalGoverningField F p Fact.out) p ≃*
        Multiplicative (ZMod p) :=
    Eq.mp (by rfl) eRootRaw
  let chiRoots := eRoot.symm.toMonoidHom.comp
    (arithmeticStageH2RadicalObstructionCharacterZMod F p hpOdd U xU chi)
  exact (idealRadicalGoverningFieldCharacterDuality F p Fact.out).symm chiRoots

/-- The governing automorphism has exactly the coefficient character with
which the stage obstruction started. -/
@[simp]
theorem idealRadicalGoverningFieldPairingZMod_obstructionGoverning_apply
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (chi : ArithmeticStageH2RadicalObstructionCharacter F p hpOdd U xU)
    (q : IdealRadicalCyclotomicRestrictedQuotient F p) :
    idealRadicalGoverningFieldPairingZMod F p
        (arithmeticStageH2ObstructionGoverningAutomorphism
          F p hpOdd U xU chi) q =
      arithmeticStageH2RadicalObstructionCharacterZMod
        F p hpOdd U xU chi q := by
  let hp : p.Prime := Fact.out
  let n : ℕ+ := p.toPNat hp.pos
  let : Fact ((n : ℕ).Prime) :=
    ⟨by simpa [n, Nat.toPNat] using hp⟩
  let eRootRaw := localNthRootsEquivMultiplicativeZMod
    (IdealRadicalGoverningField F p Fact.out) n
    (by simpa [n, Nat.toPNat] using governingFieldPrimitiveRootsNonempty F p)
  let eRoot :
      nthRootsSubgroup (IdealRadicalGoverningField F p Fact.out) p ≃*
        Multiplicative (ZMod p) :=
    Eq.mp (by rfl) eRootRaw
  let d := idealRadicalGoverningFieldCharacterDuality F p Fact.out
  unfold idealRadicalGoverningFieldPairingZMod
  unfold arithmeticStageH2ObstructionGoverningAutomorphism
  dsimp only
  change eRoot
    (d (d.symm (eRoot.symm.toMonoidHom.comp
      (arithmeticStageH2RadicalObstructionCharacterZMod
        F p hpOdd U xU chi))) q) = _
  rw [d.apply_symm_apply]
  exact eRoot.apply_symm_apply _

/-- Passing from a central-kernel obstruction character to its governing
automorphism loses no information. -/
theorem arithmeticStageH2ObstructionGoverningAutomorphism_injective
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2) :
    Function.Injective
      (arithmeticStageH2ObstructionGoverningAutomorphism F p hpOdd U xU) := by
  intro chi psi h
  apply MonoidHom.ext
  intro q
  have hq := congrArg
    (fun sigma => idealRadicalGoverningFieldPairingZMod F p sigma q) h
  rw [idealRadicalGoverningFieldPairingZMod_obstructionGoverning_apply,
    idealRadicalGoverningFieldPairingZMod_obstructionGoverning_apply] at hq
  exact (arithmeticStageH2ProjectionKernelEquivCoefficient
    F p hpOdd U xU).injective
      ((liftedCoefficientMulEquivZMod p).injective hq)

@[simp]
theorem arithmeticStageH2ObstructionGoverningAutomorphism_one
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2) :
    arithmeticStageH2ObstructionGoverningAutomorphism F p hpOdd U xU 1 = 1 := by
  apply idealRadicalGoverningFieldPairingZMod_injective F p
  apply MonoidHom.ext
  intro q
  rw [map_one,
    idealRadicalGoverningFieldPairingZMod_obstructionGoverning_apply,
    arithmeticStageH2RadicalObstructionCharacterZMod_apply]
  exact (liftedCoefficientMulEquivZMod.{0} p).map_one

/-- A nontrivial central-kernel obstruction character produces a nontrivial
governing automorphism. -/
theorem arithmeticStageH2ObstructionGoverningAutomorphism_ne_one
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    {chi : ArithmeticStageH2RadicalObstructionCharacter F p hpOdd U xU}
    (hchi : chi ≠ 1) :
    arithmeticStageH2ObstructionGoverningAutomorphism
      F p hpOdd U xU chi ≠ 1 := by
  intro h
  apply hchi
  apply arithmeticStageH2ObstructionGoverningAutomorphism_injective
    F p hpOdd U xU
  simpa using h

end


end ClassFieldTower.Martinet.Shafarevich
