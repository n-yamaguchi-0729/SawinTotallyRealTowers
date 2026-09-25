/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealRadicalCyclotomicBase
import GaloisCohomology.Kummer.Concrete.KummerCorrespondenceFormula

set_option autoImplicit false
/-!
# The ideal-radical governing field

For a number field `F` and a prime `p`, this file adjoins the `p`-th roots of the
empty-support ideal radical after passing to `F(μ_p)`.  Kummer theory identifies
the resulting finite abelian exponent-`p` Galois group with the character group
of the restricted radical quotient.
-/

open scoped NumberField

namespace ClassFieldTower.Martinet.Shafarevich

open NumberField
open KummerTheory

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (p : ℕ) (hp : p.Prime)

private theorem idealRadicalCyclotomicBase_isSepClosure :
    IsSepClosure (IdealRadicalCyclotomicBase F p hp) (AlgebraicClosure F) := by
  let _ : Algebra.IsSeparable (IdealRadicalCyclotomicBase F p hp)
      (AlgebraicClosure F) :=
    Algebra.isSeparable_tower_top_of_isSeparable F
      (IdealRadicalCyclotomicBase F p hp) (AlgebraicClosure F)
  exact ⟨inferInstance, inferInstance⟩

/-- The Kummer extension of `F(μ_p)` governed by the empty-support ideal
`p`-power radical of `F`. -/
noncomputable def IdealRadicalGoverningField :
    IntermediateField (IdealRadicalCyclotomicBase F p hp)
      (AlgebraicClosure F) :=
  kummerRadicalExtension
    (K := IdealRadicalCyclotomicBase F p hp)
    (Omega := AlgebraicClosure F) (p.toPNat hp.pos)
    (idealRadicalCyclotomicKummerSubgroup F p hp).1

/-- The governing extension is Galois over the cyclotomic base. -/
theorem idealRadicalGoverningField_isGalois :
    IsGalois (IdealRadicalCyclotomicBase F p hp)
      (IdealRadicalGoverningField F p hp) := by
  let _ : IsSepClosure (IdealRadicalCyclotomicBase F p hp)
      (AlgebraicClosure F) :=
    idealRadicalCyclotomicBase_isSepClosure F p hp
  exact kummerRadicalExtension_isGalois (p.toPNat hp.pos)
    (idealRadicalCyclotomicKummerSubgroup F p hp).1

/-- The canonical Kummer character duality for the ideal-radical governing
extension. -/
noncomputable def idealRadicalGoverningFieldCharacterDuality :
    Gal(IdealRadicalGoverningField F p hp/
      IdealRadicalCyclotomicBase F p hp) ≃*
      (RestrictedRadicalQuotient (p.toPNat hp.pos)
          (idealRadicalCyclotomicKummerSubgroup F p hp) →*
        nthRootsSubgroup (IdealRadicalGoverningField F p hp) p) := by
  let _ : IsSepClosure (IdealRadicalCyclotomicBase F p hp)
      (AlgebraicClosure F) :=
    idealRadicalCyclotomicBase_isSepClosure F p hp
  apply kummerRadicalExtensionRestrictedTransposeMulEquiv
  · exact_mod_cast hp.ne_zero
  · exact idealRadicalCyclotomicBase_primitiveRoots_nonempty F p hp

/-- The Galois group of the governing extension is finite. -/
theorem finite_idealRadicalGoverningField_galois :
    Finite Gal(IdealRadicalGoverningField F p hp/
      IdealRadicalCyclotomicBase F p hp) := by
  let Q := RestrictedRadicalQuotient (p.toPNat hp.pos)
    (idealRadicalCyclotomicKummerSubgroup F p hp)
  let E := IdealRadicalGoverningField F p hp
  let M := nthRootsSubgroup E p
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let _ : Finite Q :=
    finite_idealRadicalCyclotomicRestrictedQuotient F p hp
  let _ : Fintype M := nthRootsSubgroupFintype E p
  let _ : Finite (Q →* M) :=
    Finite.of_injective (fun chi : Q →* M ↦ (chi : Q → M))
      DFunLike.coe_injective
  exact Finite.of_equiv (Q →* M)
    (idealRadicalGoverningFieldCharacterDuality F p hp).symm.toEquiv

/-- The governing extension is finite-dimensional over `F(μ_p)`. -/
theorem finiteDimensional_idealRadicalGoverningField :
    FiniteDimensional (IdealRadicalCyclotomicBase F p hp)
      (IdealRadicalGoverningField F p hp) := by
  let _ : IsSepClosure (IdealRadicalCyclotomicBase F p hp)
      (AlgebraicClosure F) :=
    idealRadicalCyclotomicBase_isSepClosure F p hp
  let _ : IsGalois (IdealRadicalCyclotomicBase F p hp)
      (IdealRadicalGoverningField F p hp) :=
    idealRadicalGoverningField_isGalois F p hp
  let _ : Finite Gal(IdealRadicalGoverningField F p hp/
      IdealRadicalCyclotomicBase F p hp) :=
    finite_idealRadicalGoverningField_galois F p hp
  exact IsGalois.finiteDimensional_of_finite
    (IdealRadicalCyclotomicBase F p hp)
    (IdealRadicalGoverningField F p hp)

/-- The governing extension is abelian Galois over `F(μ_p)`. -/
theorem idealRadicalGoverningField_isAbelianGalois :
    IsAbelianGalois (IdealRadicalCyclotomicBase F p hp)
      (IdealRadicalGoverningField F p hp) := by
  let _ : IsSepClosure (IdealRadicalCyclotomicBase F p hp)
      (AlgebraicClosure F) :=
    idealRadicalCyclotomicBase_isSepClosure F p hp
  exact kummerRadicalExtension_isAbelianGalois (p.toPNat hp.pos)
    (idealRadicalCyclotomicBase_primitiveRoots_nonempty F p hp)
    (idealRadicalCyclotomicKummerSubgroup F p hp).1

/-- Every automorphism of the governing extension has exponent dividing `p`. -/
theorem idealRadicalGoverningField_galois_pow_eq_one
    (sigma : Gal(IdealRadicalGoverningField F p hp/
      IdealRadicalCyclotomicBase F p hp)) :
    sigma ^ p = 1 := by
  let _ : IsSepClosure (IdealRadicalCyclotomicBase F p hp)
      (AlgebraicClosure F) :=
    idealRadicalCyclotomicBase_isSepClosure F p hp
  exact kummerRadicalExtension_galois_pow_eq_one (p.toPNat hp.pos)
    (idealRadicalCyclotomicBase_primitiveRoots_nonempty F p hp)
    (idealRadicalCyclotomicKummerSubgroup F p hp).1 sigma

/-- The chosen cyclotomic Kummer subgroup lies in the radical of its
governing extension. -/
theorem idealRadicalCyclotomicKummerSubgroup_le_governingRadical :
    (idealRadicalCyclotomicKummerSubgroup F p hp).1 ≤
      finiteKummerRadicalSubgroup
        (K := IdealRadicalCyclotomicBase F p hp)
        (L := IdealRadicalGoverningField F p hp) (p.toPNat hp.pos) := by
  let _ : IsSepClosure (IdealRadicalCyclotomicBase F p hp)
      (AlgebraicClosure F) :=
    idealRadicalCyclotomicBase_isSepClosure F p hp
  apply le_finiteKummerRadicalSubgroup_kummerRadicalExtension
  exact_mod_cast hp.ne_zero

/-- In particular, every element of the base-field ideal radical maps into
the Kummer radical of the governing extension. -/
theorem idealRadicalToCyclotomicBase_mem_governingRadical
    (a : (idealNthPowerRadicalKummerSubgroup F (p.toPNat hp.pos)).1) :
    idealRadicalToCyclotomicBase F p hp a ∈
      finiteKummerRadicalSubgroup
        (K := IdealRadicalCyclotomicBase F p hp)
        (L := IdealRadicalGoverningField F p hp) (p.toPNat hp.pos) := by
  apply idealRadicalCyclotomicKummerSubgroup_le_governingRadical F p hp
  exact (le_sup_left : MonoidHom.range
    (idealRadicalToCyclotomicBase F p hp) ≤
      (idealRadicalCyclotomicKummerSubgroup F p hp).1) ⟨a, rfl⟩

end

end ClassFieldTower.Martinet.Shafarevich
