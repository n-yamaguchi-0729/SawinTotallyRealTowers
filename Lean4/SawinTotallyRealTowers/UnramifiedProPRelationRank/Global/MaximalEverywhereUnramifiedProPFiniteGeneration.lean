/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.FrattiniClassField

set_option autoImplicit false
/-!
# Finite generation of the maximal everywhere-unramified pro-p Galois group

The power--commutator quotient of the maximal everywhere-unramified pro-`p`
Galois group is the finite Galois group of the elementary Hilbert layer.  A
finite set of lifts of that quotient topologically generates the full group.
-/

open scoped NumberField IsMulCommutative

noncomputable section

open Set
open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields

namespace ClassFieldTower.Martinet

open ClassFieldTower.ProP
open ProCGroups.Generation
open ProCGroups.FiniteGeneration

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- For odd `p`, the maximal everywhere-unramified pro-`p` Galois group is
topologically finitely generated. -/
theorem maxEverywhereUnramifiedProPGaloisGroup_topologicallyFinitelyGenerated
    (hpOdd : Odd p) :
    TopologicallyFinitelyGenerated
      (MaxEverywhereUnramifiedProPGaloisGroup F p) := by
  classical
  let G := MaxEverywhereUnramifiedProPGaloisGroup F p
  let E := hilbertElementaryLayerInMaximal F p
  let : (closedPowerCommutator p G).Normal :=
    closedPowerCommutator_normal p G
  let e : powerCommutatorQuotient p G ≃* Gal(E / F) :=
    maxPowerCommutatorEquivHilbert F p hpOdd
  let : Finite (powerCommutatorQuotient p G) :=
    Finite.of_equiv Gal(E / F) e.symm.toEquiv
  have hpG : ProCGroups.ProC.HasPGroupOpenNormalBasis p G :=
    maxEverywhereUnramifiedProPGaloisGroup_hasPGroupOpenNormalBasis
      F p hpOdd
  let : Fintype (powerCommutatorQuotient p G) := Fintype.ofFinite _
  let liftQ : powerCommutatorQuotient p G → G :=
    Function.surjInv (powerCommutatorQuotientMk_surjective p G)
  let s : Finset G := Finset.univ.image liftQ
  refine ⟨s, (topologicallyGenerates_iff_powerCommutatorQuotient_image hpG).2 ?_⟩
  have himage :
      (powerCommutatorQuotientMk p G) '' (s : Set G) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    refine ⟨liftQ z, ?_, ?_⟩
    · simp [s]
    · exact Function.surjInv_eq
        (powerCommutatorQuotientMk_surjective p G) z
  rw [himage]
  apply top_unique
  rw [Subgroup.closure_univ]
  exact Subgroup.le_topologicalClosure _

end ClassFieldTower.Martinet
