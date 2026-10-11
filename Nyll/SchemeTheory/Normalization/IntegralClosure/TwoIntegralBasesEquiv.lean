/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.IntegralClosure.IntegralBase.Equiv

/-!
# Comparing integral closures over two integral bases

Let `B` and `C` be integral `A`-algebras embedded compatibly in one ambient
ring `L`.  Both `integralClosure B L` and `integralClosure C L` are the same
subring of `L`, although their literal Lean types differ.  This file gives
the canonical comparison through `integralClosure A L` and records that it
is the identity in the ambient ring.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uB uC uL

variable {A : Type uA} {B : Type uB} {C : Type uC} {L : Type uL}
variable [CommRing A] [CommRing B] [CommRing C] [CommRing L]
variable [Algebra A B] [Algebra A C]
variable [Algebra A L] [Algebra B L] [Algebra C L]
variable [IsScalarTower A B L] [IsScalarTower A C L]
variable [Algebra.IsIntegral A B] [Algebra.IsIntegral A C]

/-- The canonical `B`-algebra structure on the normalization written over
the other integral base `C`.

It is transported through the canonical identification with
`integralClosure A L`; hence its map to `L` is the originally supplied map
`B → L`. -/
@[reducible]
noncomputable def integralClosureTwoIntegralBasesAlgebra :
    Algebra B (integralClosure C L) := by
  letI : Algebra B (integralClosure A L) :=
    integralClosureIntegralBaseAlgebra
  letI : Algebra C (integralClosure A L) :=
    integralClosureIntegralBaseAlgebra
  let eC : integralClosure C L ≃ₐ[C] integralClosure A L :=
    integralClosureIntegralBaseAlgEquiv
  exact
    (eC.symm.toRingEquiv.toRingHom.comp
      (algebraMap B (integralClosure A L))).toAlgebra

/-- Integral closures over two integral bases are canonically equivalent.
The target `B`-algebra structure is the preceding transported structure. -/
noncomputable def integralClosureTwoIntegralBasesAlgEquiv :
    letI : Algebra B (integralClosure C L) :=
      integralClosureTwoIntegralBasesAlgebra (A := A) (B := B) (C := C) (L := L)
    integralClosure B L ≃ₐ[B] integralClosure C L := by
  letI : Algebra B (integralClosure A L) :=
    integralClosureIntegralBaseAlgebra
  letI : Algebra C (integralClosure A L) :=
    integralClosureIntegralBaseAlgebra
  letI : Algebra B (integralClosure C L) :=
    integralClosureTwoIntegralBasesAlgebra (A := A) (B := B) (C := C) (L := L)
  let eB : integralClosure B L ≃ₐ[B] integralClosure A L :=
    integralClosureIntegralBaseAlgEquiv
  let eC : integralClosure C L ≃ₐ[C] integralClosure A L :=
    integralClosureIntegralBaseAlgEquiv
  refine
    { toRingEquiv := eB.toRingEquiv.trans eC.symm.toRingEquiv
      commutes' := ?_ }
  intro b
  change eC.symm (eB (algebraMap B (integralClosure B L) b)) =
    eC.symm (algebraMap B (integralClosure A L) b)
  rw [eB.commutes]

/-- The comparison of the two literal normalization types is the identity
after coercion to their common ambient ring. -/
@[simp]
theorem algebraMap_integralClosureTwoIntegralBasesAlgEquiv
    (x : integralClosure B L) :
    letI : Algebra B (integralClosure C L) :=
      integralClosureTwoIntegralBasesAlgebra (A := A) (B := B) (C := C) (L := L)
    algebraMap (integralClosure C L) L
        (integralClosureTwoIntegralBasesAlgEquiv
          (A := A) (B := B) (C := C) (L := L) x) =
      algebraMap (integralClosure B L) L x := by
  let : Algebra B (integralClosure A L) :=
    integralClosureIntegralBaseAlgebra
  let : Algebra C (integralClosure A L) :=
    integralClosureIntegralBaseAlgebra
  let : Algebra B (integralClosure C L) :=
    integralClosureTwoIntegralBasesAlgebra (A := A) (B := B) (C := C) (L := L)
  let eB : integralClosure B L ≃ₐ[B] integralClosure A L :=
    integralClosureIntegralBaseAlgEquiv
  let eC : integralClosure C L ≃ₐ[C] integralClosure A L :=
    integralClosureIntegralBaseAlgEquiv
  have hC := algebraMap_integralClosureIntegralBaseAlgEquiv
    (A := A) (B := C) (L := L) (eC.symm (eB x))
  have hB := algebraMap_integralClosureIntegralBaseAlgEquiv
    (A := A) (B := B) (L := L) x
  change algebraMap (integralClosure C L) L (eC.symm (eB x)) =
    algebraMap (integralClosure B L) L x
  calc
    algebraMap (integralClosure C L) L (eC.symm (eB x)) =
        algebraMap (integralClosure A L) L
          (eC (eC.symm (eB x))) := by
      simpa [eC] using hC.symm
    _ = algebraMap (integralClosure A L) L (eB x) := by
      rw [eC.apply_symm_apply]
    _ = algebraMap (integralClosure B L) L x := by
      simpa [eB] using hB

end EtaleFundamentalGroups

end
