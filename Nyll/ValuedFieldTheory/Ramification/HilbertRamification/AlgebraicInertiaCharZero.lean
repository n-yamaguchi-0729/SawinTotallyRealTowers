/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.BaseChange
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteInertiaStructure
import Nyll.ValuedFieldTheory.Valuation.ComapResidueCharacteristic
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Inertia in residue characteristic zero over an algebraic Galois extension

Every field element lies in its actual finite Galois normal closure. Pullback
restricts inertia to that layer, and the comap valuation subring has residue
characteristic zero. Finite inertia is commutative there, and the defining
restriction formula gives commutativity on each element of the original field.
No Henselianity, discreteness, or finite-residue hypothesis is used.
-/


namespace RamificationTheory.HilbertRamification.ValuationSubring

universe u v

/-- Inertia is commutative for any algebraic Galois extension in residue
characteristic zero, using the specified valuation subring upstairs. -/
theorem inertiaGroup_isMulCommutative_of_isGalois_residueCharZero
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (A : _root_.ValuationSubring L) [CharZero (IsLocalRing.ResidueField A)] :
    IsMulCommutative (inertiaGroup K A) := by
  classical
  apply IsMulCommutative.of_comm
  intro σ τ
  apply Subtype.ext
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  change (inertiaGroupToAut (K := K) A σ)
      ((inertiaGroupToAut (K := K) A τ) x) =
    (inertiaGroupToAut (K := K) A τ) ((inertiaGroupToAut (K := K) A σ) x)
  let E : FiniteGaloisIntermediateField K L :=
    FiniteGaloisIntermediateField.adjoin K {x}
  have hx : x ∈ E.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K {x} (Set.mem_singleton x)
  let xE : E := ⟨x, hx⟩
  let i : E →+* L := E.toIntermediateField.val.toRingHom
  let B : _root_.ValuationSubring E := A.comap i
  have hsquare : i.comp (algebraMap K E) =
      (algebraMap K L).comp (RingHom.id K) := by
    apply RingHom.ext
    intro a
    change E.toIntermediateField.val (algebraMap K E a) = algebraMap K L a
    exact E.toIntermediateField.val.commutes a
  let ρ : inertiaGroup K A →* inertiaGroup K B :=
    _root_.HilbertRamification.ValuationSubring.galoisPullback_inertiaGroupMap
      (RingHom.id K) i hsquare A
  have hρ (g : inertiaGroup K A) (y : E) :
      i ((inertiaGroupToAut (K := K) B (ρ g)) y) =
        (inertiaGroupToAut (K := K) A g) (i y) := by
    change i ((_root_.HilbertRamification.galoisPullback_galoisPullback
      (RingHom.id K) i hsquare (inertiaGroupToAut (K := K) A g)) y) =
        (inertiaGroupToAut (K := K) A g) (i y)
    exact _root_.HilbertRamification.galoisPullback_galoisPullback_commutes
      (RingHom.id K) i hsquare (inertiaGroupToAut (K := K) A g) y
  have : CharZero (IsLocalRing.ResidueField B) :=
    _root_.ValuationSubring.charZero_residueField_comap A i
  have hcomm : ρ σ * ρ τ = ρ τ * ρ σ :=
    (isMulCommutative_iff.mp (inertiaGroup_isMulCommutative_of_residueCharZero K B))
      (ρ σ) (ρ τ)
  calc
    (inertiaGroupToAut (K := K) A σ) ((inertiaGroupToAut (K := K) A τ) x) =
        (inertiaGroupToAut (K := K) A σ)
          ((inertiaGroupToAut (K := K) A τ) (i xE)) := rfl
    _ = (inertiaGroupToAut (K := K) A σ)
        (i ((inertiaGroupToAut (K := K) B (ρ τ)) xE)) :=
      congrArg (inertiaGroupToAut (K := K) A σ) (hρ τ xE).symm
    _ = i ((inertiaGroupToAut (K := K) B (ρ σ))
        ((inertiaGroupToAut (K := K) B (ρ τ)) xE)) :=
      (hρ σ ((inertiaGroupToAut (K := K) B (ρ τ)) xE)).symm
    _ = i ((inertiaGroupToAut (K := K) B (ρ τ))
        ((inertiaGroupToAut (K := K) B (ρ σ)) xE)) := by
      simpa only [map_mul, AlgEquiv.mul_apply] using
        congrArg (fun g : inertiaGroup K B => i ((inertiaGroupToAut (K := K) B g) xE))
          hcomm
    _ = (inertiaGroupToAut (K := K) A τ)
        (i ((inertiaGroupToAut (K := K) B (ρ σ)) xE)) :=
      hρ τ ((inertiaGroupToAut (K := K) B (ρ σ)) xE)
    _ = (inertiaGroupToAut (K := K) A τ)
        ((inertiaGroupToAut (K := K) A σ) (i xE)) :=
      congrArg (inertiaGroupToAut (K := K) A τ) (hρ σ xE)
    _ = (inertiaGroupToAut (K := K) A τ) ((inertiaGroupToAut (K := K) A σ) x) := rfl

end RamificationTheory.HilbertRamification.ValuationSubring
