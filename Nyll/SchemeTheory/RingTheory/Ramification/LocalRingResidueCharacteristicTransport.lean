/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.CharP.Algebra

/-!
# Residue characteristic under local-ring equivalences

Transports CharP and characteristic-zero instances between residue fields of isomorphic local
rings.
-/

namespace SchemeTheory

universe u v

theorem residueField_charP_of_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) (p : ℕ) [CharP (IsLocalRing.ResidueField R) p] :
    CharP (IsLocalRing.ResidueField S) p :=
  charP_of_injective_ringHom
    (f := (IsLocalRing.ResidueField.mapEquiv e).toRingHom)
    (IsLocalRing.ResidueField.mapEquiv e).injective p

theorem residueField_charZero_of_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) [CharZero (IsLocalRing.ResidueField R)] :
    CharZero (IsLocalRing.ResidueField S) :=
  charZero_of_injective_ringHom
    (f := (IsLocalRing.ResidueField.mapEquiv e).toRingHom)
    (IsLocalRing.ResidueField.mapEquiv e).injective

end SchemeTheory
