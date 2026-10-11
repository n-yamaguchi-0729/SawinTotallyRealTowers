/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.PowerBasis

/-!
# Field Arithmetic, Definition 7.1.3: ring covers

The book's condition `S = R[z]` is recorded by the existence of a power basis.
The Galois condition is stated for the induced extension of fraction fields.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter07

universe u v

variable (R : Type u) (S : Type v)
variable [CommRing R] [CommRing S]
variable [Algebra R S]

/--
The algebraic part of the ring-cover condition in Fried--Jarden,
Definition 7.1.3.  The ambient hypotheses that `R` and `S` are integrally closed
domains are supplied where this predicate is used.
-/
def IsRingCover : Prop :=
  ∃ pb : PowerBasis R S, IsUnit (Algebra.discr R pb.basis)

/-- The extension of fraction fields induced by `R → S` is Galois. -/
def FractionExtensionIsGalois [IsDomain S] [FaithfulSMul R S] : Prop :=
  letI : IsDomain R := IsDomain.of_faithfulSMul R S
  letI : Algebra (FractionRing R) (FractionRing S) :=
    FractionRing.liftAlgebra R (FractionRing S)
  IsGalois (FractionRing R) (FractionRing S)

/-- The algebraic part of the Galois ring-cover condition in Definition 7.1.3. -/
def IsGaloisRingCover [IsDomain S] [FaithfulSMul R S] : Prop :=
  IsRingCover R S ∧ FractionExtensionIsGalois R S

end Chapter07
end FieldArithmetic
