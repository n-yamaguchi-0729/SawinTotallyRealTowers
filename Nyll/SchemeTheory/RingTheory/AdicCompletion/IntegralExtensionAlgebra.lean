/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.CoprimeProduct

/-!
# Algebra compatibility of the integral-extension completion decomposition

The Chinese-remainder decomposition of a completed finite integral extension
is compatible with the canonical maps from the extension ring.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uB

variable {A : Type uA} [CommRing A] [IsDomain A]
variable {B : Type uB} [CommRing B] [IsDedekindDomain B]
variable [Algebra A B] [Algebra.IsIntegral A B]
variable [Module.IsTorsionFree A B] [Module.Finite A B]

/-- The decomposition of the completion of a finite integral extension as a
product of prime-power completions, as an equivalence of `B`-algebras. -/
noncomputable def adicCompletionIntegralExtensionAlgEquivPi
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥) :
    AdicCompletion (p.map (algebraMap A B)) B ≃ₐ[B]
      ∀ Q : p.primesOver B,
        AdicCompletion (Q.1 ^ Q.1.ramificationIdx A) B where
  toRingEquiv := adicCompletionIntegralExtensionEquivPi p hp
  commutes' x := by
    apply funext
    intro Q
    simp only [Pi.algebraMap_apply, AdicCompletion.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply]
    change adicCompletionIntegralExtensionEquivPi p hp
        (AdicCompletion.of (p.map (algebraMap A B)) B x) Q =
      AdicCompletion.of (Q.1 ^ Q.1.ramificationIdx A) B x
    exact adicCompletionIntegralExtensionEquivPi_of p hp x Q

/-- Primewise computation of the algebra equivalence on the canonical image
of an element of `B`. -/
@[simp]
theorem adicCompletionIntegralExtensionAlgEquivPi_of_apply
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥) (x : B)
    (Q : p.primesOver B) :
    adicCompletionIntegralExtensionAlgEquivPi p hp
        (AdicCompletion.of (p.map (algebraMap A B)) B x) Q =
      AdicCompletion.of (Q.1 ^ Q.1.ramificationIdx A) B x :=
  adicCompletionIntegralExtensionEquivPi_of p hp x Q

/-- Bundled algebra-map form of the primewise compatibility calculation. -/
@[simp]
theorem adicCompletionIntegralExtensionAlgEquivPi_algebraMap_apply
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥) (x : B)
    (Q : p.primesOver B) :
    adicCompletionIntegralExtensionAlgEquivPi p hp
        (algebraMap B (AdicCompletion (p.map (algebraMap A B)) B) x) Q =
      algebraMap B (AdicCompletion (Q.1 ^ Q.1.ramificationIdx A) B) x := by
  simp only [AdicCompletion.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply,
    adicCompletionIntegralExtensionAlgEquivPi_of_apply]

end EtaleFundamentalGroups

end
