/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.CleanedRelators

/-!
# Reidemeister Schreier / Discrete / Reidemeister Schreier / Finite Quotient / Kernel

This module constructs the quotient homomorphisms induced by tau and proves
that the Schreier, quotient-section, and augmented relator families give the
required kernel-level maps.
-/


namespace ReidemeisterSchreier.Discrete

open ReidemeisterSchreier.Discrete.Presentations

variable {X Q : Type*} [Group Q] [Fintype Q]

namespace FiniteQuotientSchreierData

variable (D : FiniteQuotientSchreierData X Q)
variable [DecidableEq X]

/--
The \(\tau\)-map sends a kernel element to its class in the quotient by the Schreier relator
normal closure.
-/
noncomputable def tauKernelQuotientHom
    (R : Set (FreeGroup X)) :
    D.kernel →* FreeGroup (FiniteSchreierSymbol X Q) ⧸
      Subgroup.normalClosure (D.schreierRelators R) where
  toFun k :=
    QuotientGroup.mk'
      (Subgroup.normalClosure (D.schreierRelators R))
      (D.tau 1 (k : FreeGroup X))
  map_one' := by
    simp only [OneMemClass.coe_one, tau_one, QuotientGroup.mk'_apply, QuotientGroup.mk_one]
  map_mul' k l := by
    change
      QuotientGroup.mk'
          (Subgroup.normalClosure (D.schreierRelators R))
          (D.tau 1 ((k : FreeGroup X) * (l : FreeGroup X))) =
        QuotientGroup.mk'
          (Subgroup.normalClosure (D.schreierRelators R))
          (D.tau 1 (k : FreeGroup X)) *
        QuotientGroup.mk'
          (Subgroup.normalClosure (D.schreierRelators R))
          (D.tau 1 (l : FreeGroup X))
    rw [D.tau_mul_of_mem_kernel k.property]
    rfl

/--
The inverse-map candidate on the kernel for the raw presentation quotient, before descent
through the relator subgroup.
-/
noncomputable def tauKernelPresentationQuotientHom
    (R : Set (FreeGroup X)) :
    D.kernel →* FreeGroup (FiniteSchreierSymbol X Q) ⧸
      Subgroup.normalClosure (D.presentationRelators R) where
  toFun k :=
    QuotientGroup.mk'
      (Subgroup.normalClosure (D.presentationRelators R))
      (D.tau 1 (k : FreeGroup X))
  map_one' := by
    simp only [OneMemClass.coe_one, tau_one, QuotientGroup.mk'_apply, QuotientGroup.mk_one]
  map_mul' k l := by
    change
      QuotientGroup.mk'
          (Subgroup.normalClosure (D.presentationRelators R))
          (D.tau 1 ((k : FreeGroup X) * (l : FreeGroup X))) =
        QuotientGroup.mk'
          (Subgroup.normalClosure (D.presentationRelators R))
          (D.tau 1 (k : FreeGroup X)) *
        QuotientGroup.mk'
          (Subgroup.normalClosure (D.presentationRelators R))
          (D.tau 1 (l : FreeGroup X))
    rw [D.tau_mul_of_mem_kernel k.property]
    rfl

/--
The inverse-map candidate on the kernel for the augmented raw presentation quotient, before
descent through the relator subgroup.
-/
noncomputable def tauKernelAugmentedPresentationQuotientHom
    (R : Set (FreeGroup X)) :
    D.kernel →* FreeGroup (FiniteSchreierSymbol X Q) ⧸
      Subgroup.normalClosure (D.augmentedPresentationRelators R) where
  toFun k :=
    QuotientGroup.mk'
      (Subgroup.normalClosure (D.augmentedPresentationRelators R))
      (D.tau 1 (k : FreeGroup X))
  map_one' := by
    simp only [OneMemClass.coe_one, tau_one, QuotientGroup.mk'_apply, QuotientGroup.mk_one]
  map_mul' k l := by
    change
      QuotientGroup.mk'
          (Subgroup.normalClosure (D.augmentedPresentationRelators R))
          (D.tau 1 ((k : FreeGroup X) * (l : FreeGroup X))) =
        QuotientGroup.mk'
          (Subgroup.normalClosure (D.augmentedPresentationRelators R))
          (D.tau 1 (k : FreeGroup X)) *
        QuotientGroup.mk'
          (Subgroup.normalClosure (D.augmentedPresentationRelators R))
          (D.tau 1 (l : FreeGroup X))
    rw [D.tau_mul_of_mem_kernel k.property]
    rfl

/--
The \(\tau\)-rewrite of an original relator at a finite quotient state belongs to the
finite-quotient Schreier relator set.
-/
theorem tau_mem_schreierRelators
    {R : Set (FreeGroup X)} (q : Q) {r : FreeGroup X} (hr : r ∈ R) :
    D.tau q r ∈ D.schreierRelators R :=
  ⟨q, r, hr, rfl⟩

/-- The \(\tau\)-word of a kernel element belongs to the quotient-section relator set. -/
theorem tau_mem_quotientSectionRelators (q : Q) :
    D.tau 1 (D.quotientSection q) ∈ D.quotientSectionRelators :=
  ⟨q, rfl⟩

/--
Every finite-quotient presentation relator is included among the augmented presentation
relators.
-/
theorem presentationRelators_subset_augmentedPresentationRelators
    (R : Set (FreeGroup X)) :
    D.presentationRelators R ⊆ D.augmentedPresentationRelators R :=
  fun _ hq => Or.inl hq

/-- Every quotient-section relator is included among the augmented presentation relators. -/
theorem quotientSectionRelators_subset_augmentedPresentationRelators
    (R : Set (FreeGroup X)) :
    D.quotientSectionRelators ⊆ D.augmentedPresentationRelators R :=
  fun _ hq => Or.inr hq

end FiniteQuotientSchreierData

end ReidemeisterSchreier.Discrete
