/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.WordCertificates

/-!
# Reidemeister Schreier / Discrete / Reidemeister Schreier / Finite Quotient / Presentation

This module proves the normal-closure identities behind the finite-quotient
Reidemeister--Schreier presentation, including tau images of section words,
symbols, and conjugated original relators.
-/


namespace ReidemeisterSchreier.Discrete

open ReidemeisterSchreier.Discrete.Presentations

variable {X Q : Type*} [Group Q] [Fintype Q]

namespace FiniteQuotientSchreierData

variable (D : FiniteQuotientSchreierData X Q)
variable [DecidableEq X]

omit [DecidableEq X] in
/--
A list whose successive quotient states follow the chosen prefix-closed section rewrites into
the normal closure of the degenerate Schreier relators.
-/
theorem tauList_mem_normalClosure_degenerateSchreierRelators_of_prefixClosedAlongList
    {q : Q} {xs : List (X × Bool)}
    (hprefix : D.prefixClosedAlongList q xs) :
    D.tauList q xs ∈ Subgroup.normalClosure D.degenerateSchreierRelators := by
  induction xs generalizing q with
  | nil =>
      simp only [tauList, one_mem]
  | cons hd xs ih =>
      rcases hd with ⟨x, eps⟩
      cases eps
      · rcases hprefix with ⟨hstep, htail⟩
        have hgenerator :
            FreeGroup.of (D.inverseTransition q x, x) ∈ D.degenerateSchreierRelators := by
          refine ⟨D.inverseTransition q x, x, ?_, rfl⟩
          simpa [D.transition_after_inverseTransition q x] using hstep
        exact Subgroup.mul_mem (Subgroup.normalClosure D.degenerateSchreierRelators)
          (Subgroup.inv_mem _
            (Subgroup.subset_normalClosure hgenerator))
          (ih htail)
      · rcases hprefix with ⟨hstep, htail⟩
        have hgenerator :
            FreeGroup.of (q, x) ∈ D.degenerateSchreierRelators :=
          ⟨q, x, hstep, rfl⟩
        exact Subgroup.mul_mem (Subgroup.normalClosure D.degenerateSchreierRelators)
          (Subgroup.subset_normalClosure hgenerator)
          (ih htail)

/--
The \(\tau\)-rewrite of the indicated relator or section word belongs to the appropriate
Reidemeister--Schreier normal closure.
-/
theorem tau_quotientSection_mem_normalClosure_degenerateSchreierRelators_of_isPrefixClosed
    (hprefix : D.IsPrefixClosedQuotientSection) (q : Q) :
    D.tau 1 (D.quotientSection q) ∈
      Subgroup.normalClosure D.degenerateSchreierRelators := by
  simpa [tau] using
    D.tauList_mem_normalClosure_degenerateSchreierRelators_of_prefixClosedAlongList
      (hprefix q)

/--
The \(\tau\)-rewrite of the indicated relator or section word belongs to the appropriate
Reidemeister--Schreier normal closure.
-/
theorem tau_quotientSection_mem_normalClosure_presentationRelators_of_isPrefixClosed
    (R : Set (FreeGroup X))
    (hprefix : D.IsPrefixClosedQuotientSection) (q : Q) :
    D.tau 1 (D.quotientSection q) ∈
      Subgroup.normalClosure (D.presentationRelators R) :=
  Subgroup.normalClosure_mono
    (fun _ hq => Or.inr hq)
    (D.tau_quotientSection_mem_normalClosure_degenerateSchreierRelators_of_isPrefixClosed
      hprefix q)

/--
A quotient-section relator is relator-equivalent to the identity modulo the augmented
presentation relators.
-/
theorem quotientSectionRelator_relatorEquivalent_one
    (R : Set (FreeGroup X)) (q : Q) :
    RelatorEquivalent (D.augmentedPresentationRelators R)
      (D.tau 1 (D.quotientSection q)) 1 :=
  RelatorEquivalent.of_mem
    (D.quotientSectionRelators_subset_augmentedPresentationRelators R
      (D.tau_mem_quotientSectionRelators q))

/--
The \(\tau\)-word and its symbol evaluation are relator-equivalent modulo the augmented
presentation relators.
-/
theorem tau_symbolEval_relatorEquivalent_augmentedPresentationRelators
    (R : Set (FreeGroup X)) (q : Q) (x : X) :
    RelatorEquivalent (D.augmentedPresentationRelators R)
      (D.tau 1 (D.symbolEval (q, x))) (FreeGroup.of (q, x)) := by
  let S : Set (FreeGroup (FiniteSchreierSymbol X Q)) :=
    D.augmentedPresentationRelators R
  have htail :
      D.tau (D.transition q x) (D.quotientSection (D.transition q x))⁻¹ =
        (D.tau 1 (D.quotientSection (D.transition q x)))⁻¹ := by
    simpa [D.quotientSection_one] using
      D.tau_inv 1 (D.quotientSection (D.transition q x))
  have htail' :
      D.tau (q * D.quotientMap (FreeGroup.of x))
          (D.quotientSection (q * D.quotientMap (FreeGroup.of x)))⁻¹ =
        (D.tau 1
          (D.quotientSection (q * D.quotientMap (FreeGroup.of x))))⁻¹ := by
    simpa using htail
  have hdecomp :
      D.tau 1 (D.symbolEval (q, x)) =
        D.tau 1 (D.quotientSection q) * FreeGroup.of (q, x) *
          (D.tau 1 (D.quotientSection (D.transition q x)))⁻¹ := by
    calc
      D.tau 1 (D.symbolEval (q, x)) =
          D.tau 1
            (D.quotientSection q *
              (FreeGroup.of x * (D.quotientSection (D.transition q x))⁻¹)) := by
            simp only [symbolEval, schreierGenerator, transition_eq, mul_assoc]
      _ =
          D.tau 1 (D.quotientSection q) *
            D.tau (D.quotientMap (D.quotientSection 1 * D.quotientSection q))
              (FreeGroup.of x * (D.quotientSection (D.transition q x))⁻¹) := by
            rw [D.tau_mul]
      _ =
          D.tau 1 (D.quotientSection q) *
            D.tau q
              (FreeGroup.of x * (D.quotientSection (D.transition q x))⁻¹) := by
            simp only [D.quotientSection_one, one_mul, quotientMap_quotientSection_apply,
                transition_eq]
      _ =
          D.tau 1 (D.quotientSection q) *
            (D.tau q (FreeGroup.of x) *
              D.tau (D.quotientMap (D.quotientSection q * FreeGroup.of x))
                (D.quotientSection (D.transition q x))⁻¹) := by
            rw [D.tau_mul]
      _ =
          D.tau 1 (D.quotientSection q) * FreeGroup.of (q, x) *
            (D.tau 1 (D.quotientSection (D.transition q x)))⁻¹ := by
            simp only [tau_of, map_mul, quotientMap_quotientSection_apply, transition, htail',
                mul_assoc]
  have hleft :
      RelatorEquivalent S (D.tau 1 (D.quotientSection q)) 1 :=
    D.quotientSectionRelator_relatorEquivalent_one R q
  have hright :
      RelatorEquivalent S
        ((D.tau 1 (D.quotientSection (D.transition q x)))⁻¹) 1 := by
    simpa using
      RelatorEquivalent.inv
        (D.quotientSectionRelator_relatorEquivalent_one R (D.transition q x))
  have hmiddle :
      RelatorEquivalent S (FreeGroup.of (q, x)) (FreeGroup.of (q, x)) :=
    RelatorEquivalent.refl S (FreeGroup.of (q, x))
  have hprod :=
    RelatorEquivalent.mul (RelatorEquivalent.mul hleft hmiddle) hright
  rw [hdecomp]
  simpa [S, mul_assoc] using hprod

/--
The \(\tau\)-word and its symbol evaluation are relator-equivalent modulo the augmented
presentation relators.
-/
theorem tau_symbolEvalHom_relatorEquivalent_augmentedPresentationRelators
    (R : Set (FreeGroup X)) (z : FreeGroup (FiniteSchreierSymbol X Q)) :
    RelatorEquivalent (D.augmentedPresentationRelators R)
      (D.tau 1 (D.symbolEvalHom z)) z := by
  refine FreeGroup.induction_on z ?one ?of ?inv ?mul
  · exact RelatorEquivalent.refl (D.augmentedPresentationRelators R) 1
  · intro y
    rcases y with ⟨q, x⟩
    simpa using
      D.tau_symbolEval_relatorEquivalent_augmentedPresentationRelators R q x
  · intro y hy
    have hyK : D.symbolEval y ∈ D.kernel :=
      D.symbolEval_mem y
    have hinv :
        D.tau 1 (D.symbolEval y)⁻¹ =
          (D.tau 1 (D.symbolEval y))⁻¹ :=
      D.tau_inv_of_mem_kernel hyK
    simpa [map_inv, hinv] using RelatorEquivalent.inv hy
  · intro y z hy hz
    have hyK : D.symbolEvalHom y ∈ D.kernel :=
      D.symbolEvalHom_mem y
    have hmul :
        D.tau 1 (D.symbolEvalHom (y * z)) =
          D.tau 1 (D.symbolEvalHom y) * D.tau 1 (D.symbolEvalHom z) := by
      simpa [map_mul] using
        D.tau_mul_of_mem_kernel (v := D.symbolEvalHom z) hyK
    rw [hmul]
    exact RelatorEquivalent.mul hy hz

/--
The \(\tau\)-rewrite of the indicated relator or section word belongs to the appropriate
Reidemeister--Schreier normal closure.
-/
theorem tau_conjugate_relator_mem_normalClosure_schreierRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    (g : FreeGroup X) {r : FreeGroup X} (hr : r ∈ R) :
    D.tau 1 (g * r * g⁻¹) ∈
      Subgroup.normalClosure (D.schreierRelators R) := by
  have hrquot : D.quotientMap r = 1 := by
    simpa [kernel] using hR (Subgroup.subset_normalClosure hr)
  have hinv :
      D.tau (D.quotientMap g) g⁻¹ = (D.tau 1 g)⁻¹ := by
    simpa [D.quotientSection_one] using D.tau_inv 1 g
  have hdecomp :
      D.tau 1 (g * r * g⁻¹) =
        D.tau 1 g * D.tau (D.quotientMap g) r * (D.tau 1 g)⁻¹ := by
    rw [mul_assoc]
    rw [D.tau_mul 1 g (r * g⁻¹)]
    rw [D.tau_mul (D.quotientMap (D.quotientSection 1 * g)) r g⁻¹]
    simp only [D.quotientSection_one, one_mul, map_mul, quotientMap_quotientSection_apply,
        hrquot, mul_one, hinv,
  mul_assoc]
  have hrel :
      D.tau (D.quotientMap g) r ∈
        Subgroup.normalClosure (D.schreierRelators R) :=
    Subgroup.subset_normalClosure
      (D.tau_mem_schreierRelators (D.quotientMap g) hr)
  have hconj :
      D.tau 1 g * D.tau (D.quotientMap g) r * (D.tau 1 g)⁻¹ ∈
        Subgroup.normalClosure (D.schreierRelators R) :=
    conjugate_mem_normalClosure
      (R := D.schreierRelators R) hrel (D.tau 1 g)
  simpa [hdecomp] using hconj

/--
The \(\tau\)-rewrite of the indicated relator or section word belongs to the appropriate
Reidemeister--Schreier normal closure.
-/
theorem tau_conjugate_relator_mem_normalClosure_presentationRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    (g : FreeGroup X) {r : FreeGroup X} (hr : r ∈ R) :
    D.tau 1 (g * r * g⁻¹) ∈
      Subgroup.normalClosure (D.presentationRelators R) :=
  Subgroup.normalClosure_mono
    (fun _ hq => Or.inl hq)
    (D.tau_conjugate_relator_mem_normalClosure_schreierRelators hR g hr)

/--
The \(\tau\)-rewrite of the indicated relator or section word belongs to the appropriate
Reidemeister--Schreier normal closure.
-/
theorem tau_conjugate_relator_mem_normalClosure_augmentedPresentationRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    (g : FreeGroup X) {r : FreeGroup X} (hr : r ∈ R) :
    D.tau 1 (g * r * g⁻¹) ∈
      Subgroup.normalClosure (D.augmentedPresentationRelators R) :=
  Subgroup.normalClosure_mono
    (D.presentationRelators_subset_augmentedPresentationRelators R)
    (D.tau_conjugate_relator_mem_normalClosure_presentationRelators hR g hr)

/--
The \(\tau\)-homomorphism to the presentation-relator quotient kills every element of the normal
closure of the original relators.
-/
theorem tauKernelPresentationQuotientHom_eq_one_of_mem_normalClosure
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    {n : FreeGroup X} (hn : n ∈ Subgroup.normalClosure R) :
    D.tauKernelPresentationQuotientHom R ⟨n, hR hn⟩ = 1 := by
  let killedSubgroup : Subgroup (FreeGroup X) :=
    { carrier :=
        {n | ∃ hnK : n ∈ D.kernel,
          D.tauKernelPresentationQuotientHom R ⟨n, hnK⟩ = 1}
      one_mem' := by
        refine ⟨D.kernel.one_mem, ?_⟩
        change (D.tauKernelPresentationQuotientHom R) (1 : D.kernel) = 1
        exact (D.tauKernelPresentationQuotientHom R).map_one
      mul_mem' := by
        intro a b ha hb
        rcases ha with ⟨haK, haone⟩
        rcases hb with ⟨hbK, hbone⟩
        refine ⟨D.kernel.mul_mem haK hbK, ?_⟩
        have hmul :=
          (D.tauKernelPresentationQuotientHom R).map_mul
            ⟨a, haK⟩ ⟨b, hbK⟩
        simpa [haone, hbone] using hmul
      inv_mem' := by
        intro a ha
        rcases ha with ⟨haK, haone⟩
        refine ⟨D.kernel.inv_mem haK, ?_⟩
        change
          (D.tauKernelPresentationQuotientHom R) (⟨a, haK⟩ : D.kernel)⁻¹ = 1
        rw [(D.tauKernelPresentationQuotientHom R).map_inv, haone]
        simp only [inv_one]}
  have hclosure : Subgroup.normalClosure R ≤ killedSubgroup := by
    rw [Subgroup.normalClosure]
    rw [Subgroup.closure_le]
    intro x hx
    have hxN : x ∈ Subgroup.normalClosure R :=
      Subgroup.conjugatesOfSet_subset_normalClosure hx
    refine ⟨hR hxN, ?_⟩
    change
      QuotientGroup.mk'
          (Subgroup.normalClosure (D.presentationRelators R))
          (D.tau 1 x) = 1
    rcases Group.mem_conjugatesOfSet_iff.1 hx with ⟨r, hr, hconj⟩
    rcases isConj_iff.1 hconj with ⟨g, rfl⟩
    exact (QuotientGroup.eq_one_iff
      (N := Subgroup.normalClosure (D.presentationRelators R))
      (D.tau 1 (g * r * g⁻¹))).2
      (D.tau_conjugate_relator_mem_normalClosure_presentationRelators hR g hr)
  rcases hclosure hn with ⟨hnK, hone⟩
  simpa using hone

/--
The \(\tau\)-map descends from the kernel's relator-subgroup quotient to the quotient by the
finite Schreier presentation relators.
-/
noncomputable def tauRelatorSubgroupPresentationQuotientHom
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    D.kernel ⧸ D.relatorSubgroup R →*
      FreeGroup (FiniteSchreierSymbol X Q) ⧸
        Subgroup.normalClosure (D.presentationRelators R) :=
  QuotientGroup.lift
    (D.relatorSubgroup R)
    (D.tauKernelPresentationQuotientHom R)
    (by
      intro k hk
      rw [MonoidHom.mem_ker]
      change (D.tauKernelPresentationQuotientHom R) k = 1
      have hk' : (k : FreeGroup X) ∈ Subgroup.normalClosure R := hk
      simpa using
        (D.tauKernelPresentationQuotientHom_eq_one_of_mem_normalClosure hR hk'))

/--
The \(\tau\)-homomorphism to the augmented-presentation quotient kills every element of the
normal closure of the original relators.
-/
theorem tauKernelAugmentedPresentationQuotientHom_eq_one_of_mem_normalClosure
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    {n : FreeGroup X} (hn : n ∈ Subgroup.normalClosure R) :
    D.tauKernelAugmentedPresentationQuotientHom R ⟨n, hR hn⟩ = 1 := by
  let killedSubgroup : Subgroup (FreeGroup X) :=
    { carrier :=
        {n | ∃ hnK : n ∈ D.kernel,
          D.tauKernelAugmentedPresentationQuotientHom R ⟨n, hnK⟩ = 1}
      one_mem' := by
        refine ⟨D.kernel.one_mem, ?_⟩
        change (D.tauKernelAugmentedPresentationQuotientHom R) (1 : D.kernel) = 1
        exact (D.tauKernelAugmentedPresentationQuotientHom R).map_one
      mul_mem' := by
        intro a b ha hb
        rcases ha with ⟨haK, haone⟩
        rcases hb with ⟨hbK, hbone⟩
        refine ⟨D.kernel.mul_mem haK hbK, ?_⟩
        have hmul :=
          (D.tauKernelAugmentedPresentationQuotientHom R).map_mul
            ⟨a, haK⟩ ⟨b, hbK⟩
        simpa [haone, hbone] using hmul
      inv_mem' := by
        intro a ha
        rcases ha with ⟨haK, haone⟩
        refine ⟨D.kernel.inv_mem haK, ?_⟩
        change
          (D.tauKernelAugmentedPresentationQuotientHom R) (⟨a, haK⟩ : D.kernel)⁻¹ = 1
        rw [(D.tauKernelAugmentedPresentationQuotientHom R).map_inv, haone]
        simp only [inv_one]}
  have hclosure : Subgroup.normalClosure R ≤ killedSubgroup := by
    rw [Subgroup.normalClosure]
    rw [Subgroup.closure_le]
    intro x hx
    have hxN : x ∈ Subgroup.normalClosure R :=
      Subgroup.conjugatesOfSet_subset_normalClosure hx
    refine ⟨hR hxN, ?_⟩
    change
      QuotientGroup.mk'
          (Subgroup.normalClosure (D.augmentedPresentationRelators R))
          (D.tau 1 x) = 1
    rcases Group.mem_conjugatesOfSet_iff.1 hx with ⟨r, hr, hconj⟩
    rcases isConj_iff.1 hconj with ⟨g, rfl⟩
    exact (QuotientGroup.eq_one_iff
      (N := Subgroup.normalClosure (D.augmentedPresentationRelators R))
      (D.tau 1 (g * r * g⁻¹))).2
      (D.tau_conjugate_relator_mem_normalClosure_augmentedPresentationRelators hR g hr)
  rcases hclosure hn with ⟨hnK, hone⟩
  simpa using hone

/--
The \(\tau\)-map descends from the relator-subgroup quotient to the augmented Schreier
presentation quotient.
-/
noncomputable def tauRelatorSubgroupAugmentedPresentationQuotientHom
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    D.kernel ⧸ D.relatorSubgroup R →*
      FreeGroup (FiniteSchreierSymbol X Q) ⧸
        Subgroup.normalClosure (D.augmentedPresentationRelators R) :=
  QuotientGroup.lift
    (D.relatorSubgroup R)
    (D.tauKernelAugmentedPresentationQuotientHom R)
    (by
      intro k hk
      rw [MonoidHom.mem_ker]
      change (D.tauKernelAugmentedPresentationQuotientHom R) k = 1
      have hk' : (k : FreeGroup X) ∈ Subgroup.normalClosure R := hk
      simpa using
        (D.tauKernelAugmentedPresentationQuotientHom_eq_one_of_mem_normalClosure hR hk'))

omit [DecidableEq X] in
/--
Every degenerate finite-quotient Schreier relator evaluates to the identity under the finite
Schreier evaluation map.
-/
theorem degenerateSchreierRelator_eval_eq_one
    {q : FreeGroup (FiniteSchreierSymbol X Q)}
    (hq : q ∈ D.degenerateSchreierRelators) :
    D.symbolEvalHom q = 1 := by
  rcases hq with ⟨s, x, hsx, rfl⟩
  have hsx' :
      D.quotientSection (s * D.quotientMap (FreeGroup.of x)) =
        D.quotientSection s * FreeGroup.of x := by
    simpa [transition] using hsx
  simp only [symbolEvalHom_of, symbolEval, schreierGenerator, transition_eq, hsx', mul_inv_rev]
  group

omit [DecidableEq X] in
/--
If the relator normal closure is contained in the kernel, the quotient map sends each relator to
\(1\).
-/
theorem quotientMap_relator_eq_one_of_normalClosure_le_kernel
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    {r : FreeGroup X} (hr : r ∈ R) :
    D.quotientMap r = 1 :=
  hR (Subgroup.subset_normalClosure hr)

omit [DecidableEq X] in
/--
Multiplying a quotient section by an original relator has the same quotient-map value as the
quotient section.
-/
theorem quotientMap_quotientSection_mul_relator
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    (q : Q) {r : FreeGroup X} (hr : r ∈ R) :
    D.quotientMap (D.quotientSection q * r) = q := by
  simp only [map_mul, quotientMap_quotientSection_apply,
  quotientMap_relator_eq_one_of_normalClosure_le_kernel (D := D) hR hr, mul_one]

/--
The evaluated \(\tau\)-word of an original relator lies in the normal closure of the original
relators.
-/
theorem eval_tau_relator_mem_normalClosure
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    (q : Q) {r : FreeGroup X} (hr : r ∈ R) :
    D.symbolEvalHom (D.tau q r) ∈ Subgroup.normalClosure R := by
  have hquot := quotientMap_quotientSection_mul_relator (D := D) hR q hr
  have hconj :
      D.quotientSection q * r * (D.quotientSection q)⁻¹ ∈
        Subgroup.normalClosure R :=
    conjugate_mem_normalClosure_of_mem (R := R) hr (D.quotientSection q)
  simpa [symbolEvalHom_tau, hquot, mul_assoc] using hconj

/--
Evaluating a finite-quotient Schreier relator gives an element of the normal closure of the
original relators.
-/
theorem eval_schreierRelator_mem_normalClosure
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    {q : FreeGroup (FiniteSchreierSymbol X Q)}
    (hq : q ∈ D.schreierRelators R) :
    D.symbolEvalHom q ∈ Subgroup.normalClosure R := by
  rcases hq with ⟨s, r, hr, rfl⟩
  exact eval_tau_relator_mem_normalClosure (D := D) hR s hr

/--
Membership in the source relator normal closure is preserved by the Reidemeister--Schreier
evaluation map.
-/
theorem eval_mem_normalClosure_of_mem_normalClosure_schreierRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    {q : FreeGroup (FiniteSchreierSymbol X Q)}
    (hq : q ∈ Subgroup.normalClosure (D.schreierRelators R)) :
    D.symbolEvalHom q ∈ Subgroup.normalClosure R :=
  map_mem_normalClosure_of_relators D.symbolEvalHom
    (fun _ hr => eval_schreierRelator_mem_normalClosure (D := D) hR hr) hq

omit [DecidableEq X] in
/--
The evaluation of a degenerate finite-quotient Schreier relator lies in the normal closure of
the finite-quotient presentation relators.
-/
theorem eval_degenerateSchreierRelator_mem_normalClosure
    {R : Set (FreeGroup X)}
    {q : FreeGroup (FiniteSchreierSymbol X Q)}
    (hq : q ∈ D.degenerateSchreierRelators) :
    D.symbolEvalHom q ∈ Subgroup.normalClosure R := by
  simp only [degenerateSchreierRelator_eval_eq_one (D := D) hq, one_mem]

/--
Evaluating a finite-quotient presentation relator gives an element of the normal closure of the
original relators.
-/
theorem eval_presentationRelator_mem_normalClosure
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    {q : FreeGroup (FiniteSchreierSymbol X Q)}
    (hq : q ∈ D.presentationRelators R) :
    D.symbolEvalHom q ∈ Subgroup.normalClosure R := by
  rcases hq with hq | hq
  · exact eval_schreierRelator_mem_normalClosure (D := D) hR hq
  · exact eval_degenerateSchreierRelator_mem_normalClosure (D := D) hq

/-- The symbol evaluation of a quotient-section relator is the identity. -/
theorem quotientSectionRelator_eval_eq_one
    {q : FreeGroup (FiniteSchreierSymbol X Q)}
    (hq : q ∈ D.quotientSectionRelators) :
    D.symbolEvalHom q = 1 := by
  rcases hq with ⟨s, rfl⟩
  rw [symbolEvalHom_tau]
  simp only [D.quotientSection_one, one_mul, quotientMap_quotientSection_apply, mul_inv_cancel]

/--
The indicated evaluated relator belongs to the normal closure supplied by the
Reidemeister--Schreier relator comparison.
-/
theorem eval_quotientSectionRelator_mem_normalClosure
    {R : Set (FreeGroup X)}
    {q : FreeGroup (FiniteSchreierSymbol X Q)}
    (hq : q ∈ D.quotientSectionRelators) :
    D.symbolEvalHom q ∈ Subgroup.normalClosure R := by
  simp only [D.quotientSectionRelator_eval_eq_one hq, one_mem]

/--
The indicated evaluated relator belongs to the normal closure supplied by the
Reidemeister--Schreier relator comparison.
-/
theorem eval_augmentedPresentationRelator_mem_normalClosure
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    {q : FreeGroup (FiniteSchreierSymbol X Q)}
    (hq : q ∈ D.augmentedPresentationRelators R) :
    D.symbolEvalHom q ∈ Subgroup.normalClosure R := by
  rcases hq with hq | hq
  · exact eval_presentationRelator_mem_normalClosure (D := D) hR hq
  · exact eval_quotientSectionRelator_mem_normalClosure (D := D) hq

/--
Membership in the source relator normal closure is preserved by the Reidemeister--Schreier
evaluation map.
-/
theorem eval_mem_normalClosure_of_mem_normalClosure_presentationRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    {q : FreeGroup (FiniteSchreierSymbol X Q)}
    (hq : q ∈ Subgroup.normalClosure (D.presentationRelators R)) :
    D.symbolEvalHom q ∈ Subgroup.normalClosure R :=
  map_mem_normalClosure_of_relators D.symbolEvalHom
    (fun _ hr => eval_presentationRelator_mem_normalClosure (D := D) hR hr) hq

/--
Membership in the source relator normal closure is preserved by the Reidemeister--Schreier
evaluation map.
-/
theorem eval_mem_normalClosure_of_mem_normalClosure_augmentedPresentationRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    {q : FreeGroup (FiniteSchreierSymbol X Q)}
    (hq : q ∈ Subgroup.normalClosure (D.augmentedPresentationRelators R)) :
    D.symbolEvalHom q ∈ Subgroup.normalClosure R :=
  map_mem_normalClosure_of_relators D.symbolEvalHom
    (fun _ hr => eval_augmentedPresentationRelator_mem_normalClosure (D := D) hR hr) hq

/--
The symbol-evaluation subgroup homomorphism sends the indicated normal-closure element into the
relator subgroup.
-/
theorem symbolEvalSubgroupHom_mem_relatorSubgroup_of_mem_normalClosure_schreierRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    {q : FreeGroup (FiniteSchreierSymbol X Q)}
    (hq : q ∈ Subgroup.normalClosure (D.schreierRelators R)) :
    D.symbolEvalSubgroupHom q ∈ D.relatorSubgroup R := by
  change D.symbolEvalHom q ∈ Subgroup.normalClosure R
  exact eval_mem_normalClosure_of_mem_normalClosure_schreierRelators (D := D) hR hq

/--
The symbol-evaluation subgroup homomorphism sends the indicated normal-closure element into the
relator subgroup.
-/
theorem symbolEvalSubgroupHom_mem_relatorSubgroup_of_mem_normalClosure_presentationRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    {q : FreeGroup (FiniteSchreierSymbol X Q)}
    (hq : q ∈ Subgroup.normalClosure (D.presentationRelators R)) :
    D.symbolEvalSubgroupHom q ∈ D.relatorSubgroup R := by
  change D.symbolEvalHom q ∈ Subgroup.normalClosure R
  exact eval_mem_normalClosure_of_mem_normalClosure_presentationRelators (D := D) hR hq

/--
A word in the normal closure of augmented presentation relators evaluates into the relator
subgroup.
-/
theorem symbolEvalSubgroupHom_mem_relatorSubgroup_of_mem_normalClosure
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    {q : FreeGroup (FiniteSchreierSymbol X Q)}
    (hq : q ∈ Subgroup.normalClosure (D.augmentedPresentationRelators R)) :
    D.symbolEvalSubgroupHom q ∈ D.relatorSubgroup R := by
  change D.symbolEvalHom q ∈ Subgroup.normalClosure R
  exact eval_mem_normalClosure_of_mem_normalClosure_augmentedPresentationRelators (D := D) hR hq

/--
The canonical map from the finite Schreier-relator quotient to the kernel modulo its
intersection with the normal closure of \(R\).
-/
noncomputable def symbolEvalQuotientHom
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    FreeGroup (FiniteSchreierSymbol X Q) ⧸
        Subgroup.normalClosure (D.schreierRelators R) →*
      D.kernel ⧸ D.relatorSubgroup R :=
  QuotientGroup.lift
    (Subgroup.normalClosure (D.schreierRelators R))
    ((QuotientGroup.mk' (D.relatorSubgroup R)).comp
      D.symbolEvalSubgroupHom)
    (by
      intro q hq
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff
        (N := D.relatorSubgroup R)
        (D.symbolEvalSubgroupHom q)).2
        (symbolEvalSubgroupHom_mem_relatorSubgroup_of_mem_normalClosure_schreierRelators
          (D := D) hR hq))

/--
Evaluating the \(\tau\)-image of a kernel element recovers its class in the corresponding
relator quotient.
-/
theorem symbolEvalQuotientHom_tauKernelQuotientHom
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    (k : D.kernel) :
    D.symbolEvalQuotientHom hR (D.tauKernelQuotientHom R k) =
      QuotientGroup.mk' (D.relatorSubgroup R) k := by
  change D.symbolEvalQuotientHom hR
      (QuotientGroup.mk'
        (Subgroup.normalClosure (D.schreierRelators R))
        (D.tau 1 (k : FreeGroup X))) =
    QuotientGroup.mk' (D.relatorSubgroup R) k
  simp only [symbolEvalQuotientHom, QuotientGroup.mk'_apply, QuotientGroup.lift_mk,
      MonoidHom.coe_comp,
  QuotientGroup.coe_mk', Function.comp_apply]
  have hsub :
      D.symbolEvalSubgroupHom (D.tau 1 (k : FreeGroup X)) = k :=
    Subtype.ext (D.symbolEvalHom_tau_of_mem_kernel k.property)
  simpa using congrArg (QuotientGroup.mk' (D.relatorSubgroup R)) hsub

/-- The Schreier-relator quotient evaluation map is surjective. -/
theorem symbolEvalQuotientHom_surjective
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    Function.Surjective (D.symbolEvalQuotientHom hR) := by
  intro y
  rcases QuotientGroup.mk'_surjective (D.relatorSubgroup R) y with ⟨l, rfl⟩
  exact ⟨D.tauKernelQuotientHom R l,
    D.symbolEvalQuotientHom_tauKernelQuotientHom hR l⟩

/--
The canonical map from the raw finite Reidemeister--Schreier presentation quotient to the kernel
modulo its intersection with the normal closure of \(R\).
-/
noncomputable def symbolEvalPresentationQuotientHom
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    FreeGroup (FiniteSchreierSymbol X Q) ⧸
        Subgroup.normalClosure (D.presentationRelators R) →*
      D.kernel ⧸ D.relatorSubgroup R :=
  QuotientGroup.lift
    (Subgroup.normalClosure (D.presentationRelators R))
    ((QuotientGroup.mk' (D.relatorSubgroup R)).comp
      D.symbolEvalSubgroupHom)
    (by
      intro q hq
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff
        (N := D.relatorSubgroup R)
        (D.symbolEvalSubgroupHom q)).2
        (symbolEvalSubgroupHom_mem_relatorSubgroup_of_mem_normalClosure_presentationRelators
          (D := D) hR hq))

/--
The evaluation map from the augmented finite Reidemeister--Schreier presentation quotient to the
relator-subgroup quotient of the kernel.
-/
noncomputable def symbolEvalAugmentedPresentationQuotientHom
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    FreeGroup (FiniteSchreierSymbol X Q) ⧸
        Subgroup.normalClosure (D.augmentedPresentationRelators R) →*
      D.kernel ⧸ D.relatorSubgroup R :=
  QuotientGroup.lift
    (Subgroup.normalClosure (D.augmentedPresentationRelators R))
    ((QuotientGroup.mk' (D.relatorSubgroup R)).comp
      D.symbolEvalSubgroupHom)
    (by
      intro q hq
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff
        (N := D.relatorSubgroup R)
        (D.symbolEvalSubgroupHom q)).2
        (symbolEvalSubgroupHom_mem_relatorSubgroup_of_mem_normalClosure
          (D := D) hR hq))

/--
Evaluating the \(\tau\)-image of a kernel element recovers its class in the corresponding
relator quotient.
-/
theorem symbolEvalPresentationQuotientHom_tauKernelPresentationQuotientHom
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    (k : D.kernel) :
    D.symbolEvalPresentationQuotientHom hR
        (D.tauKernelPresentationQuotientHom R k) =
      QuotientGroup.mk' (D.relatorSubgroup R) k := by
  change D.symbolEvalPresentationQuotientHom hR
      (QuotientGroup.mk'
        (Subgroup.normalClosure (D.presentationRelators R))
        (D.tau 1 (k : FreeGroup X))) =
    QuotientGroup.mk' (D.relatorSubgroup R) k
  simp only [symbolEvalPresentationQuotientHom, QuotientGroup.mk'_apply, QuotientGroup.lift_mk,
  MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply]
  have hsub :
      D.symbolEvalSubgroupHom (D.tau 1 (k : FreeGroup X)) = k :=
    Subtype.ext (D.symbolEvalHom_tau_of_mem_kernel k.property)
  simpa using congrArg (QuotientGroup.mk' (D.relatorSubgroup R)) hsub

/-- The symbol-evaluation map is inverse to the \(\tau\)-map on the relator-subgroup quotient. -/
theorem symbolEvalPresentationQuotientHom_tauRelatorSubgroupPresentationQuotientHom
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    (y : D.kernel ⧸ D.relatorSubgroup R) :
    D.symbolEvalPresentationQuotientHom hR
        (D.tauRelatorSubgroupPresentationQuotientHom hR y) = y := by
  rcases QuotientGroup.mk'_surjective (D.relatorSubgroup R) y with ⟨k, rfl⟩
  simpa [tauRelatorSubgroupPresentationQuotientHom] using
    D.symbolEvalPresentationQuotientHom_tauKernelPresentationQuotientHom hR k

/--
Evaluating the \(\tau\)-image of a kernel element recovers its class in the corresponding
relator quotient.
-/
theorem symbolEvalAugmentedPresentationQuotientHom_tauKernelAugmentedPresentationQuotientHom
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    (k : D.kernel) :
    D.symbolEvalAugmentedPresentationQuotientHom hR
        (D.tauKernelAugmentedPresentationQuotientHom R k) =
      QuotientGroup.mk' (D.relatorSubgroup R) k := by
  change D.symbolEvalAugmentedPresentationQuotientHom hR
      (QuotientGroup.mk'
        (Subgroup.normalClosure (D.augmentedPresentationRelators R))
        (D.tau 1 (k : FreeGroup X))) =
    QuotientGroup.mk' (D.relatorSubgroup R) k
  simp only [symbolEvalAugmentedPresentationQuotientHom, QuotientGroup.mk'_apply,
      QuotientGroup.lift_mk,
  MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply]
  have hsub :
      D.symbolEvalSubgroupHom (D.tau 1 (k : FreeGroup X)) = k :=
    Subtype.ext (D.symbolEvalHom_tau_of_mem_kernel k.property)
  simpa using congrArg (QuotientGroup.mk' (D.relatorSubgroup R)) hsub

/--
Evaluating after the \(\tau\)-relator quotient map returns the original relator quotient class.
-/
theorem symbolEvalQuotHom_tauRelatorQuotHom
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    (y : D.kernel ⧸ D.relatorSubgroup R) :
    D.symbolEvalAugmentedPresentationQuotientHom hR
        (D.tauRelatorSubgroupAugmentedPresentationQuotientHom hR y) = y := by
  rcases QuotientGroup.mk'_surjective (D.relatorSubgroup R) y with ⟨k, rfl⟩
  simpa [tauRelatorSubgroupAugmentedPresentationQuotientHom] using
    D.symbolEvalAugmentedPresentationQuotientHom_tauKernelAugmentedPresentationQuotientHom hR k

/--
Applying the \(\tau\)-relator quotient map after symbol evaluation returns the original
augmented presentation quotient class.
-/
theorem tauRelatorQuotHom_symbolEvalQuotHom
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    (y : FreeGroup (FiniteSchreierSymbol X Q) ⧸
        Subgroup.normalClosure (D.augmentedPresentationRelators R)) :
    D.tauRelatorSubgroupAugmentedPresentationQuotientHom hR
        (D.symbolEvalAugmentedPresentationQuotientHom hR y) = y := by
  rcases QuotientGroup.mk'_surjective
      (Subgroup.normalClosure (D.augmentedPresentationRelators R)) y with ⟨z, rfl⟩
  change D.tauRelatorSubgroupAugmentedPresentationQuotientHom hR
      (QuotientGroup.mk' (D.relatorSubgroup R)
        (D.symbolEvalSubgroupHom z)) =
    QuotientGroup.mk'
      (Subgroup.normalClosure (D.augmentedPresentationRelators R)) z
  simp only [tauRelatorSubgroupAugmentedPresentationQuotientHom, QuotientGroup.mk'_apply,
      QuotientGroup.lift_mk]
  exact relatorEquivalent_iff_eq_in_presentedQuotient.1
    (D.tau_symbolEvalHom_relatorEquivalent_augmentedPresentationRelators R z)

/--
The augmented finite Schreier presentation quotient is equivalent to the kernel relator
quotient.
-/
noncomputable def augmentedPresentationQuotientEquiv
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    FreeGroup (FiniteSchreierSymbol X Q) ⧸
        Subgroup.normalClosure (D.augmentedPresentationRelators R) ≃*
      D.kernel ⧸ D.relatorSubgroup R where
  toFun := D.symbolEvalAugmentedPresentationQuotientHom hR
  invFun := D.tauRelatorSubgroupAugmentedPresentationQuotientHom hR
  left_inv :=
    D.tauRelatorQuotHom_symbolEvalQuotHom hR
  right_inv :=
    D.symbolEvalQuotHom_tauRelatorQuotHom hR
  map_mul' x y := (D.symbolEvalAugmentedPresentationQuotientHom hR).map_mul x y

/-- The augmented finite Schreier presented group is equivalent to the kernel relator quotient. -/
noncomputable def augmentedPresentedGroupEquiv
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    PresentedGroup (D.augmentedPresentationRelators R) ≃*
      D.kernel ⧸ D.relatorSubgroup R :=
  D.augmentedPresentationQuotientEquiv hR

/--
The augmented-presentation relator normal closure equals the normal closure generated by the
corresponding Reidemeister--Schreier relators.
-/
theorem normalClosure_augmentedPresentationRelators_eq
    {R : Set (FreeGroup X)}
    (hsection :
      ∀ q : Q,
        D.tau 1 (D.quotientSection q) ∈
          Subgroup.normalClosure (D.presentationRelators R)) :
    Subgroup.normalClosure (D.augmentedPresentationRelators R) =
      Subgroup.normalClosure (D.presentationRelators R) := by
  apply normalClosure_eq_of_subset_normalClosure
  · intro q hq
    rcases hq with hq | hq
    · exact Subgroup.subset_normalClosure hq
    · rcases hq with ⟨s, rfl⟩
      exact hsection s
  · intro q hq
    exact Subgroup.subset_normalClosure (Or.inl hq)

/--
The augmented-presentation relator normal closure equals the normal closure generated by the
corresponding Reidemeister--Schreier relators.
-/
theorem normalClosure_augmentedPresentationRelators_eq_of_isPrefixClosed
    {R : Set (FreeGroup X)}
    (hprefix : D.IsPrefixClosedQuotientSection) :
    Subgroup.normalClosure (D.augmentedPresentationRelators R) =
      Subgroup.normalClosure (D.presentationRelators R) :=
  D.normalClosure_augmentedPresentationRelators_eq
    (fun q =>
      D.tau_quotientSection_mem_normalClosure_presentationRelators_of_isPrefixClosed
        R hprefix q)

/--
After adding quotient-section relators, the finite Schreier presentation quotient is equivalent
to the kernel relator quotient.
-/
noncomputable def presentationQuotientEquivOfQuotientSectionRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    (hsection :
      ∀ q : Q,
        D.tau 1 (D.quotientSection q) ∈
          Subgroup.normalClosure (D.presentationRelators R)) :
    FreeGroup (FiniteSchreierSymbol X Q) ⧸
        Subgroup.normalClosure (D.presentationRelators R) ≃*
      D.kernel ⧸ D.relatorSubgroup R :=
  (QuotientGroup.congr
    (Subgroup.normalClosure (D.presentationRelators R))
    (Subgroup.normalClosure (D.augmentedPresentationRelators R))
    (MulEquiv.refl (FreeGroup (FiniteSchreierSymbol X Q)))
    (by
      simpa using (D.normalClosure_augmentedPresentationRelators_eq hsection).symm)).trans
    (D.augmentedPresentationQuotientEquiv hR)

/--
After adding quotient-section relators, the finite Schreier presented group is equivalent to the
kernel quotient.
-/
noncomputable def presentationPresentedGroupEquivOfQuotientSectionRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    (hsection :
      ∀ q : Q,
        D.tau 1 (D.quotientSection q) ∈
          Subgroup.normalClosure (D.presentationRelators R)) :
    PresentedGroup (D.presentationRelators R) ≃*
      D.kernel ⧸ D.relatorSubgroup R :=
  D.presentationQuotientEquivOfQuotientSectionRelators hR hsection

/--
For a prefix-closed quotient section, the finite Schreier presentation quotient is equivalent to
the kernel relator quotient.
-/
noncomputable def presentationQuotientEquivOfIsPrefixClosedQuotientSection
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    (hprefix : D.IsPrefixClosedQuotientSection) :
    FreeGroup (FiniteSchreierSymbol X Q) ⧸
        Subgroup.normalClosure (D.presentationRelators R) ≃*
      D.kernel ⧸ D.relatorSubgroup R :=
  D.presentationQuotientEquivOfQuotientSectionRelators hR
    (fun q =>
      D.tau_quotientSection_mem_normalClosure_presentationRelators_of_isPrefixClosed
        R hprefix q)

/--
For a prefix-closed quotient section, the finite Schreier presented group is equivalent to the
kernel quotient.
-/
noncomputable def presentationPresentedGroupEquivOfIsPrefixClosedQuotientSection
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel)
    (hprefix : D.IsPrefixClosedQuotientSection) :
    PresentedGroup (D.presentationRelators R) ≃*
      D.kernel ⧸ D.relatorSubgroup R :=
  D.presentationQuotientEquivOfIsPrefixClosedQuotientSection hR hprefix

/--
The presented group using the finite augmented relator finset is equivalent to the kernel
relator quotient.
-/
noncomputable def augmentedPresentationRelatorFinsetPresentedGroupEquiv [Fintype X]
    (R : Finset (FreeGroup X))
    (hR : Subgroup.normalClosure ({r | r ∈ R} : Set (FreeGroup X)) ≤ D.kernel) :
    PresentedGroup
        ({z | z ∈ D.augmentedPresentationRelatorFinset R} :
          Set (FreeGroup (FiniteSchreierSymbol X Q))) ≃*
      D.kernel ⧸ D.relatorSubgroup ({r | r ∈ R} : Set (FreeGroup X)) :=
  (QuotientGroup.congr
    (Subgroup.normalClosure
      ({z | z ∈ D.augmentedPresentationRelatorFinset R} :
        Set (FreeGroup (FiniteSchreierSymbol X Q))))
    (Subgroup.normalClosure
      (D.augmentedPresentationRelators ({r | r ∈ R} : Set (FreeGroup X))))
    (MulEquiv.refl (FreeGroup (FiniteSchreierSymbol X Q)))
    (by
      rw [D.coe_augmentedPresentationRelatorFinset R]
      simp only [MulEquiv.toMonoidHom_refl, SetLike.setOfPred_mem_eq, Subgroup.map_id])).trans
    (D.augmentedPresentedGroupEquiv hR)

/--
Under the prefix-closed quotient-section hypothesis, replacing the presentation relator set by
its finite relator finset preserves the presented group.
-/
noncomputable def presentationRelatorFinsetPresentedGroupEquivOfIsPrefixClosedQuotientSection
    [Fintype X]
    (R : Finset (FreeGroup X))
    (hR : Subgroup.normalClosure ({r | r ∈ R} : Set (FreeGroup X)) ≤ D.kernel)
    (hprefix : D.IsPrefixClosedQuotientSection) :
    PresentedGroup
        ({z | z ∈ D.presentationRelatorFinset R} :
          Set (FreeGroup (FiniteSchreierSymbol X Q))) ≃*
      D.kernel ⧸ D.relatorSubgroup ({r | r ∈ R} : Set (FreeGroup X)) :=
  (QuotientGroup.congr
    (Subgroup.normalClosure
      ({z | z ∈ D.presentationRelatorFinset R} :
        Set (FreeGroup (FiniteSchreierSymbol X Q))))
    (Subgroup.normalClosure
      (D.presentationRelators ({r | r ∈ R} : Set (FreeGroup X))))
    (MulEquiv.refl (FreeGroup (FiniteSchreierSymbol X Q)))
    (by
      rw [D.coe_presentationRelatorFinset R]
      simp only [MulEquiv.toMonoidHom_refl, SetLike.setOfPred_mem_eq, Subgroup.map_id])).trans
    (D.presentationPresentedGroupEquivOfIsPrefixClosedQuotientSection hR hprefix)

/-- The raw presentation evaluation quotient map is surjective. -/
theorem symbolEvalPresentationQuotientHom_surjective
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    Function.Surjective (D.symbolEvalPresentationQuotientHom hR) := by
  intro y
  rcases QuotientGroup.mk'_surjective (D.relatorSubgroup R) y with ⟨l, rfl⟩
  exact ⟨D.tauKernelPresentationQuotientHom R l,
    D.symbolEvalPresentationQuotientHom_tauKernelPresentationQuotientHom hR l⟩

/-- The augmented-presentation evaluation quotient map is surjective. -/
theorem symbolEvalAugmentedPresentationQuotientHom_surjective
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    Function.Surjective (D.symbolEvalAugmentedPresentationQuotientHom hR) := by
  intro y
  rcases QuotientGroup.mk'_surjective (D.relatorSubgroup R) y with ⟨l, rfl⟩
  exact ⟨D.tauKernelAugmentedPresentationQuotientHom R l,
    D.symbolEvalAugmentedPresentationQuotientHom_tauKernelAugmentedPresentationQuotientHom hR l⟩


end FiniteQuotientSchreierData

end ReidemeisterSchreier.Discrete
