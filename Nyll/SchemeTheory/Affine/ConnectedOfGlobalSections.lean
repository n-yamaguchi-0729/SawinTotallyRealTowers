/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Connectedness from integral global sections

A disconnection of a scheme produces a nontrivial idempotent global section
by gluing the constant sections zero and one. Consequently, a scheme whose
ring of global sections is a domain is connected. In particular, a scheme
over a field is connected when its actual global-sections map is an
isomorphism. This is the section-to-connectedness step used for the fibres
of the canonical relative normalization.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- Triviality of actual global idempotent sections makes a scheme preconnected. -/
lemma Scheme.preconnectedSpace_of_globalSections_idempotents (X : Scheme.{u})
    (h : ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1) :
    PreconnectedSpace X := by
  classical
  apply preconnectedSpace_iff_clopen.mpr
  intro s hs
  let U : X.Opens := ⟨s, hs.isOpen⟩
  let V : X.Opens := ⟨sᶜ, hs.compl.isOpen⟩
  have hCover : U ⊔ V = ⊤ := by
    apply Opens.ext
    exact Set.union_compl_self s
  have hDisjoint : U ⊓ V = ⊥ := by
    apply Opens.ext
    exact Set.inter_compl_self s
  let W : Bool → X.Opens := fun b => cond b U V
  let sections : ∀ b : Bool, Γ(X, W b) :=
    fun b => Bool.rec (motive := fun b => Γ(X, W b)) 0 1 b
  have hW : (⊤ : X.Opens) ≤ iSup W := by
    rw [← hCover]
    exact sup_le (le_iSup W true) (le_iSup W false)
  have hEmpty (b c : Bool) (hbc : b ≠ c) : W b ⊓ W c = ⊥ := by
    cases b with
    | false =>
      cases c with
      | false => exact (hbc rfl).elim
      | true => exact (inf_comm V U).trans hDisjoint
    | true =>
      cases c with
      | false => exact hDisjoint
      | true => exact (hbc rfl).elim
  have hCompatible : TopCat.Presheaf.IsCompatible X.presheaf W sections := by
    intro b c
    by_cases hbc : b = c
    · subst c
      rfl
    · have : Subsingleton Γ(X, W b ⊓ W c) :=
        CommRingCat.subsingleton_of_isTerminal
          (X.sheaf.isTerminalOfEqEmpty (hEmpty b c hbc))
      exact Subsingleton.elim _ _
  obtain ⟨e0, he0, hUnique0⟩ := X.sheaf.existsUnique_gluing' W ⊤
    (fun b => homOfLE le_top) hW sections hCompatible
  let e : Γ(X, ⊤) := e0
  have he : ∀ b : Bool,
      X.presheaf.map (homOfLE (show W b ≤ ⊤ from le_top)).op e = sections b := he0
  have hUnique : ∀ a : Γ(X, ⊤),
      (∀ b : Bool, X.presheaf.map
        (homOfLE (show W b ≤ ⊤ from le_top)).op a = sections b) → a = e := hUnique0
  have hIdempotent : IsIdempotentElem e := by
    change e * e = e
    apply hUnique
    intro b
    rw [map_mul, he b]
    cases b with
    | false => exact zero_mul 0
    | true => exact one_mul 1
  rcases h e hIdempotent with heZero | heOne
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have heU : X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op e = 1 := he true
    rw [heZero, map_zero] at heU
    have hStalk := congrArg (X.presheaf.germ U x hx) heU
    rw [map_zero, map_one] at hStalk
    exact zero_ne_one hStalk
  · right
    apply Set.eq_univ_iff_forall.mpr
    intro x
    by_contra hx
    have heV : X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op e = 0 := he false
    rw [heOne, map_one] at heV
    have hStalk := congrArg (X.presheaf.germ V x hx) heV
    rw [map_one, map_zero] at hStalk
    exact one_ne_zero hStalk

/-- A scheme with an integral domain of global sections is connected. -/
lemma Scheme.connectedSpace_of_isDomain_globalSections (X : Scheme.{u})
    [IsDomain Γ(X, ⊤)] : ConnectedSpace X := by
  have : PreconnectedSpace X := X.preconnectedSpace_of_globalSections_idempotents
    fun _ he => IsIdempotentElem.iff_eq_zero_or_one.mp he
  have hNonempty : Nonempty X := by
    rcases isEmpty_or_nonempty X with hX | hX
    · have : Subsingleton Γ(X, ⊤) := inferInstance
      exact (zero_ne_one (Subsingleton.elim (0 : Γ(X, ⊤)) 1)).elim
    · exact hX
  exact { toNonempty := hNonempty }

/-- If the actual global-sections map of a scheme over a field is an
isomorphism, the scheme is connected. -/
lemma connectedSpace_of_isIso_appTop_to_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsIso f.appTop] : ConnectedSpace X := by
  let e : Γ(X, ⊤) ≅ CommRingCat.of K :=
    (asIso f.appTop).symm ≪≫ Scheme.ΓSpecIso (CommRingCat.of K)
  have : IsDomain Γ(X, ⊤) :=
    MulEquiv.isDomain K e.commRingCatIsoToRingEquiv.toMulEquiv
  exact X.connectedSpace_of_isDomain_globalSections

end AlgebraicGeometry
