/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.Presentation

/-!
# Reidemeister--Schreier target-presentation core

Reidemeister Schreier / Discrete / Reidemeister Schreier / Finite Quotient / Target Presentation
/ Core.

This module defines the structured certificates for prefix-closed
quotient-section words and the core data specifying a cleaned
Reidemeister--Schreier target presentation.
-/


namespace ReidemeisterSchreier.Discrete

open ReidemeisterSchreier.Discrete.Presentations

variable {X Q : Type*} [Group Q] [Fintype Q]

/--
Finite quotient Schreier data whose section is prefix closed on its representative words. This
is the convenient application-facing input for the raw finite Reidemeister--Schreier
presentation theorem.
-/
structure PrefixClosedFiniteQuotientSchreierData
    (X Q : Type*) [Group Q] [Fintype Q] [DecidableEq X] where
  /-- The underlying finite quotient and normalized section. -/
  toFiniteQuotientSchreierData : FiniteQuotientSchreierData X Q
  /-- The chosen quotient-section words are closed under taking prefixes. -/
  isPrefixClosed :
    toFiniteQuotientSchreierData.IsPrefixClosedQuotientSection

/-- Common word-level data for a finite quotient section. -/
structure QuotientSectionWordCertificate
    (X Q : Type*) [Group Q] [Fintype Q] where
  /-- The homomorphism from the free group to the finite quotient. -/
  quotientMap : FreeGroup X →* Q
  /-- The chosen word representing each finite quotient element. -/
  quotientSectionWord : Q → List (X × Bool)
  /-- Evaluating a chosen word and applying the quotient map recovers its quotient element. -/
  quotientMap_mk_quotientSectionWord :
    ∀ q : Q, quotientMap (FreeGroup.mk (quotientSectionWord q)) = q

/--
A reusable word-level certificate for a prefix-closed finite quotient section, including the
required reduced-word and prefix-closedness conditions.
-/
structure PrefixClosedQuotientSectionWordCertificate
    (X Q : Type*) [Group Q] [Fintype Q] [DecidableEq X]
    extends QuotientSectionWordCertificate X Q where
  /-- The identity quotient element is represented by the empty word. -/
  quotientSectionWord_one : quotientSectionWord 1 = []
  /-- Every chosen quotient-section word is reduced. -/
  quotientSectionWord_reduced :
    ∀ q : Q, FreeGroup.reduce (quotientSectionWord q) = quotientSectionWord q
  /-- Every prefix of a chosen quotient-section word is the chosen word for its quotient state. -/
  prefixClosed_quotientSectionWord :
    ∀ q : Q,
      (FiniteQuotientSchreierData.ofQuotientSectionWords quotientMap
        quotientSectionWord quotientMap_mk_quotientSectionWord
        quotientSectionWord_one).prefixClosedQuotientSectionWordAlongList
          quotientSectionWord 1 (quotientSectionWord q)

namespace PrefixClosedQuotientSectionWordCertificate

variable [DecidableEq X]
variable (C : PrefixClosedQuotientSectionWordCertificate X Q)

/-- The certificate data forgets to the underlying finite quotient Schreier data. -/
def toFiniteQuotientSchreierData :
    FiniteQuotientSchreierData X Q :=
  FiniteQuotientSchreierData.ofQuotientSectionWords
    C.quotientMap C.quotientSectionWord
    C.quotientMap_mk_quotientSectionWord C.quotientSectionWord_one

/-- The certificate data determines prefix-closed finite quotient Schreier data. -/
def toPrefixClosedFiniteQuotientSchreierData :
    PrefixClosedFiniteQuotientSchreierData X Q where
  toFiniteQuotientSchreierData := C.toFiniteQuotientSchreierData
  isPrefixClosed :=
    FiniteQuotientSchreierData.isPrefixClosedQuotientSection_of_prefixClosedQuotientSectionWord
      C.toFiniteQuotientSchreierData
      (by intro q; rfl)
      C.quotientSectionWord_reduced
      (by
        intro q
        exact C.prefixClosed_quotientSectionWord q)

end PrefixClosedQuotientSectionWordCertificate

/--
A certificate for a positive prefix-closed quotient-section tree. Each quotient element has a
positive word in the original generators, and every prefix is the chosen word for the quotient
element it represents.
-/
structure PositivePrefixClosedQuotientSectionWordCertificate
    (X Q : Type*) [Group Q] [Fintype Q]
    extends QuotientSectionWordCertificate X Q where
  /-- Every letter in every chosen quotient-section word has positive orientation. -/
  quotientSectionWord_positive :
    ∀ q : Q, ∀ xb ∈ quotientSectionWord q, xb.2 = true
  /-- Each prefix is the chosen word for the quotient element obtained by evaluating that prefix. -/
  prefixState :
    ∀ q : Q, ∀ acc rest : List (X × Bool),
      acc ++ rest = quotientSectionWord q →
        quotientSectionWord (quotientMap (FreeGroup.mk acc)) = acc

namespace PositivePrefixClosedQuotientSectionWordCertificate

variable (C : PositivePrefixClosedQuotientSectionWordCertificate X Q)

/-- The quotient-section word certificate sends the identity quotient element to the empty word. -/
theorem quotientSectionWord_one :
    C.quotientSectionWord 1 = [] := by
  have h := C.prefixState 1 [] (C.quotientSectionWord 1) (by simp only [List.nil_append])
  simpa [← FreeGroup.one_eq_mk] using h

/-- Every quotient-section word in the positive prefix-closed certificate is reduced. -/
theorem quotientSectionWord_reduced [DecidableEq X] (q : Q) :
    FreeGroup.reduce (C.quotientSectionWord q) = C.quotientSectionWord q :=
  FiniteQuotientSchreierData.reduce_eq_of_forall_snd_eq_true
    (C.quotientSectionWord_positive q)

/-- The certificate data forgets to the underlying finite quotient Schreier data. -/
def toFiniteQuotientSchreierData :
    FiniteQuotientSchreierData X Q :=
  FiniteQuotientSchreierData.ofQuotientSectionWords
    C.quotientMap C.quotientSectionWord
    C.quotientMap_mk_quotientSectionWord
    C.quotientSectionWord_one

/-- The certificate data determines prefix-closed finite quotient Schreier data. -/
def toPrefixClosedFiniteQuotientSchreierData [DecidableEq X] :
    PrefixClosedFiniteQuotientSchreierData X Q where
  toFiniteQuotientSchreierData := C.toFiniteQuotientSchreierData
  isPrefixClosed := by
    apply
      FiniteQuotientSchreierData.isPrefixClosedQuotientSection_of_prefixClosedQuotientSectionWord
        (D := C.toFiniteQuotientSchreierData)
    · intro q
      rfl
    · intro q
      exact C.quotientSectionWord_reduced q
    · intro q
      exact
        FiniteQuotientSchreierData.prefixClosedQuotientSectionWordAlongList_of_positive_prefixStates
          (D := C.toFiniteQuotientSchreierData)
          (by intro q; rfl)
          C.quotientSectionWord_positive
          (by
            intro target acc rest hcat
            simpa [toFiniteQuotientSchreierData,
              FiniteQuotientSchreierData.ofQuotientSectionWords] using
              C.prefixState target acc rest hcat)
          q

end PositivePrefixClosedQuotientSectionWordCertificate

namespace PrefixClosedFiniteQuotientSchreierData

variable [DecidableEq X]

/--
Finite quotient Schreier data can be built from quotient-section words whose evaluations are the
prescribed quotient sections.
-/
def ofQuotientSectionWords
    (quotientMap : FreeGroup X →* Q)
    (quotientSectionWord : Q → List (X × Bool))
    (quotientMap_mk_quotientSectionWord :
      ∀ q : Q, quotientMap (FreeGroup.mk (quotientSectionWord q)) = q)
    (quotientSectionWord_one : quotientSectionWord 1 = [])
    (quotientSectionWord_reduced :
      ∀ q : Q, FreeGroup.reduce (quotientSectionWord q) = quotientSectionWord q)
    (prefixClosed_quotientSectionWord :
      ∀ q : Q,
        (FiniteQuotientSchreierData.ofQuotientSectionWords quotientMap
          quotientSectionWord quotientMap_mk_quotientSectionWord
          quotientSectionWord_one).prefixClosedAlongList 1
            (quotientSectionWord q)) :
    PrefixClosedFiniteQuotientSchreierData X Q where
  toFiniteQuotientSchreierData :=
    FiniteQuotientSchreierData.ofQuotientSectionWords quotientMap
      quotientSectionWord quotientMap_mk_quotientSectionWord
      quotientSectionWord_one
  isPrefixClosed := by
    intro q
    simpa [FiniteQuotientSchreierData.ofQuotientSectionWords,
      FreeGroup.toWord_mk, quotientSectionWord_reduced q] using
      prefixClosed_quotientSectionWord q

/--
Build prefix-closed finite-quotient Schreier data from reduced quotient-section words and their
prefix-closedness certificate.
-/
def ofPrefixClosedQuotientSectionWords
    (quotientMap : FreeGroup X →* Q)
    (quotientSectionWord : Q → List (X × Bool))
    (quotientMap_mk_quotientSectionWord :
      ∀ q : Q, quotientMap (FreeGroup.mk (quotientSectionWord q)) = q)
    (quotientSectionWord_one : quotientSectionWord 1 = [])
    (quotientSectionWord_reduced :
      ∀ q : Q, FreeGroup.reduce (quotientSectionWord q) = quotientSectionWord q)
    (prefixClosed_quotientSectionWord :
      ∀ q : Q,
        FiniteQuotientSchreierData.prefixClosedQuotientSectionWordAlongList
          (FiniteQuotientSchreierData.ofQuotientSectionWords quotientMap
            quotientSectionWord quotientMap_mk_quotientSectionWord
            quotientSectionWord_one)
          quotientSectionWord 1 (quotientSectionWord q)) :
    PrefixClosedFiniteQuotientSchreierData X Q where
  toFiniteQuotientSchreierData :=
    FiniteQuotientSchreierData.ofQuotientSectionWords quotientMap
      quotientSectionWord quotientMap_mk_quotientSectionWord
      quotientSectionWord_one
  isPrefixClosed :=
    FiniteQuotientSchreierData.isPrefixClosedQuotientSection_of_prefixClosedQuotientSectionWord
      (FiniteQuotientSchreierData.ofQuotientSectionWords quotientMap
        quotientSectionWord quotientMap_mk_quotientSectionWord
        quotientSectionWord_one)
      (by intro q; rfl)
      quotientSectionWord_reduced
      prefixClosed_quotientSectionWord

/--
Forgetting the prefix-closed structure from `ofQuotientSectionWords` recovers the underlying
finite-quotient Schreier data built from the same section words.
-/
@[simp 900]
theorem ofQuotientSectionWords_toFiniteQuotientSchreierData
    (quotientMap : FreeGroup X →* Q)
    (quotientSectionWord : Q → List (X × Bool))
    (quotientMap_mk_quotientSectionWord :
      ∀ q : Q, quotientMap (FreeGroup.mk (quotientSectionWord q)) = q)
    (quotientSectionWord_one : quotientSectionWord 1 = [])
    (quotientSectionWord_reduced :
      ∀ q : Q, FreeGroup.reduce (quotientSectionWord q) = quotientSectionWord q)
    (prefixClosed_quotientSectionWord :
      ∀ q : Q,
        (FiniteQuotientSchreierData.ofQuotientSectionWords quotientMap
          quotientSectionWord quotientMap_mk_quotientSectionWord
          quotientSectionWord_one).prefixClosedAlongList 1
            (quotientSectionWord q)) :
    (ofQuotientSectionWords quotientMap quotientSectionWord
      quotientMap_mk_quotientSectionWord quotientSectionWord_one
      quotientSectionWord_reduced prefixClosed_quotientSectionWord).toFiniteQuotientSchreierData =
      FiniteQuotientSchreierData.ofQuotientSectionWords quotientMap
        quotientSectionWord quotientMap_mk_quotientSectionWord
        quotientSectionWord_one :=
  rfl

variable (D : PrefixClosedFiniteQuotientSchreierData X Q)

/-- Prefix-closed finite-quotient Schreier data coerces to its underlying finite-quotient
Schreier data. -/
instance instCoePrefixClosedFiniteQuotientSchreierData :
    Coe (PrefixClosedFiniteQuotientSchreierData X Q)
    (FiniteQuotientSchreierData X Q) where
  coe D := D.toFiniteQuotientSchreierData

/-- The kernel of the finite quotient map is the subgroup used in the finite Schreier data. -/
abbrev kernel : Subgroup (FreeGroup X) :=
  D.toFiniteQuotientSchreierData.kernel

/--
For a prefix-closed finite quotient section, the presentation relators are those of the
underlying finite-quotient Schreier data.
-/
abbrev presentationRelators (R : Set (FreeGroup X)) :
    Set (FreeGroup (FiniteQuotientSchreierData.FiniteSchreierSymbol X Q)) :=
  D.toFiniteQuotientSchreierData.presentationRelators R

/-- The relator subgroup is the normal subgroup generated by the target presentation relators. -/
abbrev relatorSubgroup (R : Set (FreeGroup X)) :
    Subgroup D.kernel :=
  D.toFiniteQuotientSchreierData.relatorSubgroup R

/--
The raw finite Reidemeister--Schreier presentation theorem for a prefix-closed finite quotient
section.
-/
noncomputable def presentationQuotientEquiv
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    FreeGroup (FiniteQuotientSchreierData.FiniteSchreierSymbol X Q) ⧸
        Subgroup.normalClosure (presentationRelators D R) ≃*
      D.kernel ⧸ relatorSubgroup D R :=
  (D.toFiniteQuotientSchreierData).presentationQuotientEquivOfIsPrefixClosedQuotientSection
    hR D.isPrefixClosed

/--
The prefix-closed finite quotient Schreier target presentation has presented group equivalent to
the kernel quotient.
-/
noncomputable def presentationPresentedGroupEquiv
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    PresentedGroup (presentationRelators D R) ≃*
      D.kernel ⧸ relatorSubgroup D R :=
  D.presentationQuotientEquiv hR

/-- The nondegenerate Schreier symbols attached to the underlying finite-quotient Schreier data. -/
abbrev nondegenerateSchreierSymbol :
    Type _ :=
  D.toFiniteQuotientSchreierData.NondegenerateSchreierSymbol

/--
For a prefix-closed finite quotient section, these are the raw Reidemeister--Schreier relators
after deleting degenerate Schreier generators.
-/
abbrev presentationRelatorsAfterDeletingDegenerateSchreierGenerators
    (R : Set (FreeGroup X))
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol] :
    Set (FreeGroup D.nondegenerateSchreierSymbol) :=
  (D.toFiniteQuotientSchreierData).presentationRelatorsAfterDeletingDegenerateSchreierGenerators R

/--
Deleting degenerate finite Schreier generators gives a Tietze equivalence with the cleaned
presentation.
-/
def deleteDegenerateSchreierGeneratorsScript
    (R : Set (FreeGroup X))
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol] :
    VerifiedTietzeScript
      (Presentation.ofRelators (presentationRelators D R))
      (Presentation.ofRelators
        (D.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R)) := by
  let data := D.toFiniteQuotientSchreierData
  change VerifiedTietzeScript
    (Presentation.ofRelators (data.presentationRelators R))
    (Presentation.ofRelators
      (data.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R))
  exact data.deleteDegenerateSchreierGeneratorsScript R

/--
Deleting degenerate finite Schreier generators produces the cleaned presentation on
nondegenerate Schreier symbols.
-/
noncomputable def deleteDegenerateSchreierGenerators
    (R : Set (FreeGroup X))
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol] :
    PresentedGroup (presentationRelators D R) ≃*
      PresentedGroup
        (D.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R) :=
  (D.deleteDegenerateSchreierGeneratorsScript R).toCertificate.presentedEquiv

/--
Prefix-closed finite Reidemeister--Schreier theorem after deleting all degenerate Schreier
generators.
-/
noncomputable def presentationAfterDeletingDegenerateSchreierGeneratorsPresentedGroupEquiv
    {R : Set (FreeGroup X)}
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    PresentedGroup
        (D.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R) ≃*
      D.kernel ⧸ relatorSubgroup D R :=
  (D.deleteDegenerateSchreierGenerators R).symm.trans
    (D.presentationPresentedGroupEquiv hR)

/--
The cleaned \(\tau\)-map is the Reidemeister--Schreier rewriting map with degenerate generators
removed.
-/
abbrev cleanedTau
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    FreeGroup D.nondegenerateSchreierSymbol :=
  D.toFiniteQuotientSchreierData.cleanedTau q w

/--
The cleaned \(\tau\)-list is the Reidemeister--Schreier \(\tau\)-list after deleting degenerate
Schreier generators.
-/
abbrev cleanedTauList
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool)) :
    FreeGroup D.nondegenerateSchreierSymbol :=
  D.toFiniteQuotientSchreierData.cleanedTauList q xs

/--
The cleaned \(\tau\)-normal word records the reduced list form of the cleaned \(\tau\)-rewrite.
-/
noncomputable def cleanedTauNormalWord
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    [DecidableEq D.nondegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    List (D.nondegenerateSchreierSymbol × Bool) :=
  D.toFiniteQuotientSchreierData.cleanedTauNormalWord q w

/--
The cleaned \(\tau\)-list normal word records the reduced list form of the cleaned \(\tau\)-list
rewrite.
-/
noncomputable def cleanedTauListNormalWord
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    [DecidableEq D.nondegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool)) :
    List (D.nondegenerateSchreierSymbol × Bool) :=
  D.toFiniteQuotientSchreierData.cleanedTauListNormalWord q xs

/--
The cleaned Schreier relators are the cleaned \(\tau\)-rewrites of original relators over all
finite quotient elements.
-/
abbrev cleanedSchreierRelators
    (R : Set (FreeGroup X))
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol] :
    Set (FreeGroup D.nondegenerateSchreierSymbol) :=
  D.toFiniteQuotientSchreierData.cleanedSchreierRelators R

/--
Prefix-closed finite Reidemeister--Schreier theorem stated directly with cleaned relators, i.e.
after deleting degenerate Schreier generators.
-/
noncomputable def cleanedPresentationPresentedGroupEquiv
    {R : Set (FreeGroup X)}
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    PresentedGroup (D.cleanedSchreierRelators R) ≃*
      D.kernel ⧸ relatorSubgroup D R :=
  (Presented.ofNormalClosureEq
    (R := D.cleanedSchreierRelators R)
    (S := D.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R)
    (by
      change
        Subgroup.normalClosure
            (D.toFiniteQuotientSchreierData.cleanedSchreierRelators R) =
          Subgroup.normalClosure
            (D.toFiniteQuotientSchreierData
              |>.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R)
      exact congrArg Subgroup.normalClosure
        (D.toFiniteQuotientSchreierData
          |>.presentationRelatorsAfterDeletingDegenerate_eq_cleaned R).symm)).trans
    (D.presentationAfterDeletingDegenerateSchreierGeneratorsPresentedGroupEquiv hR)

/--
A certificate that the cleaned finite Reidemeister--Schreier presentation is Tietze equivalent
to a chosen target presentation.
-/
structure CleanedReidemeisterSchreierTargetPresentationData
    (R : Set (FreeGroup X)) (Y : Type*)
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol] where
  /-- The relators of the chosen target presentation on generators \(Y\). -/
  targetRelators : Set (FreeGroup Y)
  /-- The word in target generators assigned to each nondegenerate Schreier generator. -/
  toTargetGenerator : D.nondegenerateSchreierSymbol → FreeGroup Y
  /-- The word in nondegenerate Schreier generators assigned to each target generator. -/
  fromTargetGenerator : Y → FreeGroup D.nondegenerateSchreierSymbol
  /-- Cleaned Reidemeister--Schreier relators map to consequences of the target relators. -/
  mapsCleanedRelators :
    ∀ q : Q, ∀ r ∈ R,
      RelatorEquivalent targetRelators
        (FreeGroup.lift toTargetGenerator (D.cleanedTau q r)) 1
  /-- Target relators map to consequences of the cleaned Reidemeister--Schreier relators. -/
  mapsTargetRelators :
    ∀ s ∈ targetRelators,
      RelatorEquivalent (D.cleanedSchreierRelators R)
        (FreeGroup.lift fromTargetGenerator s) 1
  /-- Mapping a nondegenerate Schreier generator forward and back recovers it modulo relators. -/
  from_toTargetGenerator :
    ∀ z : D.nondegenerateSchreierSymbol,
      RelatorEquivalent (D.cleanedSchreierRelators R)
        (FreeGroup.lift fromTargetGenerator (toTargetGenerator z))
        (FreeGroup.of z)
  /-- Mapping a target generator back and forward recovers it modulo target relators. -/
  to_fromTargetGenerator :
    ∀ y : Y,
      RelatorEquivalent targetRelators
        (FreeGroup.lift toTargetGenerator (fromTargetGenerator y))
        (FreeGroup.of y)

namespace CleanedReidemeisterSchreierTargetPresentationData

variable {D}
variable {R : Set (FreeGroup X)} {Y : Type*}
variable [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]

/-- The cleaned Reidemeister--Schreier target presentation data yields a Tietze equivalence. -/
def toTietzeEquiv
    (C : D.CleanedReidemeisterSchreierTargetPresentationData R Y) :
    TietzeEquiv (D.cleanedSchreierRelators R) C.targetRelators :=
  TietzeEquiv.ofGeneratorMapsRelatorEquivalent
    C.toTargetGenerator C.fromTargetGenerator
    (by
      intro z hz
      rcases hz with ⟨q, r, hr, rfl⟩
      exact C.mapsCleanedRelators q r hr)
    C.mapsTargetRelators
    C.from_toTargetGenerator
    C.to_fromTargetGenerator

/-- The target presentation is equivalent to the cleaned Reidemeister--Schreier presentation. -/
noncomputable def presentedEquiv
    (C : D.CleanedReidemeisterSchreierTargetPresentationData R Y) :
    PresentedGroup (D.cleanedSchreierRelators R) ≃*
      PresentedGroup C.targetRelators :=
  C.toTietzeEquiv.presentedEquiv

/--
The target presented group is equivalent to the subgroup kernel described by the cleaned
Reidemeister--Schreier presentation.
-/
noncomputable def targetPresentedGroupEquivKernel
    (C : D.CleanedReidemeisterSchreierTargetPresentationData R Y)
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    PresentedGroup C.targetRelators ≃*
      D.kernel ⧸ relatorSubgroup D R :=
  C.presentedEquiv.symm.trans (D.cleanedPresentationPresentedGroupEquiv hR)

/--
The cleaned Reidemeister--Schreier target presentation data yields the corresponding Tietze
script.
-/
def toPresentationEquivCertificate
    (C : D.CleanedReidemeisterSchreierTargetPresentationData R Y) :
    PresentationEquivCertificate
      (Presentation.ofRelators (D.cleanedSchreierRelators R))
      (Presentation.ofRelators C.targetRelators) :=
  C.toTietzeEquiv.toCertificate

end CleanedReidemeisterSchreierTargetPresentationData

end PrefixClosedFiniteQuotientSchreierData

end ReidemeisterSchreier.Discrete
