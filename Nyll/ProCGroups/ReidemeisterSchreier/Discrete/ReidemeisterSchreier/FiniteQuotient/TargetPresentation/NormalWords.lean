/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.TargetPresentation.Core

/-!
# Reidemeister--Schreier target-presentation normal words

Reidemeister Schreier / Discrete / Reidemeister Schreier / Finite Quotient / Target Presentation
/ Normal Words.

This module packages normal-word witnesses for the cleaned symbols and uses
them to construct the cleaned target-presentation data, Tietze equivalence,
and kernel equivalence.
-/


namespace ReidemeisterSchreier.Discrete

open ReidemeisterSchreier.Discrete.Presentations

variable {X Q : Type*} [Group Q] [Fintype Q]

namespace PrefixClosedFiniteQuotientSchreierData

variable [DecidableEq X]
variable (D : PrefixClosedFiniteQuotientSchreierData X Q)

/--
A computation-facing variant of \(\mathrm{CleanedReidemeisterSchreierTargetPresentationData}\),
carrying a concrete target word and a certificate that substitution into the reduced
\(\mathrm{cleanedTauNormalWord}(q,r)\) reduces to that word.
-/
structure CleanedReidemeisterSchreierTargetPresentationNormalWordData
    (R : Set (FreeGroup X)) (Y : Type*)
    [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
    [DecidableEq D.nondegenerateSchreierSymbol] [DecidableEq Y] where
  /-- The relators of the chosen target presentation on generators \(Y\). -/
  targetRelators : Set (FreeGroup Y)
  /-- The word in target generators assigned to each nondegenerate Schreier generator. -/
  toTargetGenerator : D.nondegenerateSchreierSymbol → FreeGroup Y
  /-- The word in nondegenerate Schreier generators assigned to each target generator. -/
  fromTargetGenerator : Y → FreeGroup D.nondegenerateSchreierSymbol
  /-- A concrete target word representing each cleaned Reidemeister--Schreier relator. -/
  cleanedRelatorWord : Q → FreeGroup X → List (Y × Bool)
  /--
  Substituting target words into a cleaned normal word reduces to the specified target relator
  word.
  -/
  cleanedRelatorWord_reduce :
    ∀ q : Q, ∀ r ∈ R,
      FreeGroup.reduce
          (freeGroupSubstitutionWord toTargetGenerator
            (D.cleanedTauNormalWord q r)) =
        FreeGroup.reduce (cleanedRelatorWord q r)
  /-- Every specified target relator word is trivial modulo the target relators. -/
  mapsCleanedRelatorWords :
    ∀ q : Q, ∀ r ∈ R,
      RelatorEquivalent targetRelators
        (FreeGroup.mk (cleanedRelatorWord q r)) 1
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

namespace CleanedReidemeisterSchreierTargetPresentationNormalWordData

variable {D}
variable {R : Set (FreeGroup X)} {Y : Type*}
variable [DecidablePred D.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol]
variable [DecidableEq D.nondegenerateSchreierSymbol] [DecidableEq Y]

/--
The normal-word target data maps every cleaned Schreier relator to an identity modulo the target
relators.
-/
theorem mapsCleanedRelators
    (C : D.CleanedReidemeisterSchreierTargetPresentationNormalWordData R Y) :
    ∀ q : Q, ∀ r ∈ R,
      RelatorEquivalent C.targetRelators
        (FreeGroup.lift C.toTargetGenerator (D.cleanedTau q r)) 1 :=
  D.toFiniteQuotientSchreierData.mapsCleanedRelators_of_cleanedTauNormalWord_reduce
    (toTargetGenerator := C.toTargetGenerator)
    C.cleanedRelatorWord C.cleanedRelatorWord_reduce
    C.mapsCleanedRelatorWords

/--
Normal-word target presentation data forgets to the corresponding cleaned target presentation
data.
-/
def toTargetPresentationData
    (C : D.CleanedReidemeisterSchreierTargetPresentationNormalWordData R Y) :
    D.CleanedReidemeisterSchreierTargetPresentationData R Y where
  targetRelators := C.targetRelators
  toTargetGenerator := C.toTargetGenerator
  fromTargetGenerator := C.fromTargetGenerator
  mapsCleanedRelators := C.mapsCleanedRelators
  mapsTargetRelators := C.mapsTargetRelators
  from_toTargetGenerator := C.from_toTargetGenerator
  to_fromTargetGenerator := C.to_fromTargetGenerator

/-- The normal-word cleaned target presentation data yields a Tietze equivalence. -/
def toTietzeEquiv
    (C : D.CleanedReidemeisterSchreierTargetPresentationNormalWordData R Y) :
    TietzeEquiv (D.cleanedSchreierRelators R) C.targetRelators :=
  C.toTargetPresentationData.toTietzeEquiv

/--
The normal-word target presentation is equivalent to the cleaned Reidemeister--Schreier
presentation.
-/
noncomputable def presentedEquiv
    (C : D.CleanedReidemeisterSchreierTargetPresentationNormalWordData R Y) :
    PresentedGroup (D.cleanedSchreierRelators R) ≃*
      PresentedGroup C.targetRelators :=
  C.toTietzeEquiv.presentedEquiv

/--
The target presented group is equivalent to the subgroup kernel described by the cleaned
Reidemeister--Schreier presentation.
-/
noncomputable def targetPresentedGroupEquivKernel
    (C : D.CleanedReidemeisterSchreierTargetPresentationNormalWordData R Y)
    (hR : Subgroup.normalClosure R ≤ D.kernel) :
    PresentedGroup C.targetRelators ≃*
      D.kernel ⧸ relatorSubgroup D R :=
  C.presentedEquiv.symm.trans (D.cleanedPresentationPresentedGroupEquiv hR)

/-- The normal-word cleaned target presentation data yields the corresponding Tietze script. -/
def toPresentationEquivCertificate
    (C : D.CleanedReidemeisterSchreierTargetPresentationNormalWordData R Y) :
    PresentationEquivCertificate
      (Presentation.ofRelators (D.cleanedSchreierRelators R))
      (Presentation.ofRelators C.targetRelators) :=
  C.toTietzeEquiv.toCertificate

end CleanedReidemeisterSchreierTargetPresentationNormalWordData

end PrefixClosedFiniteQuotientSchreierData

end ReidemeisterSchreier.Discrete
