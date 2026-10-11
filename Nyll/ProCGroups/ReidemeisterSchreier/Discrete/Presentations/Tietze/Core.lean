/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.PresentedGroup
import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorMap

/-!
# Semantic equivalence of presentations

This module packages the algebraic content of a Tietze equivalence: mutually
inverse maps between groups presented by relators.  `Presentation` remembers
the generator type, while `PresentationEquivCertificate` composes and reverses
the resulting semantic certificates.

Concrete, inspectable move sequences are defined separately in
`Tietze.Script`.
-/

universe u v w

namespace ReidemeisterSchreier.Discrete.Presentations

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- A reusable semantic Tietze certificate between two relator presentations. -/
structure TietzeEquiv
    {X Y : Type*} (R : Set (FreeGroup X)) (S : Set (FreeGroup Y)) where
  /-- Mutually inverse maps between the two free groups, modulo their relator normal closures. -/
  toMutualMapData : RelatorQuotientMutualMapData R S

namespace TietzeEquiv

variable {X Y Z : Type*}
variable {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
variable {T : Set (FreeGroup Z)}

/-- The identity mutual map gives a reflexive Tietze equivalence. -/
def refl (R : Set (FreeGroup X)) : TietzeEquiv R R where
  toMutualMapData := RelatorQuotientMutualMapData.refl R

/-- Reversing the mutual maps gives the symmetric Tietze equivalence. -/
def symm (D : TietzeEquiv R S) : TietzeEquiv S R where
  toMutualMapData := D.toMutualMapData.symm

/-- Composing mutual maps gives the transitive composite of Tietze equivalences. -/
def trans (D₁ : TietzeEquiv R S) (D₂ : TietzeEquiv S T) :
    TietzeEquiv R T where
  toMutualMapData := D₁.toMutualMapData.trans D₂.toMutualMapData

/-- Mutual relator-quotient map data define a Tietze equivalence. -/
def ofMutualMapData (D : RelatorQuotientMutualMapData R S) :
    TietzeEquiv R S where
  toMutualMapData := D

/--
A Tietze equivalence is induced by a relator-equivalence comparison between the two relator
sets.
-/
def ofRelatorEquivalent
    {R S : Set (FreeGroup X)}
    (hR_to_S : ∀ r ∈ R, RelatorEquivalent S r 1)
    (hS_to_R : ∀ s ∈ S, RelatorEquivalent R s 1) :
    TietzeEquiv R S where
  toMutualMapData :=
    relatorQuotientMutualMapDataOfRelatorEquivalent hR_to_S hS_to_R

/-- Equal normal closures give a Tietze equivalence between the two relator sets. -/
def ofNormalClosureEq
    {R S : Set (FreeGroup X)}
    (h : Subgroup.normalClosure R = Subgroup.normalClosure S) :
    TietzeEquiv R S where
  toMutualMapData := relatorQuotientMutualMapDataOfNormalClosureEq h

/--
Compatible generator maps in both directions define a Tietze equivalence between the two relator
quotients.
-/
def ofGeneratorMaps
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    (toGenerator : X → FreeGroup Y)
    (invGenerator : Y → FreeGroup X)
    (hR :
      ∀ r ∈ R,
        FreeGroup.lift toGenerator r ∈ Subgroup.normalClosure S)
    (hS :
      ∀ s ∈ S,
        FreeGroup.lift invGenerator s ∈ Subgroup.normalClosure R)
    (hinv_to :
      ∀ x : X,
        RelatorEquivalent R
          (FreeGroup.lift invGenerator (toGenerator x))
          (FreeGroup.of x))
    (hto_inv :
      ∀ y : Y,
        RelatorEquivalent S
          (FreeGroup.lift toGenerator (invGenerator y))
          (FreeGroup.of y)) :
    TietzeEquiv R S :=
  TietzeEquiv.ofMutualMapData
    (relatorQuotientMutualMapDataOfGeneratorMaps
      toGenerator invGenerator hR hS hinv_to hto_inv)

/--
Generator maps that preserve relators up to relator equivalence induce the corresponding
presented-group map.
-/
def ofGeneratorMapsRelatorEquivalent
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    (toGenerator : X → FreeGroup Y)
    (invGenerator : Y → FreeGroup X)
    (hR :
      ∀ r ∈ R,
        RelatorEquivalent S (FreeGroup.lift toGenerator r) 1)
    (hS :
      ∀ s ∈ S,
        RelatorEquivalent R (FreeGroup.lift invGenerator s) 1)
    (hinv_to :
      ∀ x : X,
        RelatorEquivalent R
          (FreeGroup.lift invGenerator (toGenerator x))
          (FreeGroup.of x))
    (hto_inv :
      ∀ y : Y,
        RelatorEquivalent S
          (FreeGroup.lift toGenerator (invGenerator y))
          (FreeGroup.of y)) :
    TietzeEquiv R S :=
  TietzeEquiv.ofMutualMapData
    (relatorQuotientMutualMapDataOfGeneratorMapsRelatorEquivalent
      toGenerator invGenerator hR hS hinv_to hto_inv)

/--
A Tietze certificate from generator maps when both relator sets are indexed unions of named
relator families.
-/
def ofGeneratorMapsRelatorEquivalent_iUnion
    {ι κ : Sort*}
    {R : ι → Set (FreeGroup X)} {S : κ → Set (FreeGroup Y)}
    (toGenerator : X → FreeGroup Y)
    (invGenerator : Y → FreeGroup X)
    (hR :
      ∀ i : ι, ∀ r ∈ R i,
        RelatorEquivalent (Set.iUnion S) (FreeGroup.lift toGenerator r) 1)
    (hS :
      ∀ k : κ, ∀ s ∈ S k,
        RelatorEquivalent (Set.iUnion R) (FreeGroup.lift invGenerator s) 1)
    (hinv_to :
      ∀ x : X,
        RelatorEquivalent (Set.iUnion R)
          (FreeGroup.lift invGenerator (toGenerator x))
          (FreeGroup.of x))
    (hto_inv :
      ∀ y : Y,
        RelatorEquivalent (Set.iUnion S)
          (FreeGroup.lift toGenerator (invGenerator y))
          (FreeGroup.of y)) :
    TietzeEquiv (Set.iUnion R) (Set.iUnion S) :=
  TietzeEquiv.ofMutualMapData
    (relatorQuotientMutualMapDataOfGeneratorMapsRelatorEquivalent_iUnion
      toGenerator invGenerator hR hS hinv_to hto_inv)

/--
A Tietze equivalence is obtained from generator maps whose doubly indexed source relators map to
relator-equivalent target relators.
-/
def ofGeneratorMapsRelatorEquivalent_iUnion₂
    {ι κ : Sort*} {α : ι → Sort*} {β : κ → Sort*}
    {R : ∀ i : ι, α i → Set (FreeGroup X)}
    {S : ∀ k : κ, β k → Set (FreeGroup Y)}
    (toGenerator : X → FreeGroup Y)
    (invGenerator : Y → FreeGroup X)
    (hR :
      ∀ i : ι, ∀ a : α i, ∀ r ∈ R i a,
        RelatorEquivalent
          (Set.iUnion fun k : κ => Set.iUnion (S k))
          (FreeGroup.lift toGenerator r) 1)
    (hS :
      ∀ k : κ, ∀ b : β k, ∀ s ∈ S k b,
        RelatorEquivalent
          (Set.iUnion fun i : ι => Set.iUnion (R i))
          (FreeGroup.lift invGenerator s) 1)
    (hinv_to :
      ∀ x : X,
        RelatorEquivalent
          (Set.iUnion fun i : ι => Set.iUnion (R i))
          (FreeGroup.lift invGenerator (toGenerator x))
          (FreeGroup.of x))
    (hto_inv :
      ∀ y : Y,
        RelatorEquivalent
          (Set.iUnion fun k : κ => Set.iUnion (S k))
          (FreeGroup.lift toGenerator (invGenerator y))
          (FreeGroup.of y)) :
    TietzeEquiv
      (Set.iUnion fun i : ι => Set.iUnion (R i))
      (Set.iUnion fun k : κ => Set.iUnion (S k)) :=
  TietzeEquiv.ofMutualMapData
    (relatorQuotientMutualMapDataOfGeneratorMapsRelatorEquivalent_iUnion₂
      toGenerator invGenerator hR hS hinv_to hto_inv)

/-- A Tietze equivalence induces an isomorphism of the corresponding relator quotients. -/
noncomputable def quotientEquiv (D : TietzeEquiv R S) :
    FreeGroup X ⧸ Subgroup.normalClosure R ≃*
      FreeGroup Y ⧸ Subgroup.normalClosure S :=
  quotientEquivOfRelatorQuotientMutualMapData R S D.toMutualMapData

/-- A Tietze equivalence induces an isomorphism of presented groups. -/
noncomputable def presentedEquiv (D : TietzeEquiv R S) :
    PresentedGroup R ≃* PresentedGroup S :=
  quotientEquivOfRelatorQuotientMutualMapData R S D.toMutualMapData

end TietzeEquiv

/--
A free-group equivalence gives a Tietze equivalence between a relator set and its pullback
relator set.
-/
def freeGroupPullbackRelatorTietzeEquiv
    {X Y : Type*} (e : FreeGroup X ≃* FreeGroup Y)
    (S : Set (FreeGroup Y)) :
    TietzeEquiv (freeGroupPullbackRelatorSet e S) S :=
  TietzeEquiv.ofMutualMapData
    (relatorQuotientMutualMapDataOfNormalClosureMapEq
      (freeGroupPullbackRelatorSet e S) S e
      (map_normalClosure_freeGroupPullbackRelatorSet e S))

/--
A presentation packaged with its generator type. This is a light wrapper for writing long Tietze
scripts whose intermediate presentations may have different generator types.
-/
structure Presentation where
  /-- The type of generators of the presentation. -/
  Generator : Type u
  /-- The set of relators in the free group on `Generator`. -/
  relators : Set (FreeGroup Generator)

namespace Presentation

/-- This constructs a presentation from the given relator family. -/
def ofRelators {X : Type u} (R : Set (FreeGroup X)) : Presentation.{u} where
  Generator := X
  relators := R

end Presentation

/-- A semantic equivalence certificate between packaged presentations. -/
structure PresentationEquivCertificate
    (P : Presentation.{u}) (Q : Presentation.{v}) where
  /-- The Tietze equivalence between the relator sets of the two presentations. -/
  toTietzeEquiv : TietzeEquiv P.relators Q.relators

namespace PresentationEquivCertificate

/--
A Tietze equivalence between the relator sets gives a scriptable Tietze certificate between the
packaged presentations.
-/
def ofTietzeEquiv {P : Presentation.{u}} {Q : Presentation.{v}}
    (D : TietzeEquiv P.relators Q.relators) :
    PresentationEquivCertificate P Q where
  toTietzeEquiv := D

/-- Mutual maps modulo relators determine a Tietze script between the two presentations. -/
def ofMutualMapData {P : Presentation.{u}} {Q : Presentation.{v}}
    (D : RelatorQuotientMutualMapData P.relators Q.relators) :
    PresentationEquivCertificate P Q :=
  ofTietzeEquiv (TietzeEquiv.ofMutualMapData D)

/-- Every packaged presentation has its identity semantic equivalence certificate. -/
def refl (P : Presentation.{u}) : PresentationEquivCertificate P P :=
  ofTietzeEquiv (TietzeEquiv.refl P.relators)

/-- Reversing a presentation certificate gives a certificate in the opposite direction. -/
def symm {P : Presentation.{u}} {Q : Presentation.{v}}
    (D : PresentationEquivCertificate P Q) :
    PresentationEquivCertificate Q P :=
  ofTietzeEquiv D.toTietzeEquiv.symm

/-- Presentation equivalence certificates compose through an intermediate presentation. -/
def trans {P : Presentation.{u}} {Q : Presentation.{v}}
    {U : Presentation.{w}}
    (D₁ : PresentationEquivCertificate P Q) (D₂ : PresentationEquivCertificate Q U) :
    PresentationEquivCertificate P U :=
  ofTietzeEquiv (D₁.toTietzeEquiv.trans D₂.toTietzeEquiv)

/-- A Tietze script induces an isomorphism of the packaged presented groups. -/
noncomputable def presentedEquiv
    {P : Presentation.{u}} {Q : Presentation.{v}}
    (D : PresentationEquivCertificate P Q) :
    PresentedGroup P.relators ≃* PresentedGroup Q.relators :=
  D.toTietzeEquiv.presentedEquiv

/-- A Tietze script induces an isomorphism of the packaged relator quotients. -/
noncomputable def quotientEquiv
    {P : Presentation.{u}} {Q : Presentation.{v}}
    (D : PresentationEquivCertificate P Q) :
    FreeGroup P.Generator ⧸ Subgroup.normalClosure P.relators ≃*
      FreeGroup Q.Generator ⧸ Subgroup.normalClosure Q.relators :=
  D.toTietzeEquiv.quotientEquiv

end PresentationEquivCertificate

namespace TietzeEquiv

/-- Package a Tietze equivalence as a scriptable Tietze certificate. -/
def toCertificate
    {X Y : Type*} {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    (D : TietzeEquiv R S) :
    PresentationEquivCertificate (Presentation.ofRelators R) (Presentation.ofRelators S) :=
  PresentationEquivCertificate.ofTietzeEquiv D

end TietzeEquiv

end ReidemeisterSchreier.Discrete.Presentations
