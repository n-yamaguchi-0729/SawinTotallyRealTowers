/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.RelatorQuotientMutualMapData

/-!
# Reidemeister Schreier / Discrete / Presentations / Tietze / Generator Map

This module builds relator-quotient equivalences from maps on generators,
including indexed relator families, and proves the normal-closure properties
of the associated free-group pullback relators.
-/

universe u v w

namespace ReidemeisterSchreier.Discrete.Presentations

variable {G H K : Type*} [Group G] [Group H] [Group K]

/--
A group equivalence whose forward and inverse maps send relators into the opposite normal
closures supplies mutual map data for the two relator quotients.
-/
def relatorQuotientMutualMapDataOfRelatorImagesMemNormalClosure
    (e : G ≃* H) (R : Set G) (S : Set H)
    (hR_to_S : ∀ r ∈ R, e r ∈ Subgroup.normalClosure S)
    (hS_to_R : ∀ s ∈ S, e.symm s ∈ Subgroup.normalClosure R) :
    RelatorQuotientMutualMapData R S :=
  relatorQuotientMutualMapDataOfNormalClosureMapEq R S e
    (map_normalClosure_eq_of_mulEquiv_relator_images_mem_normalClosure e R S hR_to_S hS_to_R)

/--
Compatible generator maps in both directions define mutual map data on the corresponding relator
quotients.
-/
def relatorQuotientMutualMapDataOfGeneratorMaps
    {X Y : Type*} {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
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
    RelatorQuotientMutualMapData R S where
  toHom := FreeGroup.lift toGenerator
  invHom := FreeGroup.lift invGenerator
  mapsRelators := hR
  mapsTargetRelators := hS
  inv_toHom := by
    intro w
    let N : Subgroup (FreeGroup X) := Subgroup.normalClosure R
    let F : FreeGroup X →* FreeGroup X ⧸ N :=
      (QuotientGroup.mk' N).comp
        ((FreeGroup.lift invGenerator).comp (FreeGroup.lift toGenerator))
    have hhom : F = QuotientGroup.mk' N := by
      ext x
      dsimp [F]
      simp only [FreeGroup.lift_apply_of]
      rw [← relatorEquivalent_iff_eq_in_presentedQuotient]
      exact hinv_to x
    have hw := congrArg (fun f : FreeGroup X →* FreeGroup X ⧸ N => f w) hhom
    change
      ((FreeGroup.lift invGenerator
          (FreeGroup.lift toGenerator w) : FreeGroup X) :
        FreeGroup X ⧸ N) =
      ((w : FreeGroup X) : FreeGroup X ⧸ N) at hw
    exact (by
      simpa [N, RelatorEquivalent] using
        (relatorEquivalent_iff_eq_in_presentedQuotient.2 hw :
          RelatorEquivalent R
            (FreeGroup.lift invGenerator (FreeGroup.lift toGenerator w)) w))
  to_invHom := by
    intro w
    let N : Subgroup (FreeGroup Y) := Subgroup.normalClosure S
    let F : FreeGroup Y →* FreeGroup Y ⧸ N :=
      (QuotientGroup.mk' N).comp
        ((FreeGroup.lift toGenerator).comp (FreeGroup.lift invGenerator))
    have hhom : F = QuotientGroup.mk' N := by
      ext y
      dsimp [F]
      simp only [FreeGroup.lift_apply_of]
      rw [← relatorEquivalent_iff_eq_in_presentedQuotient]
      exact hto_inv y
    have hw := congrArg (fun f : FreeGroup Y →* FreeGroup Y ⧸ N => f w) hhom
    change
      ((FreeGroup.lift toGenerator
          (FreeGroup.lift invGenerator w) : FreeGroup Y) :
        FreeGroup Y ⧸ N) =
      ((w : FreeGroup Y) : FreeGroup Y ⧸ N) at hw
    exact (by
      simpa [N, RelatorEquivalent] using
        (relatorEquivalent_iff_eq_in_presentedQuotient.2 hw :
          RelatorEquivalent S
            (FreeGroup.lift toGenerator (FreeGroup.lift invGenerator w)) w))

/--
Generator maps that preserve relators up to relator equivalence give mutual map data between
relator quotients.
-/
def relatorQuotientMutualMapDataOfGeneratorMapsRelatorEquivalent
    {X Y : Type*} {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
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
    RelatorQuotientMutualMapData R S :=
  relatorQuotientMutualMapDataOfGeneratorMaps
    toGenerator invGenerator
    (fun r hr => RelatorEquivalent.mem_normalClosure_of_eq_one (hR r hr))
    (fun s hs => RelatorEquivalent.mem_normalClosure_of_eq_one (hS s hs))
    hinv_to hto_inv

/--
Generator-map certificate for presentations whose relators are indexed families, with source and
target relators checked one family at a time.
-/
def relatorQuotientMutualMapDataOfGeneratorMapsRelatorEquivalent_iUnion
    {X Y : Type*} {ι κ : Sort*}
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
    RelatorQuotientMutualMapData (Set.iUnion R) (Set.iUnion S) :=
  relatorQuotientMutualMapDataOfGeneratorMapsRelatorEquivalent
    toGenerator invGenerator
    (by
      intro r hr
      rcases Set.mem_iUnion.1 hr with ⟨i, hi⟩
      exact hR i r hi)
    (by
      intro s hs
      rcases Set.mem_iUnion.1 hs with ⟨k, hk⟩
      exact hS k s hk)
    hinv_to hto_inv

/--
Generator maps that preserve doubly indexed relator families give mutual map data between the
relator quotients.
-/
def relatorQuotientMutualMapDataOfGeneratorMapsRelatorEquivalent_iUnion₂
    {X Y : Type*} {ι κ : Sort*} {α : ι → Sort*} {β : κ → Sort*}
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
    RelatorQuotientMutualMapData
      (Set.iUnion fun i : ι => Set.iUnion (R i))
      (Set.iUnion fun k : κ => Set.iUnion (S k)) :=
  relatorQuotientMutualMapDataOfGeneratorMapsRelatorEquivalent
    toGenerator invGenerator
    (by
      intro r hr
      rcases Set.mem_iUnion.1 hr with ⟨i, hi⟩
      rcases Set.mem_iUnion.1 hi with ⟨a, ha⟩
      exact hR i a r ha)
    (by
      intro s hs
      rcases Set.mem_iUnion.1 hs with ⟨k, hk⟩
      rcases Set.mem_iUnion.1 hk with ⟨b, hb⟩
      exact hS k b s hb)
    hinv_to hto_inv

/-- Pull a relator set back along a free-group equivalence. -/
def freeGroupPullbackRelatorSet
    {Y : Type*} (e : FreeGroup Y ≃* G) (S : Set G) :
    Set (FreeGroup Y) :=
  e.symm '' S

/-- Mapping the normal closure of the pulled-back relators recovers the original normal closure. -/
theorem map_normalClosure_freeGroupPullbackRelatorSet
    {Y : Type*} (e : FreeGroup Y ≃* G) (S : Set G) :
    Subgroup.map e.toMonoidHom
        (Subgroup.normalClosure (freeGroupPullbackRelatorSet e S)) =
      Subgroup.normalClosure S := by
  rw [Subgroup.map_normalClosure _ e.toMonoidHom e.surjective]
  congr
  ext z
  constructor
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    simpa [← hy] using hs
  · intro hz
    exact ⟨e.symm z, ⟨z, hz, rfl⟩, by simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
        MulEquiv.apply_symm_apply]⟩

/--
A free-group equivalence identifies the quotient by a relator set with the quotient by its
pullback relator set.
-/
noncomputable def freeGroupPullbackRelatorQuotientEquiv
    {Y : Type*} (e : FreeGroup Y ≃* G) (S : Set G) :
    FreeGroup Y ⧸
        Subgroup.normalClosure (freeGroupPullbackRelatorSet e S) ≃*
      G ⧸ Subgroup.normalClosure S :=
  QuotientGroup.congr
    (Subgroup.normalClosure (freeGroupPullbackRelatorSet e S))
    (Subgroup.normalClosure S)
    e
    (map_normalClosure_freeGroupPullbackRelatorSet e S)

/-- Mutual relator-quotient map data induce an isomorphism of the corresponding quotients. -/
noncomputable def quotientEquivOfRelatorQuotientMutualMapData
    (R : Set G) (S : Set H)
    (hData : RelatorQuotientMutualMapData R S) :
    G ⧸ Subgroup.normalClosure R ≃* H ⧸ Subgroup.normalClosure S :=
  quotientEquivOfRelatorsByMutualMaps R S
    hData.toHom hData.invHom hData.mapsRelators hData.mapsTargetRelators
    hData.inv_toHom hData.to_invHom


end ReidemeisterSchreier.Discrete.Presentations
