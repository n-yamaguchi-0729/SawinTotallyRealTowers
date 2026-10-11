/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.EtaleIrreducibleComponents

/-!
# Étale morphisms on reduced components

Pulling back a reduced component of the base produces an actual finite étale
cover. A component of the original source lifts to a closed component in that
pullback. Domain stalks make this lifted component open, which proves that the
induced map of reduced components is finite étale.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- A finite étale map restricts to a finite étale map on chosen reduced
components if the base change to the target component has domain stalks. -/
theorem reducedIrreducibleComponentMap_isFiniteEtale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFiniteEtale f]
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    (W : Set Y) (hW : W ∈ irreducibleComponents Y)
    (himage : f '' Z = W)
    [IsLocallyNoetherian (pullback f (Y.reducedIrreducibleComponentι W hW))]
    (hdom : ∀ x : (pullback f (Y.reducedIrreducibleComponentι W hW) : Scheme.{u}),
      IsDomain ((pullback f (Y.reducedIrreducibleComponentι W hW)).presheaf.stalk x)) :
    IsFiniteEtale (X.reducedIrreducibleComponentMap f Z hZ W hW himage) := by
  let iZ : X.reducedIrreducibleComponent Z hZ ⟶ X :=
    X.reducedIrreducibleComponentι Z hZ
  let iW : Y.reducedIrreducibleComponent W hW ⟶ Y :=
    Y.reducedIrreducibleComponentι W hW
  let c : X.reducedIrreducibleComponent Z hZ ⟶ Y.reducedIrreducibleComponent W hW :=
    X.reducedIrreducibleComponentMap f Z hZ W hW himage
  let P : Scheme.{u} := pullback f iW
  let p : P ⟶ X := pullback.fst f iW
  let q : P ⟶ Y.reducedIrreducibleComponent W hW := pullback.snd f iW
  let k : X.reducedIrreducibleComponent Z hZ ⟶ P :=
    pullback.lift iZ c (reducedIrreducibleComponentMap_ι f Z hZ W hW himage).symm
  have hkp : k ≫ p = iZ := pullback.lift_fst _ _ _
  have hkq : k ≫ q = c := pullback.lift_snd _ _ _
  let : IsClosedImmersion (k ≫ p) := hkp.symm ▸ inferInstance
  let : IsClosedImmersion k := IsClosedImmersion.of_comp k p
  have hrange : p '' Set.range k = Z := by
    rw [← Set.range_comp]
    exact (congrArg (fun g : X.reducedIrreducibleComponent Z hZ ⟶ X => Set.range g)
      hkp).trans (range_reducedIrreducibleComponentι X Z hZ)
  have hirred : Set.range k ∈ irreducibleComponents P := by
    refine ⟨?_, ?_⟩
    · simpa only [Set.image_univ] using
        (IrreducibleSpace.isIrreducible_univ
          (X.reducedIrreducibleComponent Z hZ)).image k k.continuous.continuousOn
    · intro V hV hsub x hxV
      have hZV : Z ⊆ p '' V := by
        rw [← hrange]
        exact Set.image_mono hsub
      have hpV : p '' V ⊆ Z := hZ.2 (hV.image p p.continuous.continuousOn) hZV
      have hxZ : p x ∈ Z := hpV ⟨x, hxV, rfl⟩
      rw [← hrange] at hxZ
      obtain ⟨y, hy, hyx⟩ := hxZ
      exact p.isClosedEmbedding.injective hyx ▸ hy
  have hopen : IsOpen (Set.range k) :=
    isOpen_irreducibleComponent_of_isDomain_stalk P hdom (Set.range k) hirred
  let (x : P) : _root_.IsReduced (P.presheaf.stalk x) := by
    let : IsDomain (P.presheaf.stalk x) := hdom x
    infer_instance
  let : IsReduced P := isReduced_of_isReduced_stalk P
  let : IsOpenImmersion k := isOpenImmersion_of_isClosedImmersion_of_isOpen_range k hopen
  let : Etale c := by
    rw [← hkq]
    infer_instance
  change IsFiniteEtale c
  exact IsFiniteEtale.mk

namespace IdealSheafData

/-- The structural morphism of a pulled-back component is the composite of
the actual map of reduced components with the downstairs structural map. -/
theorem componentToBase_comap_eq
    {X Y S : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) (p : X ⟶ S)
    (Z : Set (I.comap f).subscheme)
    (hZ : Z ∈ irreducibleComponents (I.comap f).subscheme)
    (W : Set I.subscheme) (hW : W ∈ irreducibleComponents I.subscheme)
    (himage : I.comapSubschemeTo f '' Z = W) :
    (I.comap f).componentToBase (f ≫ p) Z hZ =
      (I.comap f).subscheme.reducedIrreducibleComponentMap
        (I.comapSubschemeTo f) Z hZ W hW himage ≫ I.componentToBase p W hW := by
  simp only [componentToBase, reducedIrreducibleComponentMap_ι_assoc,
    comapSubschemeTo_subschemeι_assoc]

end IdealSheafData

end AlgebraicGeometry.Scheme
