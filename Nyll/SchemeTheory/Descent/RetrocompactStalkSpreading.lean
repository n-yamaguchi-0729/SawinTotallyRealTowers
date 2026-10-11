/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.StalkSpreading
import Nyll.SchemeTheory.LocalGeometry.CompactOpenSpecialization
import Nyll.SchemeTheory.Morphisms.UnramifiedHomExt
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Compatible spreading from a stalk over a retrocompact open

The disagreement locus is clopen in the overlap with an affine neighborhood.
Retrocompactness of the original open makes that locus compact. Stalk
compatibility excludes every generization of the chosen point from this
compact open locus. Constructible compactness then gives a neighborhood
on which the two actual morphisms agree.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A stalk section compatible with a retrocompact open section extends
compatibly to a neighborhood, with no finite-component hypothesis. -/
theorem exists_compatible_open_extension_fromSpecStalk_of_quasiCompact
    {X Y : Scheme.{u}} [IsAffine X]
    (f : Y ⟶ X) [Etale f] [IsSeparated f]
    (U : X.Opens) [QuasiCompact U.ι]
    (s : U.toScheme ⟶ Y) (hs : s ≫ f = U.ι)
    (x : X) (a : Spec (X.presheaf.stalk x) ⟶ Y)
    (ha : a ≫ f = X.fromSpecStalk x)
    (hcompat : pullback.snd (X.fromSpecStalk x) U.ι ≫ s =
      pullback.fst (X.fromSpecStalk x) U.ι ≫ a) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (b : V.toScheme ⟶ Y),
      V.fromSpecStalkOfMem x hxV ≫ b = a ∧ b ≫ f = V.ι ∧
      X.homOfLE (show U ⊓ V ≤ U from inf_le_left) ≫ s =
        X.homOfLE (show U ⊓ V ≤ V from inf_le_right) ≫ b := by
  obtain ⟨W, hxW, b, hba, hbf⟩ :=
    Scheme.exists_open_extension_fromSpecStalk_of_isAffine (X := X) f x a ha
  obtain ⟨A, hA, hxA, hAWset⟩ := exists_isAffineOpen_mem_and_subset hxW
  have hAW : A ≤ W := fun _y hy => hAWset hy
  let bA : A.toScheme ⟶ Y := X.homOfLE hAW ≫ b
  have hAWstalk : A.fromSpecStalkOfMem x hxA ≫ X.homOfLE hAW =
      W.fromSpecStalkOfMem x hxW := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  have hbAa : A.fromSpecStalkOfMem x hxA ≫ bA = a := by
    rw [← Category.assoc, hAWstalk, hba]
  have hbAf : bA ≫ f = A.ι := by
    rw [Category.assoc, hbf, Scheme.homOfLE_ι]
  let O : X.Opens := U ⊓ A
  let dU : O.toScheme ⟶ U.toScheme := X.homOfLE inf_le_left
  let dA : O.toScheme ⟶ A.toScheme := X.homOfLE inf_le_right
  have hOcompact : IsCompact (O : Set X) := by
    have h := (U.ι.isCompact_preimage hA.isCompact).image U.ι.continuous
    change IsCompact (U.ι '' (U.ι ⁻¹' (A : Set X))) at h
    rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_comm] at h
    exact h
  have : CompactSpace O.toScheme := isCompact_iff_compactSpace.mp hOcompact
  let s₁ : Over.mk O.ι ⟶ Over.mk f := Over.homMk (dU ≫ s) (by
    change (dU ≫ s) ≫ f = O.ι
    rw [Category.assoc, hs, Scheme.homOfLE_ι])
  let s₂ : Over.mk O.ι ⟶ Over.mk f := Over.homMk (dA ≫ bA) (by
    change (dA ≫ bA) ≫ f = O.ι
    rw [Category.assoc, hbAf, Scheme.homOfLE_ι])
  have : FormallyUnramified (Over.mk f).hom := inferInstanceAs (FormallyUnramified f)
  have : LocallyOfFiniteType (Over.mk f).hom := inferInstanceAs (LocallyOfFiniteType f)
  have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  let e : (equalizer s₁ s₂).left ⟶ O.toScheme := (equalizer.ι s₁ s₂).left
  have heopen : IsOpen (Set.range e) := IsOpenImmersion.isOpen_range e
  have heclosed : IsClosed (Set.range e) := e.isClosedEmbedding.isClosed_range
  let K : Set X := O.ι '' (Set.range e)ᶜ
  have hKopen : IsOpen K := O.ι.isOpenEmbedding.isOpenMap _ heclosed.isOpen_compl
  have hKcompact : IsCompact K := heopen.isClosed_compl.isCompact.image O.ι.continuous
  let q : Spec (X.presheaf.stalk x) ⟶ X := X.fromSpecStalk x
  let qO : pullback O.ι q ⟶ O.toScheme := pullback.fst O.ι q
  let qS : pullback O.ι q ⟶ Spec (X.presheaf.stalk x) := pullback.snd O.ι q
  have hkcond : qS ≫ q = (qO ≫ dU) ≫ U.ι := by
    rw [Category.assoc, Scheme.homOfLE_ι]
    exact pullback.condition.symm
  let k : pullback O.ι q ⟶ pullback q U.ι := pullback.lift qS (qO ≫ dU) hkcond
  have hk : (qO ≫ dU) ≫ s = qS ≫ a := by
    have hkfst : k ≫ pullback.fst q U.ι = qS := pullback.lift_fst _ _ _
    have hksnd : k ≫ pullback.snd q U.ι = qO ≫ dU := pullback.lift_snd _ _ _
    have ht : k ≫ (pullback.snd q U.ι ≫ s) = k ≫ (pullback.fst q U.ι ≫ a) :=
      congrArg (fun z : pullback q U.ι ⟶ Y => k ≫ z) hcompat
    rw [← Category.assoc, hksnd, ← Category.assoc, hkfst] at ht
    exact ht
  have hqA : qS ≫ A.fromSpecStalkOfMem x hxA = qO ≫ dA := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Category.assoc, Scheme.homOfLE_ι]
    exact pullback.condition.symm
  have heq : qO ≫ (dU ≫ s) = qO ≫ (dA ≫ bA) := by
    rw [← Category.assoc, hk, ← hbAa, ← Category.assoc,
      hqA, Category.assoc]
  let q' : Over.mk (qO ≫ O.ι) ⟶ Over.mk O.ι := Over.homMk qO rfl
  have hq' : q' ≫ s₁ = q' ≫ s₂ := Over.OverMorphism.ext heq
  let l : Over.mk (qO ≫ O.ι) ⟶ equalizer s₁ s₂ := equalizer.lift q' hq'
  have hle : l.left ≫ e = qO :=
    congrArg (fun z : Over.mk (qO ≫ O.ι) ⟶ Over.mk O.ι => z.left)
      (equalizer.lift_ι q' hq')
  have havoid : ∀ y ∈ K, ¬ y ⤳ x := by
    rintro y ⟨yO, hyO, hy⟩ hyx
    have hyrange : y ∈ Set.range (pullback.fst O.ι q ≫ O.ι) := by
      rw [IsOpenImmersion.range_pullback_to_base_of_left,
        Scheme.Opens.range_ι, Scheme.range_fromSpecStalk]
      exact ⟨hy ▸ yO.2, hyx⟩
    obtain ⟨p, hp⟩ := hyrange
    have hpO : qO p = yO := O.ι.isOpenEmbedding.injective (hp.trans hy.symm)
    apply hyO
    refine ⟨l.left p, ?_⟩
    exact (congrArg (fun z : pullback O.ι q ⟶ O.toScheme => z p) hle).trans hpO
  have : SpectralSpace (Spec Γ(X, ⊤)) :=
    inferInstanceAs (SpectralSpace (PrimeSpectrum Γ(X, ⊤)))
  have : SpectralSpace X := X.isoSpec.hom.homeomorph.isOpenEmbedding.spectralSpace
  obtain ⟨N, hxN, hNK⟩ :=
    exists_open_nhds_disjoint_of_forall_not_specializes K hKopen hKcompact x havoid
  let V : X.Opens := A ⊓ N
  have hxV : x ∈ V := ⟨hxA, hxN⟩
  let iA : V.toScheme ⟶ A.toScheme := X.homOfLE inf_le_left
  let bV : V.toScheme ⟶ Y := iA ≫ bA
  have hiAstalk : V.fromSpecStalkOfMem x hxV ≫ iA =
      A.fromSpecStalkOfMem x hxA := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  have hbVa : V.fromSpecStalkOfMem x hxV ≫ bV = a := by
    rw [← Category.assoc, hiAstalk, hbAa]
  have hbVf : bV ≫ f = V.ι := by
    rw [Category.assoc, hbAf, Scheme.homOfLE_ι]
  have hVO : U ⊓ V ≤ O := inf_le_inf le_rfl inf_le_left
  let j : (U ⊓ V).toScheme ⟶ O.toScheme := X.homOfLE hVO
  have hjrange : Set.range j ⊆ Set.range e := by
    rintro y ⟨z, rfl⟩
    by_contra hz
    have hbad : O.ι (j z) ∈ K := ⟨j z, hz, rfl⟩
    have hjι : j ≫ O.ι = (U ⊓ V).ι := X.homOfLE_ι hVO
    have hy : O.ι (j z) = z.1 :=
      congrArg (fun m : (U ⊓ V).toScheme ⟶ X => m z) hjι
    have hzN : O.ι (j z) ∈ N := hy.symm ▸ z.2.2.2
    exact (Set.disjoint_left.mp hNK) hzN hbad
  let jE : (U ⊓ V).toScheme ⟶ (equalizer s₁ s₂).left :=
    IsOpenImmersion.lift e j hjrange
  have hjE : jE ≫ e = j := IsOpenImmersion.lift_fac e j hjrange
  have hecondition : e ≫ (dU ≫ s) = e ≫ (dA ≫ bA) :=
    congrArg (fun z : equalizer s₁ s₂ ⟶ Over.mk f => z.left)
      (equalizer.condition s₁ s₂)
  have hjcondition : j ≫ (dU ≫ s) = j ≫ (dA ≫ bA) := by
    rw [← hjE, Category.assoc, Category.assoc, hecondition]
  refine ⟨V, hxV, bV, hbVa, hbVf, ?_⟩
  simpa only [j, dU, dA, bV, iA, ← Category.assoc,
    Scheme.homOfLE_homOfLE] using hjcondition

end AlgebraicGeometry.Scheme
