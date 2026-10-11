/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The residue-field pushout of a local ring map

When the extended maximal ideal is the maximal ideal of the target,
the actual square of the ring map and the two residue maps is a pushout.
The universal factorization is the quotient lift of the given map from
the target ring; its kernel containment follows from the supplied cocone.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

universe u

/-- Extending the maximal ideal to the target maximal ideal identifies the
closed-fibre base change with the target residue field, as an actual pushout. -/
lemma isPushout_residue_of_maximalIdeal_map_eq
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    (hMaximal : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B) :
    IsPushout (ofHom (IsLocalRing.residue A)) (ofHom (algebraMap A B))
      (ofHom (IsLocalRing.ResidueField.map (algebraMap A B)))
      (ofHom (IsLocalRing.residue B)) := by
  let α : of A ⟶ of (IsLocalRing.ResidueField A) := ofHom (IsLocalRing.residue A)
  let β : of A ⟶ of B := ofHom (algebraMap A B)
  let δ : of (IsLocalRing.ResidueField A) ⟶ of (IsLocalRing.ResidueField B) :=
    ofHom (IsLocalRing.ResidueField.map (algebraMap A B))
  let ε : of B ⟶ of (IsLocalRing.ResidueField B) := ofHom (IsLocalRing.residue B)
  have comm : α ≫ δ = β ≫ ε := by
    ext a
    exact IsLocalRing.ResidueField.map_residue (algebraMap A B) a
  have hKernel (s : PushoutCocone α β) :
      IsLocalRing.maximalIdeal B ≤ RingHom.ker s.inr.hom := by
    rw [← hMaximal, Ideal.map_le_iff_le_comap]
    intro a ha
    change s.inr (algebraMap A B a) = 0
    have hs := congrArg (fun h : of A ⟶ s.pt => h a) s.condition
    have hZero : IsLocalRing.residue A a = 0 :=
      (IsLocalRing.residue_eq_zero_iff a).mpr ha
    calc
      s.inr (algebraMap A B a) = s.inl (IsLocalRing.residue A a) := hs.symm
      _ = 0 := by rw [hZero, map_zero]
  let desc (s : PushoutCocone α β) : of (IsLocalRing.ResidueField B) ⟶ s.pt :=
    ofHom (Ideal.Quotient.lift (IsLocalRing.maximalIdeal B) s.inr.hom (hKernel s))
  have desc_residue (s : PushoutCocone α β) (b : B) :
      desc s (IsLocalRing.residue B b) = s.inr b := rfl
  change IsPushout α β δ ε
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk comm desc ?_ ?_ ?_)
  · intro s
    ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change desc s (IsLocalRing.ResidueField.map (algebraMap A B)
      (IsLocalRing.residue A a)) = s.inl (IsLocalRing.residue A a)
    rw [IsLocalRing.ResidueField.map_residue, desc_residue]
    exact (congrArg (fun h : of A ⟶ s.pt => h a) s.condition).symm
  · intro s
    ext b
    exact desc_residue s b
  · intro s m _ hm
    ext x
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective x
    exact (congrArg (fun h : of B ⟶ s.pt => h b) hm).trans (desc_residue s b).symm

end CommRingCat
