/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteInertiaRestriction
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianInertiaRestriction
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteInertiaStructure
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicRamificationDetection
import Nyll.ValuedFieldTheory.Ramification.ClosedSubgroups
import Nyll.ValuedFieldTheory.Valuation.ComapResidueCharP
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Surjectivity of absolute wild inertia restriction

The finite ramification subgroup is the Sylow subgroup of finite inertia for
the residue characteristic. Surjectivity of actual inertia restriction gives
compatible finite ramification lifts. Compactness then supplies an absolute
inertia element whose restrictions at every finite layer are ramified.
-/


namespace RamificationTheory.HilbertRamification.ValuationSubring

open scoped Topology

noncomputable section

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

private theorem restrictNormal_ramification_mono
    (A : _root_.ValuationSubring L)
    (E F : FiniteGaloisIntermediateField K L) (hEF : E ≤ F)
    (σ : L ≃ₐ[K] L)
    (hσ : AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F σ ∈
      ramificationGroupInAut K (A.comap F.toIntermediateField.val.toRingHom)) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E σ ∈
      ramificationGroupInAut K (A.comap E.toIntermediateField.val.toRingHom) := by
  let i : E →+* F := (IntermediateField.inclusion hEF).toRingHom
  let B : _root_.ValuationSubring F := A.comap F.toIntermediateField.val.toRingHom
  have hsquare : i.comp (algebraMap K E) =
      (algebraMap K F).comp (RingHom.id K) := by
    apply RingHom.ext
    intro a
    exact (IntermediateField.inclusion hEF).commutes a
  obtain ⟨τ, hτ, hτσ⟩ := hσ
  let ρ : ramificationGroup K B →* ramificationGroup K (B.comap i) :=
    _root_.HilbertRamification.ValuationSubring.galoisPullback_ramificationGroupMap
      (RingHom.id K) i hsquare B
  let t : ramificationGroup K (B.comap i) := ρ ⟨τ, hτ⟩
  refine ⟨(t : inertiaGroup K (B.comap i)), t.property, ?_⟩
  apply AlgEquiv.ext
  intro x
  apply E.toIntermediateField.val.injective
  calc
    _ = F.toIntermediateField.val (inertiaGroupToAut (K := K) B τ (i x)) :=
      congrArg F.toIntermediateField.val
        (_root_.HilbertRamification.galoisPullback_galoisPullback_commutes
          (RingHom.id K) i hsquare (inertiaGroupToAut (K := K) B τ) x)
    _ = F.toIntermediateField.val
        ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F σ) (i x)) := by
      rw [hτσ]
    _ = σ (E.toIntermediateField.val x) :=
      AlgEquiv.restrictNormal_commutes σ F (i x)
    _ = _ := (AlgEquiv.restrictNormal_commutes σ E x).symm

private theorem exists_inertia_with_finite_ramification_and_restriction
    [IsGalois K L]
    (V : _root_.ValuationSubring K)
    [HenselianRing V (IsLocalRing.maximalIdeal V)]
    (A : _root_.ValuationSubring L) [V.valuation.HasExtension A.valuation]
    (E F : FiniteGaloisIntermediateField K L) (hEF : E ≤ F)
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (τ : ramificationGroup K (A.comap E.toIntermediateField.val.toRingHom)) :
    ∃ σ : inertiaGroup K A,
      finiteInertiaRestriction A F σ ∈
        ramificationGroup K (A.comap F.toIntermediateField.val.toRingHom) ∧
      finiteInertiaRestriction A E σ = (τ : inertiaGroup K _) := by
  let i : E →+* F := (IntermediateField.inclusion hEF).toRingHom
  let B : _root_.ValuationSubring F := A.comap F.toIntermediateField.val.toRingHom
  let C : _root_.ValuationSubring E := A.comap E.toIntermediateField.val.toRingHom
  have : CharP (IsLocalRing.ResidueField B) p :=
    _root_.ValuationSubring.charP_residueField_comap A F.toIntermediateField.val.toRingHom p
  have : CharP (IsLocalRing.ResidueField C) p :=
    _root_.ValuationSubring.charP_residueField_comap A E.toIntermediateField.val.toRingHom p
  have hsquare : i.comp (algebraMap K E) =
      (algebraMap K F).comp (RingHom.id K) := by
    apply RingHom.ext
    intro a
    exact (IntermediateField.inclusion hEF).commutes a
  let f : inertiaGroup K B →* inertiaGroup K C :=
    _root_.HilbertRamification.ValuationSubring.galoisPullback_inertiaGroupMap
      (RingHom.id K) i hsquare B
  have hcomp (σ : inertiaGroup K A) :
      f (finiteInertiaRestriction A F σ) = finiteInertiaRestriction A E σ := by
    apply Subtype.ext
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    apply E.toIntermediateField.val.injective
    calc
      _ = F.toIntermediateField.val
          (inertiaGroupToAut (K := K) B (finiteInertiaRestriction A F σ) (i x)) :=
        congrArg F.toIntermediateField.val
          (_root_.HilbertRamification.galoisPullback_galoisPullback_commutes
            (RingHom.id K) i hsquare
            (inertiaGroupToAut (K := K) B (finiteInertiaRestriction A F σ)) x)
      _ = inertiaGroupToAut (K := K) A σ (E.toIntermediateField.val x) := by
        rw [finiteInertiaRestriction_coe]
        exact AlgEquiv.restrictNormal_commutes (inertiaGroupToAut (K := K) A σ) F (i x)
      _ = _ := by
        have hcoe :=
          congrArg
            (fun g : E ≃ₐ[K] E => E.toIntermediateField.val (g x))
            (finiteInertiaRestriction_coe A E σ)
        exact
          (AlgEquiv.restrictNormal_commutes
            (inertiaGroupToAut (K := K) A σ) E x).symm.trans hcoe.symm
  have hf : Function.Surjective f := by
    intro t
    obtain ⟨σ, hσ⟩ :=
      galoisPullback_inertiaGroupMap_surjective_of_henselianRing V A E.toIntermediateField t
    exact ⟨finiteInertiaRestriction A F σ, (hcomp σ).trans hσ⟩
  let P : Sylow p (inertiaGroup K B) := Sylow.nonempty.some
  have hP : (P : Subgroup (inertiaGroup K B)) = ramificationGroup K B :=
    sylow_eq_ramificationGroup_of_residueChar K B p P
  have hmap : (ramificationGroup K B).map f = ramificationGroup K C := by
    have hQ := sylow_eq_ramificationGroup_of_residueChar K C p (P.mapSurjective hf)
    change (P : Subgroup (inertiaGroup K B)).map f = ramificationGroup K C at hQ
    rwa [hP] at hQ
  have hτ : (τ : inertiaGroup K C) ∈ (ramificationGroup K B).map f := by
    rw [hmap]
    exact τ.property
  obtain ⟨t, ht, htτ⟩ := Subgroup.mem_map.mp hτ
  obtain ⟨σ, hσ⟩ :=
    galoisPullback_inertiaGroupMap_surjective_of_henselianRing V A F.toIntermediateField t
  refine ⟨σ, ?_, ?_⟩
  · change finiteInertiaRestriction A F σ ∈ ramificationGroup K B
    rw [show finiteInertiaRestriction A F σ = t from hσ]
    exact ht
  · calc
      finiteInertiaRestriction A E σ = f (finiteInertiaRestriction A F σ) := (hcomp σ).symm
      _ = f t := congrArg f hσ
      _ = (τ : inertiaGroup K C) := htτ

/-- Restriction of actual ramification from an algebraic Galois extension to
every finite Galois intermediate field is surjective over a Henselian base in
positive residue characteristic. No discreteness or residue perfectness is needed. -/
theorem galoisPullback_ramificationGroupMap_surjective_of_isGalois_henselianRing
    [IsGalois K L]
    (V : _root_.ValuationSubring K)
    [HenselianRing V (IsLocalRing.maximalIdeal V)]
    (A : _root_.ValuationSubring L) [V.valuation.HasExtension A.valuation]
    (E : FiniteGaloisIntermediateField K L)
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    Function.Surjective
      (_root_.HilbertRamification.ValuationSubring.galoisPullback_ramificationGroupMap
        (RingHom.id K) E.toIntermediateField.val.toRingHom
        (by
          apply RingHom.ext
          intro a
          exact E.toIntermediateField.val.commutes a) A) := by
  intro τ
  let C : FiniteGaloisIntermediateField K L → Set (L ≃ₐ[K] L) := fun F =>
    {σ | σ ∈ inertiaGroupInAut K A ∧
      AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F σ ∈
        ramificationGroupInAut K (A.comap F.toIntermediateField.val.toRingHom) ∧
      AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E σ =
        inertiaGroupToAut (K := K) (A.comap E.toIntermediateField.val.toRingHom) τ}
  have hclosed (F : FiniteGaloisIntermediateField K L) : IsClosed (C F) :=
    (inertiaGroupInAut_isClosed K A).inter
      (((ramificationGroupInAut_isClosed K
        (A.comap F.toIntermediateField.val.toRingHom)).preimage
          (InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField)).inter
        (isClosed_eq
          (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField) continuous_const))
  have hnonempty (F : FiniteGaloisIntermediateField K L) : (C F).Nonempty := by
    obtain ⟨σ, hσR, hσE⟩ :=
      exists_inertia_with_finite_ramification_and_restriction V A E (F ⊔ E) le_sup_right p τ
    refine ⟨inertiaGroupToAut (K := K) A σ, ?_, ?_, ?_⟩
    · exact ⟨(σ : decompositionGroup K A), σ.property, rfl⟩
    · apply restrictNormal_ramification_mono A F (F ⊔ E) le_sup_left
      rw [← finiteInertiaRestriction_coe]
      exact ⟨finiteInertiaRestriction A (F ⊔ E) σ, hσR, rfl⟩
    · rw [← finiteInertiaRestriction_coe, hσE]
  have hdir : Directed (· ⊇ ·) C := by
    intro F₁ F₂
    refine ⟨F₁ ⊔ F₂, ?_, ?_⟩
    · intro σ hσ
      exact ⟨hσ.1,
        restrictNormal_ramification_mono A F₁ (F₁ ⊔ F₂) le_sup_left σ hσ.2.1, hσ.2.2⟩
    · intro σ hσ
      exact ⟨hσ.1,
        restrictNormal_ramification_mono A F₂ (F₁ ⊔ F₂) le_sup_right σ hσ.2.1, hσ.2.2⟩
  obtain ⟨σ, hσ⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hnonempty
      (fun F => (hclosed F).isCompact) hclosed
  have hσF (F : FiniteGaloisIntermediateField K L) := Set.mem_iInter.mp hσ F
  obtain ⟨δ, hδ, hδσ⟩ := (hσF E).1
  let s : inertiaGroup K A := ⟨δ, hδ⟩
  have hsσ : inertiaGroupToAut (K := K) A s = σ := hδσ
  have hsR : s ∈ ramificationGroup K A :=
    (mem_ramificationGroup_iff_forall_finiteGalois_restrict K A s).mpr fun F => by
      rw [hsσ]
      exact (hσF F).2.1
  refine ⟨⟨s, hsR⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change inertiaGroupToAut (K := K) (A.comap E.toIntermediateField.val.toRingHom)
      (finiteInertiaRestriction A E s) =
    inertiaGroupToAut (K := K) (A.comap E.toIntermediateField.val.toRingHom) τ
  rw [finiteInertiaRestriction_coe, hsσ]
  exact (hσF E).2.2

end

end RamificationTheory.HilbertRamification.ValuationSubring
