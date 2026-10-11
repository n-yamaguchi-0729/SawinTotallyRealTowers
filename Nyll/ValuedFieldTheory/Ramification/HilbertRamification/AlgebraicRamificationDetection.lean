/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.BaseChange
import Nyll.ValuedFieldTheory.Valuation.ComapResidueCharacteristic
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Detecting absolute ramification on finite Galois layers

For an actual inertia element, ramification can be tested after restriction
to every finite Galois intermediate field. A failure of the defining
principal-unit condition involves one unit, which already lies in one such
finite layer. No Henselianity or residue-characteristic hypothesis is used.
-/


namespace RamificationTheory.HilbertRamification.ValuationSubring

universe u v

/-- Membership in actual ramification, inside inertia, is equivalent to
ramification of all finite Galois restrictions in their ambient automorphism
groups. This is the finite-coordinate membership test used on compact inertia. -/
theorem mem_ramificationGroup_iff_forall_finiteGalois_restrict
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) :
    σ ∈ ramificationGroup K A ↔
      ∀ E : FiniteGaloisIntermediateField K L,
        AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E
            (inertiaGroupToAut (K := K) A σ) ∈
          ramificationGroupInAut K (A.comap E.toIntermediateField.val.toRingHom) := by
  constructor
  · intro hσ E
    let i : E →+* L := E.toIntermediateField.val.toRingHom
    let B : _root_.ValuationSubring E := A.comap i
    have hsquare : i.comp (algebraMap K E) =
        (algebraMap K L).comp (RingHom.id K) := by
      apply RingHom.ext
      intro a
      exact E.toIntermediateField.val.commutes a
    let ρ : ramificationGroup K A →* ramificationGroup K B :=
      _root_.HilbertRamification.ValuationSubring.galoisPullback_ramificationGroupMap
        (RingHom.id K) i hsquare A
    let τ : ramificationGroup K B := ρ ⟨σ, hσ⟩
    refine ⟨(τ : inertiaGroup K B), τ.property, ?_⟩
    apply AlgEquiv.ext
    intro z
    apply i.injective
    calc
      i (inertiaGroupToAut (K := K) B (τ : inertiaGroup K B) z) =
          inertiaGroupToAut (K := K) A σ (i z) :=
        _root_.HilbertRamification.galoisPullback_galoisPullback_commutes
          (RingHom.id K) i hsquare (inertiaGroupToAut (K := K) A σ) z
      _ = i ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E
          (inertiaGroupToAut (K := K) A σ)) z) :=
        (AlgEquiv.restrictNormal_commutes (inertiaGroupToAut (K := K) A σ) E z).symm
  · intro hσ x
    let E : FiniteGaloisIntermediateField K L :=
      FiniteGaloisIntermediateField.adjoin K {(x : L)}
    let i : E →+* L := E.toIntermediateField.val.toRingHom
    let B : _root_.ValuationSubring E := A.comap i
    have hx : (x : L) ∈ E.toIntermediateField :=
      FiniteGaloisIntermediateField.subset_adjoin K {(x : L)} (Set.mem_singleton _)
    let z : E := ⟨(x : L), hx⟩
    have hz : z ≠ 0 := by
      intro h
      exact Units.ne_zero x (congrArg (fun a : E => (a : L)) h)
    let y : Eˣ := Units.mk0 z hz
    obtain ⟨τ, hτ, hτσ⟩ := hσ E
    have hquot :
        Units.map i (automorphismUnitQuotient K B (τ : decompositionGroup K B) y) =
          automorphismUnitQuotient K A (σ : decompositionGroup K A) x := by
      apply Units.ext
      simp only [Units.coe_map, automorphismUnitQuotient, Units.val_div_eq_div_val,
        Units.coe_mapEquiv]
      change i ((inertiaGroupToAut (K := K) B τ) (y : E) / (y : E)) =
        (inertiaGroupToAut (K := K) A σ) (x : L) / (x : L)
      rw [map_div₀]
      have hτy := congrArg (fun f : E ≃ₐ[K] E => i (f (y : E))) hτσ
      have hres := AlgEquiv.restrictNormal_commutes
        (inertiaGroupToAut (K := K) A σ) E (y : E)
      exact congrArg₂ (fun a b : L => a / b) (hτy.trans hres) rfl
    have hnonunit :
        ((automorphismUnitQuotient K B (τ : decompositionGroup K B) y : E) - 1) ∈
          B.nonunits :=
      B.mem_nonunits_iff.mpr (hτ y)
    have hmapped :=
      (_root_.ValuationSubring.mem_nonunits_comap_iff A i
        ((automorphismUnitQuotient K B (τ : decompositionGroup K B) y : E) - 1)).mp
        hnonunit
    rw [map_sub, map_one] at hmapped
    have hcoe := congrArg (fun a : Lˣ => (a : L)) hquot
    change i (automorphismUnitQuotient K B (τ : decompositionGroup K B) y : E) =
      (automorphismUnitQuotient K A (σ : decompositionGroup K A) x : L) at hcoe
    rw [hcoe] at hmapped
    exact A.mem_nonunits_iff.mp hmapped

end RamificationTheory.HilbertRamification.ValuationSubring
