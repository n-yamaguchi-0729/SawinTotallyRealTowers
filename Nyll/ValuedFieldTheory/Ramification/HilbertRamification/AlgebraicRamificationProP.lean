/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.BaseChange
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteRamificationPrimary
import Nyll.ValuedFieldTheory.Valuation.ComapResidueCharP
import Nyll.ProCGroups.FiniteGroups.StandardClasses
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import Mathlib.FieldTheory.Galois.Profinite

/-!
# The actual ramification subgroup is pro-p

Restriction to a finite Galois layer lands in that layer's actual ramification
group. Its finite image is therefore a p-group in residue characteristic p.
The kernels of these continuous restrictions form a Krull neighborhood basis.
No surjectivity of restriction on ramification groups is required.
-/


namespace RamificationTheory.HilbertRamification.ValuationSubring

open ProCGroups.ProC
open scoped Topology

noncomputable section

universe u v

private theorem restrictNormal_ramification_range_isPGroup
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField A) p]
    (E : FiniteGaloisIntermediateField K L) :
    IsPGroup p
      (((AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).comp
        (ramificationGroupInAut K A).subtype).range) := by
  let i : E →+* L := E.toIntermediateField.val.toRingHom
  let B : _root_.ValuationSubring E := A.comap i
  have : CharP (IsLocalRing.ResidueField B) p :=
    _root_.ValuationSubring.charP_residueField_comap A i p
  have hsquare : i.comp (algebraMap K E) =
      (algebraMap K L).comp (RingHom.id K) := by
    apply RingHom.ext
    intro a
    exact E.toIntermediateField.val.commutes a
  let ρ : ramificationGroup K A →* ramificationGroup K B :=
    _root_.HilbertRamification.ValuationSubring.galoisPullback_ramificationGroupMap
      (RingHom.id K) i hsquare A
  let φ : ramificationGroup K B →* (E ≃ₐ[K] E) :=
    (inertiaGroupToAut (K := K) B).comp (ramificationGroup K B).subtype
  have hfiniteP : IsPGroup p (ramificationGroup K B) :=
    ramificationGroup_isPGroup_of_residueChar K B p
  intro x
  obtain ⟨σ, hσx⟩ := x.property
  let τ : ramificationGroup K A :=
    (ramificationGroupEquivInAut (K := K) A).symm σ
  have hτσ : inertiaGroupToAut (K := K) A (τ : inertiaGroup K A) =
      (σ : L ≃ₐ[K] L) :=
    congrArg (fun g : ramificationGroupInAut K A => (g : L ≃ₐ[K] L))
      ((ramificationGroupEquivInAut (K := K) A).apply_symm_apply σ)
  have hρ : (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E)
      (σ : L ≃ₐ[K] L) = φ (ρ τ) := by
    apply AlgEquiv.ext
    intro z
    apply i.injective
    calc
      i (((AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E)
          (σ : L ≃ₐ[K] L)) z) = (σ : L ≃ₐ[K] L) (i z) :=
        AlgEquiv.restrictNormal_commutes (σ : L ≃ₐ[K] L) E z
      _ = (inertiaGroupToAut (K := K) A (τ : inertiaGroup K A)) (i z) := by
        rw [hτσ]
      _ = i (φ (ρ τ) z) :=
        (_root_.HilbertRamification.galoisPullback_galoisPullback_commutes
          (RingHom.id K) i hsquare
          (inertiaGroupToAut (K := K) A (τ : inertiaGroup K A)) z).symm
  obtain ⟨a, ha⟩ := hfiniteP (ρ τ)
  refine ⟨a, Subtype.ext ?_⟩
  change (x : E ≃ₐ[K] E) ^ (p ^ a) = 1
  calc
    (x : E ≃ₐ[K] E) ^ (p ^ a) = (φ (ρ τ)) ^ (p ^ a) :=
      congrArg (fun g : E ≃ₐ[K] E => g ^ (p ^ a)) (hσx.symm.trans hρ)
    _ = φ ((ρ τ) ^ (p ^ a)) := (map_pow φ (ρ τ) (p ^ a)).symm
    _ = 1 := by rw [ha, map_one]

/-- For an algebraic Galois extension, the actual ramification subgroup in
the ambient automorphism group has an open-normal p-group basis in residue
characteristic p. No Henselianity, discreteness, or residue perfectness is needed. -/
theorem ramificationGroupInAut_hasOpenNormalBasisInClass_of_isGalois_residueChar
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (A : _root_.ValuationSubring L) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField A) p] :
    HasOpenNormalBasisInClass (ProCGroups.FiniteGroupClass.pGroup p)
      (ramificationGroupInAut K A) := by
  intro W hW h1W
  let R : Subgroup (L ≃ₐ[K] L) := ramificationGroupInAut K A
  obtain ⟨W₀, hW₀, hW₀W⟩ :=
    (mem_nhds_subtype (R : Set (L ≃ₐ[K] L)) (1 : R) W).mp (hW.mem_nhds h1W)
  obtain ⟨E, hE⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
      (k := K) (K := L) W₀).mp hW₀
  let f : R →ₜ* (E ≃ₐ[K] E) :=
    { toMonoidHom :=
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).comp R.subtype
      continuous_toFun :=
        (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField).comp
          continuous_subtype_val }
  let U : OpenNormalSubgroup R := ProCGroups.ProC.OpenNormalSubgroup.ker f
  refine ⟨U, ?_, ?_⟩
  · intro σ hσ
    have hfix : (σ : L ≃ₐ[K] L) ∈ E.fixingSubgroup :=
      (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff
        (σ : L ≃ₐ[K] L) E).mpr hσ
    exact hW₀W (hE hfix)
  · change ProCGroups.FiniteGroupClass.pGroup p (R ⧸ f.toMonoidHom.ker)
    exact (ProCGroups.FiniteGroupClass.pGroup p).mem_of_mulEquiv
      (QuotientGroup.quotientKerEquivRange f.toMonoidHom).symm
      ⟨inferInstance, restrictNormal_ramification_range_isPGroup K A p E⟩

end

end RamificationTheory.HilbertRamification.ValuationSubring
