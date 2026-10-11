/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Finite models of localizations of integral algebras

If a principal localization of an integral algebra is of finite type, finitely
many numerators of algebra generators already generate that localization. They
can be adjoined together with any prescribed finite set before localizing. The
resulting subalgebra is finite as a module by integrality.
-/


@[expose] public section

universe u v

namespace Algebra

/-- A principal localization of an integral algebra that is of finite type comes
from a finite subalgebra containing any prescribed finite set and the element
being inverted. The comparison is the canonical localization map. -/
theorem exists_finite_subalgebra_awayMap_bijective_of_finiteType
    {R : Type u} {C : Type v} [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.IsIntegral R C] (b : C) [Algebra.FiniteType R (Localization.Away b)]
    (T : Set C) (hT : T.Finite) :
    ∃ S : Subalgebra R C, Module.Finite R S ∧ T ⊆ S ∧ ∃ hb : b ∈ S,
      Function.Bijective (Localization.awayMap S.val.toRingHom ⟨b, hb⟩) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := Localization.Away b)
  have hfrac (z : Localization.Away b) : ∃ (a : C) (n : ℕ),
      IsLocalization.mk' (M := Submonoid.powers b) (Localization.Away b)
        a ⟨b ^ n, n, rfl⟩ = z := by
    obtain ⟨a, ⟨_, n, rfl⟩, ha⟩ := IsLocalization.exists_mk'_eq (.powers b) z
    exact ⟨a, n, ha⟩
  choose a n ha using hfrac
  let S : Subalgebra R C :=
    Algebra.adjoin R (insert b (T ∪ a '' (s : Set (Localization.Away b))))
  have hfinite : Module.Finite R S :=
    Algebra.finite_adjoin_of_finite_of_isIntegral
      ((hT.union (s.finite_toSet.image a)).insert b)
      (fun x _ ↦ Algebra.IsIntegral.isIntegral x)
  have hTS : T ⊆ S := fun x hx ↦
    Algebra.subset_adjoin (Set.mem_insert_of_mem b (Or.inl hx))
  have hbS : b ∈ S := Algebra.subset_adjoin (Set.mem_insert b _)
  have haS (z : Localization.Away b) (hz : z ∈ s) : a z ∈ S :=
    Algebra.subset_adjoin (Set.mem_insert_of_mem b (Or.inr ⟨z, hz, rfl⟩))
  let bS : S := ⟨b, hbS⟩
  let φ : Localization.Away bS →ₐ[R] Localization.Away b :=
    Localization.awayMapₐ S.val bS
  have hpowers : Submonoid.powers bS ≤
      (Submonoid.powers b).comap (S.val : S →+* C) := by
    rintro _ ⟨m, rfl⟩
    exact ⟨m, rfl⟩
  have hφ : φ.toRingHom =
      IsLocalization.map (M := Submonoid.powers bS)
        (S := Localization.Away bS) (P := C) (T := Submonoid.powers b)
        (Localization.Away b) S.val hpowers := by
    rfl
  have hsrange : (s : Set (Localization.Away b)) ⊆ φ.range := by
    intro z hz
    let den : Submonoid.powers bS := ⟨bS ^ n z, ⟨n z, rfl⟩⟩
    refine ⟨IsLocalization.mk' (M := Submonoid.powers bS)
      (Localization.Away bS) ⟨a z, haS z hz⟩
      den, ?_⟩
    rw [hφ, IsLocalization.map_mk']
    simpa [den] using ha z
  have htop : (⊤ : Subalgebra R (Localization.Away b)) ≤ φ.range := by
    rw [← hs]
    exact Algebra.adjoin_le_iff.mpr hsrange
  have hsurj : Function.Surjective φ := fun z ↦
    (φ.mem_range).mp (htop (show z ∈ (⊤ : Subalgebra R (Localization.Away b)) from trivial))
  refine ⟨S, hfinite, hTS, hbS, ?_⟩
  exact ⟨IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective, hsurj⟩

end Algebra
