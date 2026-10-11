/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Cyclic quotient idempotents and principal localizations

A bijection on principal localizations identifies ideals extended from the base
ring. Clearing the resulting denominator gives an ideal-membership statement in
the source. For a quotient idempotent, multiplication by one additional copy of
the idempotent removes this denominator, so cyclicity of its factor descends.
-/


@[expose] public section

universe u v w

namespace Algebra

/-- A bijective map of principal localizations reflects membership in an ideal
extended from the base, after multiplication by a power of the element inverted. -/
theorem exists_pow_mul_mem_map_of_awayMap_bijective
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (I : Ideal R) (b : A)
    (hf : Function.Bijective (Localization.awayMap f.toRingHom b))
    {x : A} (hx : f x ∈ I.map (algebraMap R B)) :
    ∃ n : ℕ, b ^ n * x ∈ I.map (algebraMap R A) := by
  let φ : Localization.Away b →ₐ[R] Localization.Away (f b) :=
    Localization.awayMapₐ f b
  have hφ : Function.Bijective φ := hf
  have hmap : (I.map (algebraMap R (Localization.Away b))).map φ.toRingHom =
      I.map (algebraMap R (Localization.Away (f b))) := by
    rw [Ideal.map_map]
    congr 1
    ext r
    exact φ.commutes r
  have hcomap : (I.map (algebraMap R (Localization.Away (f b)))).comap φ.toRingHom =
      I.map (algebraMap R (Localization.Away b)) := by
    rw [← hmap]
    exact Ideal.comap_map_of_bijective φ.toRingHom hφ
  have hlocB : algebraMap B (Localization.Away (f b)) (f x) ∈
      I.map (algebraMap R (Localization.Away (f b))) := by
    have hm := Ideal.mem_map_of_mem (algebraMap B (Localization.Away (f b))) hx
    rwa [Ideal.map_map,
      ← IsScalarTower.algebraMap_eq R B (Localization.Away (f b))] at hm
  have hφx : φ (algebraMap A (Localization.Away b) x) =
      algebraMap B (Localization.Away (f b)) (f x) := by
    simp only [φ, Localization.awayMapₐ, IsLocalization.Away.mapₐ_apply,
      IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  have hlocA : algebraMap A (Localization.Away b) x ∈
      I.map (algebraMap R (Localization.Away b)) := by
    rw [← hcomap]
    change φ (algebraMap A (Localization.Away b) x) ∈
      I.map (algebraMap R (Localization.Away (f b)))
    rw [hφx]
    exact hlocB
  have hext : (I.map (algebraMap R A)).map (algebraMap A (Localization.Away b)) =
      I.map (algebraMap R (Localization.Away b)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R A (Localization.Away b)]
  rw [← hext] at hlocA
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers b)
      (Localization.Away b) (I.map (algebraMap R A)) x).mp hlocA
  exact ⟨n, hn⟩

/-- Cyclicity of a quotient idempotent factor descends along an algebra map that
becomes bijective after localizing at that idempotent representative. -/
theorem cyclic_quotient_idempotent_of_awayMap_bijective
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (I : Ideal R) (b : A)
    (hb : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap R A)) b))
    (hf : Function.Bijective (Localization.awayMap f.toRingHom b))
    (hcyc : ∀ x : B ⧸ I.map (algebraMap R B), ∃ r : R,
      Ideal.Quotient.mk (I.map (algebraMap R B)) (f b) * x =
        r • Ideal.Quotient.mk (I.map (algebraMap R B)) (f b)) :
    ∀ x : A ⧸ I.map (algebraMap R A), ∃ r : R,
      Ideal.Quotient.mk (I.map (algebraMap R A)) b * x =
        r • Ideal.Quotient.mk (I.map (algebraMap R A)) b := by
  let qA : A →ₐ[R] A ⧸ I.map (algebraMap R A) :=
    Ideal.Quotient.mkₐ R (I.map (algebraMap R A))
  let qB : B →ₐ[R] B ⧸ I.map (algebraMap R B) :=
    Ideal.Quotient.mkₐ R (I.map (algebraMap R B))
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨r, hr⟩ := hcyc (qB (f x))
  have hmem : f (b * x - r • b) ∈ I.map (algebraMap R B) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change qB (f (b * x - r • b)) = 0
    rw [map_sub, map_mul, map_smul]
    exact sub_eq_zero.mpr hr
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_map_of_awayMap_bijective f I b hf hmem
  have hzero : qA (b ^ n * (b * x - r • b)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hn
  have hb' : IsIdempotentElem (qA b) := hb
  have hm := congrArg (fun z ↦ qA b * z) hzero
  rw [map_mul, map_pow, mul_zero, ← mul_assoc, ← pow_succ', hb'.pow_succ_eq n] at hm
  have hmul : qA b * qA (b * x - r • b) = qA (b * x - r • b) := by
    rw [map_sub, map_mul, map_smul, mul_sub, ← mul_assoc, hb'.eq, mul_smul_comm, hb'.eq]
  rw [hmul, map_sub, map_mul, map_smul, sub_eq_zero] at hm
  exact ⟨r, hm⟩

end Algebra
