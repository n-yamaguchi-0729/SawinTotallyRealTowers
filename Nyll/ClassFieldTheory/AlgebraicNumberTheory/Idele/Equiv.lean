/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.Equiv
public import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Field-equivalence transport on the standard idele carriers

The idele equivalence is the units functor applied to adelic transport. Its
principal-idele formula descends that same map to the standard class quotient.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace NumberField

universe u v

variable {K : Type u} {M : Type v}
  [Field K] [NumberField K] [Algebra ℚ K]
  [Field M] [NumberField M] [Algebra ℚ M]

namespace IdeleGroup

/-- The standard idele transport induced by the adelic ring equivalence. -/
def congr (e : K ≃ₐ[ℚ] M) : IdeleGroup (𝓞 K) K ≃* IdeleGroup (𝓞 M) M :=
  Units.mapEquiv (adeleCongr e).toMulEquiv

/-- Adelic evaluation of the standard idele equivalence. -/
theorem coe_congr (e : K ≃ₐ[ℚ] M) (a : IdeleGroup (𝓞 K) K) :
    (congr e a : AdeleRing (𝓞 M) M) = adeleCongr e (a : AdeleRing (𝓞 K) K) := rfl

/-- Identity field transport is the identity on standard ideles. -/
theorem congr_refl (a : IdeleGroup (𝓞 K) K) :
    congr (AlgEquiv.refl : K ≃ₐ[ℚ] K) a = a := by
  apply Units.ext
  exact adeleCongr_refl (a : AdeleRing (𝓞 K) K)

/-- Field-equivalence transport is functorial on standard ideles. -/
theorem congr_trans {N : Type*} [Field N] [NumberField N] [Algebra ℚ N]
    (e : K ≃ₐ[ℚ] M) (f : M ≃ₐ[ℚ] N) (a : IdeleGroup (𝓞 K) K) :
    congr f (congr e a) = congr (e.trans f) a := by
  apply Units.ext
  exact adeleCongr_trans e f (a : AdeleRing (𝓞 K) K)

/-- Transport preserves diagonal units through the given field equivalence. -/
theorem congr_unitEmbedding (e : K ≃ₐ[ℚ] M) (x : Kˣ) :
    congr e (unitEmbedding (𝓞 K) K x) =
      unitEmbedding (𝓞 M) M (Units.mapEquiv e.toMulEquiv x) := by
  apply Units.ext
  exact adeleCongr_algebraMap e (x : K)

/-- The standard principal subgroups correspond under idele transport. -/
theorem principalSubgroup_map_congr (e : K ≃ₐ[ℚ] M) :
    (principalSubgroup (𝓞 K) K).map (congr e) = principalSubgroup (𝓞 M) M := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx⟩, rfl⟩
    rw [← hx]
    exact ⟨Units.mapEquiv e.toMulEquiv x, (congr_unitEmbedding e x).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := (Units.mapEquiv e.toMulEquiv).surjective y
    exact ⟨unitEmbedding (𝓞 K) K x, ⟨x, rfl⟩, congr_unitEmbedding e x⟩

end IdeleGroup

namespace IdeleClassGroup

/-- The induced equivalence of the standard principal quotients. -/
def congr (e : K ≃ₐ[ℚ] M) :
    IdeleClassGroup (𝓞 K) K ≃* IdeleClassGroup (𝓞 M) M :=
  QuotientGroup.congr
    (IdeleGroup.principalSubgroup (𝓞 K) K)
    (IdeleGroup.principalSubgroup (𝓞 M) M)
    (IdeleGroup.congr e) (IdeleGroup.principalSubgroup_map_congr e)

/-- Quotient representatives are transported by the standard idele equivalence. -/
theorem congr_mk (e : K ≃ₐ[ℚ] M) (a : IdeleGroup (𝓞 K) K) :
    congr e (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K) a) =
      QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 M) M)
        (IdeleGroup.congr e a) := rfl

/-- Identity field transport is the identity on standard idele classes. -/
theorem congr_refl (c : IdeleClassGroup (𝓞 K) K) :
    congr (AlgEquiv.refl : K ≃ₐ[ℚ] K) c = c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
  change congr (AlgEquiv.refl : K ≃ₐ[ℚ] K) (q a) = q a
  exact (congr_mk (AlgEquiv.refl : K ≃ₐ[ℚ] K) a).trans (congrArg q (IdeleGroup.congr_refl a))

/-- Field-equivalence transport is functorial on standard principal quotients. -/
theorem congr_trans {N : Type*} [Field N] [NumberField N] [Algebra ℚ N]
    (e : K ≃ₐ[ℚ] M) (f : M ≃ₐ[ℚ] N) (c : IdeleClassGroup (𝓞 K) K) :
    congr f (congr e c) = congr (e.trans f) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  let qK := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
  let qM := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 M) M)
  let qN := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 N) N)
  change congr f (congr e (qK a)) = congr (e.trans f) (qK a)
  calc
    _ = congr f (qM (IdeleGroup.congr e a)) := congrArg (congr f) (congr_mk e a)
    _ = qN (IdeleGroup.congr f (IdeleGroup.congr e a)) := congr_mk f _
    _ = qN (IdeleGroup.congr (e.trans f) a) := congrArg qN (IdeleGroup.congr_trans e f a)
    _ = _ := (congr_mk (e.trans f) a).symm

/-- A homomorphism into field automorphisms acts on the same standard class quotient. -/
@[reducible] def actionOfFieldHom {G : Type*} [Monoid G]
    (ρ : G →* (K ≃ₐ[ℚ] K)) : MulDistribMulAction G (IdeleClassGroup (𝓞 K) K) where
  smul σ c := congr (ρ σ) c
  one_smul c := by
    change congr (ρ 1) c = c
    rw [map_one]
    exact congr_refl c
  mul_smul σ τ c := by
    change congr (ρ (σ * τ)) c = congr (ρ σ) (congr (ρ τ) c)
    rw [map_mul]
    exact (congr_trans (ρ τ) (ρ σ) c).symm
  smul_one σ := map_one (congr (ρ σ))
  smul_mul σ c d := map_mul (congr (ρ σ)) c d

end IdeleClassGroup

end NumberField
