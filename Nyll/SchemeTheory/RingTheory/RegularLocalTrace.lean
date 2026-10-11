/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.RegularLocalFiniteFreeResolution
import Nyll.SchemeTheory.RingTheory.FractionFieldSubalgebraTrace
import Nyll.SchemeTheory.RingTheory.RegularLocalDomain
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.LinearAlgebra.Trace

/-!
# Traces over regular local rings

A finite free resolution expresses the trace after flat field extension as an
alternating sum of traces of finite free modules. We use only the finite free
resolution theorem for a regular local ring from the imported source; the
stronger hypothesis of its unique factorization theorem is not used.
-/

open scoped TensorProduct nonZeroDivisors

universe u v w₁ w₂ w₃

namespace SchemeTheory

private theorem trace_add_of_exact
    {K : Type v} [Field K]
    {A : Type w₁} [AddCommGroup A] [Module K A] [Module.Finite K A]
    {F : Type w₂} [AddCommGroup F] [Module K F] [Module.Finite K F]
    {M : Type w₃} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (i : A →ₗ[K] F) (p : F →ₗ[K] M)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p)
    (a : Module.End K A) (b : Module.End K F) (c : Module.End K M)
    (hbi : b.comp i = i.comp a) (hpb : p.comp b = c.comp p) :
    LinearMap.trace K F b = LinearMap.trace K A a + LinearMap.trace K M c := by
  obtain ⟨s₀, hs₀⟩ := Module.projective_lifting_property p LinearMap.id hp
  obtain ⟨e, hie, hpe⟩ := hex.splitSurjectiveEquiv hi ⟨s₀, hs₀⟩
  let r : F →ₗ[K] A := (LinearMap.fst K A M).comp e.toLinearMap
  let s : M →ₗ[K] F := e.symm.toLinearMap.comp (LinearMap.inr K A M)
  have hri : r.comp i = LinearMap.id := by
    rw [hie]
    ext x
    change (e (e.symm (x, 0))).1 = x
    rw [e.apply_symm_apply]
  have hps : p.comp s = LinearMap.id := by
    rw [hpe]
    ext x
    change (e (e.symm (0, x))).2 = x
    rw [e.apply_symm_apply]
  have hsplit : i.comp r + s.comp p = LinearMap.id := by
    rw [hie, hpe]
    ext x
    change e.symm ((e x).1, 0) + e.symm (0, (e x).2) = x
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    exact e.symm_apply_apply x
  have hba : r.comp (b.comp i) = a := by
    rw [hbi, ← LinearMap.comp_assoc, hri, LinearMap.id_comp]
  have hbc : p.comp (b.comp s) = c := by
    rw [← LinearMap.comp_assoc, hpb, LinearMap.comp_assoc, hps, LinearMap.comp_id]
  calc
    LinearMap.trace K F b = LinearMap.trace K F
        ((b.comp i).comp r + (b.comp s).comp p) := by
      congr 1
      rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← LinearMap.comp_add,
        hsplit, LinearMap.comp_id]
    _ = LinearMap.trace K F ((b.comp i).comp r) +
        LinearMap.trace K F ((b.comp s).comp p) := map_add _ _ _
    _ = LinearMap.trace K A (r.comp (b.comp i)) +
        LinearMap.trace K M (p.comp (b.comp s)) := by
      rw [LinearMap.trace_comp_comm' r (b.comp i),
        LinearMap.trace_comp_comm' p (b.comp s)]
    _ = LinearMap.trace K A a + LinearMap.trace K M c := by rw [hba, hbc]

open RegularLocalResolution.P2mAB.StablyFree

private theorem trace_baseChange_mem_range_of_hasFFR
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : Type v) [Field K] [Algebra R K] [Module.Flat R K]
    (n : ℕ) : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      HasFFR R n M → ∀ φ : Module.End R M,
        ∃ r : R, algebraMap R K r = LinearMap.trace K (K ⊗[R] M) (φ.baseChange K) := by
  induction n with
  | zero =>
    intro M _ _ _ h φ
    have : Module.Free R M := h.2
    exact ⟨LinearMap.trace R M φ, (LinearMap.trace_baseChange φ K).symm⟩
  | succ n ih =>
    intro M _ _ _ h φ
    obtain ⟨k, p, hp, hn⟩ := h
    obtain ⟨b, hb⟩ := Module.projective_lifting_property p (φ.comp p) hp
    let a : Module.End R (LinearMap.ker p) :=
      LinearMap.codRestrict (LinearMap.ker p) (b.comp (LinearMap.ker p).subtype) (by
        intro x
        change p (b x) = 0
        rw [← LinearMap.comp_apply, hb]
        simp only [LinearMap.comp_apply, LinearMap.mem_ker.mp x.property, map_zero])
    have hbi : b.comp (LinearMap.ker p).subtype = (LinearMap.ker p).subtype.comp a := by
      ext x
      rfl
    obtain ⟨r, hr⟩ := ih (LinearMap.ker p) hn a
    have hiK : Function.Injective ((LinearMap.ker p).subtype.baseChange K) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _
        (Submodule.injective_subtype (LinearMap.ker p))
    have hpK : Function.Surjective (p.baseChange K) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact LinearMap.lTensor_surjective K hp
    have hexK : Function.Exact ((LinearMap.ker p).subtype.baseChange K) (p.baseChange K) := by
      simp only [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_exact K (LinearMap.exact_subtype_ker_map p)
    have hbiK : (b.baseChange K).comp ((LinearMap.ker p).subtype.baseChange K) =
        ((LinearMap.ker p).subtype.baseChange K).comp (a.baseChange K) := by
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hbi]
    have hpbK : (p.baseChange K).comp (b.baseChange K) =
        (φ.baseChange K).comp (p.baseChange K) := by
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hb]
    have ht := trace_add_of_exact ((LinearMap.ker p).subtype.baseChange K) (p.baseChange K)
      hiK hpK hexK (a.baseChange K) (b.baseChange K) (φ.baseChange K) hbiK hpbK
    refine ⟨LinearMap.trace R (Fin k → R) b - r, ?_⟩
    rw [map_sub, ← LinearMap.trace_baseChange b K, ht, ← hr, add_sub_cancel_left]

/-- The trace of an endomorphism of a finite module over a regular local ring,
after any flat field extension, is the image of a scalar of the original ring. -/
theorem trace_baseChange_mem_range_of_isRegularLocalRing
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (K : Type v) [Field K] [Algebra R K] [Module.Flat R K]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (φ : Module.End R M) :
    ∃ r : R, algebraMap R K r = LinearMap.trace K (K ⊗[R] M) (φ.baseChange K) := by
  exact trace_baseChange_mem_range_of_hasFFR K
    (IsLocalRing.maximalIdeal R).spanFinrank M
    (hasFFR (IsLocalRing.maximalIdeal R).spanFinrank
      (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm M) φ

/-- A regular local ring is integrally closed. An integral fraction generates a
finite module whose multiplication trace is that fraction itself. -/
theorem isIntegrallyClosed_of_isRegularLocalRing
    (R : Type u) [CommRing R] [IsRegularLocalRing R] : IsIntegrallyClosed R := by
  let : IsDomain R := IsRegularLocalRing.isDomain R
  let K := FractionRing R
  let : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  apply (isIntegrallyClosed_iff K).mpr
  intro z hz
  let B : Subalgebra R K := Algebra.adjoin R {z}
  let : Module.Finite R B := Algebra.finite_adjoin_simple_of_isIntegral hz
  let b : B := ⟨z, Algebra.subset_adjoin (Set.mem_singleton z)⟩
  obtain ⟨r, hr⟩ := trace_baseChange_mem_range_of_isRegularLocalRing R K B
    (Algebra.lmul R B b)
  exact ⟨r, hr.trans (trace_baseChange_lmul_subalgebra R K B b)⟩

end SchemeTheory
