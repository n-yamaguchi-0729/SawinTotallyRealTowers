/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsRegularRing_uniqueFactorizationMonoid_of_isLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.RingTheory.LocalAlgebra
import Nyll.SchemeTheory.RingTheory.RegularLocalDepthFreeness
import Nyll.SchemeTheory.RingTheory.RegularLocalDepth
import Nyll.SchemeTheory.RingTheory.FreeModuleRegularSequence
import Nyll.SchemeTheory.RingTheory.ModuleDepthBound
import Nyll.SchemeTheory.RingTheory.ModuleDepthRegularQuotient
import Nyll.SchemeTheory.RingTheory.CommonRegularElement

/-!
# Finite free resolutions over regular local rings

The depth argument and the resolution construction are extracted from the
attributed source above, independently of its subsequent localization and
unique factorization argument. The ring hypothesis here is only regular local.
-/

open IsLocalRing RingTheory.Sequence

universe u

namespace SchemeTheory.RegularLocalResolution

namespace P2mAB
namespace DepthLemma

variable {R : Type*} [CommRing R] [IsLocalRing R]

lemma length_le_depth {M : Type*} [AddCommGroup M] [Module R M] {rs : List R}
    (h1 : IsWeaklyRegular M rs) (h2 : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    (rs.length : ℕ∞) ≤ Module.depth R M :=
  le_sSup ⟨rs, h1, h2, rfl⟩

lemma exists_isSMulRegular_of_one_le_depth {M : Type*} [AddCommGroup M] [Module R M]
    (h : 1 ≤ Module.depth R M) : ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
  by_contra hcon
  push Not at hcon
  have : Module.depth R M ≤ 0 := by
    apply sSup_le
    rintro _ ⟨rs, h1, h2, rfl⟩
    cases rs with
    | nil => simp only [List.length_nil, CharP.cast_eq_zero, Std.le_refl]
    | cons r rs =>
      exact absurd ((isWeaklyRegular_cons_iff M r rs).mp h1).1
        (hcon r (h2 r (List.mem_cons_self (a := r) (l := rs))))
  exact (not_le_of_gt (zero_lt_one : (0 : ℕ∞) < 1)) (h.trans this)

lemma not_isAssociatedPrime_of_isSMulRegular [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    ¬ IsAssociatedPrime (maximalIdeal R) M := by
  intro h
  obtain ⟨m, hm⟩ := (isAssociatedPrime_iff.mp h).2
  have hxm : x • m = 0 := by
    have : x ∈ Submodule.colon ⊥ {m} := hm ▸ hx
    simpa only [Submodule.mem_colon_singleton, Submodule.mem_bot] using this
  have hm0 : m = 0 := hreg (by simpa only [smul_zero] using hxm)
  apply (maximalIdeal.isMaximal R).ne_top
  rw [hm, hm0]
  ext r
  simp only [Submodule.mem_colon_singleton, smul_zero, zero_mem, Submodule.mem_top]

theorem core [IsNoetherianRing R] (n : ℕ) :
    ∀ {K F M : Type*} [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F]
      [Module.Finite R F] [AddCommGroup M] [Module R M]
      (f : K →ₗ[R] F) (g : F →ₗ[R] M), Function.Injective f → Function.Exact f g →
      Function.Surjective g →
      (n : ℕ∞) ≤ Module.depth R F → (n : ℕ∞) ≤ Module.depth R M + 1 →
      (n : ℕ∞) ≤ Module.depth R K := by
  induction n with
  | zero => intros; exact zero_le
  | succ n ih =>
    intro K F M _ _ _ _ _ _ _ f g hf hfg hg hF hM
    have hF1 : 1 ≤ Module.depth R F :=
      le_trans (by simp only [Nat.cast_add, Nat.cast_one, self_le_add_left]) hF
    obtain ⟨x, hxm, hxF⟩ := exists_isSMulRegular_of_one_le_depth hF1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hxK : IsSMulRegular K x := hxF.of_injective f hf
      have h1 : IsWeaklyRegular K [x] := (isWeaklyRegular_singleton_iff K x).mpr hxK
      simpa only [zero_add, Nat.cast_one, ge_iff_le, List.length_cons, List.length_nil] using
        length_le_depth h1 (by
          intro r hr
          rw [List.mem_singleton] at hr
          exact hr ▸ hxm)
    · have : Module.Finite R M := Module.Finite.of_surjective g hg
      have hM1 : 1 ≤ Module.depth R M := by
        have h1 : ((n : ℕ) : ℕ∞) + 1 ≤ Module.depth R M + 1 := by
          simpa only [ne_eq, ENat.one_ne_top, not_false_eq_true,
            add_le_add_iff_left_of_ne_top, Nat.cast_succ] using hM
        have h2 : (n : ℕ∞) ≤ Module.depth R M := (ENat.add_le_add_iff_right ENat.one_ne_top).mp h1
        exact le_trans (by exact_mod_cast hn) h2
      obtain ⟨y, hym, hyM⟩ := exists_isSMulRegular_of_one_le_depth hM1
      obtain ⟨z, hzm, hzF, hzM⟩ :=
        Module.exists_mem_maximalIdeal_isSMulRegular_isSMulRegular F M
          (not_isAssociatedPrime_of_isSMulRegular hxm hxF)
          (not_isAssociatedPrime_of_isSMulRegular hym hyM)
      have hzK : IsSMulRegular K z := hzF.of_injective f hf
      let f' := QuotSMulTop.map z f
      let g' := QuotSMulTop.map z g
      have hf' : Function.Injective f' := by
        have h0 : Function.Exact (0 : K →ₗ[R] K) f := by
          intro k
          simp only [LinearMap.zero_apply, Set.mem_range, exists_const]
          constructor
          · intro hk
            exact (hf (by simpa only [map_zero] using hk) : k = 0) ▸ rfl
          · rintro rfl; exact map_zero f
        have := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last h0 hfg hzM
        rw [map_zero] at this
        rw [← LinearMap.ker_eq_bot, this.linearMap_ker_eq]
        exact LinearMap.range_zero
      have hfg' : Function.Exact f' g' := QuotSMulTop.map_exact z hfg hg
      have hg' : Function.Surjective g' := QuotSMulTop.map_surjective z hg
      have : Module.Finite R (QuotSMulTop z F) :=
        inferInstanceAs (Module.Finite R (F ⧸ _))
      have hKf : Module.Finite R K := Module.Finite.of_injective f hf
      have eF := Module.depth_quotSMulTop_succ_eq F hzm hzF
      have eM := Module.depth_quotSMulTop_succ_eq M hzm hzM
      have eK := Module.depth_quotSMulTop_succ_eq K hzm hzK
      have hF' : (n : ℕ∞) ≤ Module.depth R (QuotSMulTop z F) := by
        have : ((n : ℕ) : ℕ∞) + 1 ≤ Module.depth R (QuotSMulTop z F) + 1 := by
          rw [eF]; simpa only [Nat.cast_succ] using hF
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
      have hM' : (n : ℕ∞) ≤ Module.depth R (QuotSMulTop z M) + 1 := by
        rw [eM]
        have : ((n : ℕ) : ℕ∞) + 1 ≤ Module.depth R M + 1 := by
          simpa only [ne_eq, ENat.one_ne_top, not_false_eq_true,
            add_le_add_iff_left_of_ne_top, Nat.cast_succ] using hM
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
      have hK' := ih f' g' hf' hfg' hg' hF' hM'
      rw [← eK]
      simpa only [Nat.cast_succ, ne_eq, ENat.one_ne_top, not_false_eq_true,
        add_le_add_iff_left_of_ne_top, ge_iff_le, add_le_add_iff_right_of_ne_top] using
        add_le_add_right hK' 1

theorem min_depth_depth_add_one_le_depth_of_exact
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {K F M : Type*} [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F]
    [Module.Finite R F] [AddCommGroup M] [Module R M]
    (f : K →ₗ[R] F) (g : F →ₗ[R] M) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    min (Module.depth R F) (Module.depth R M + 1) ≤ Module.depth R K := by
  rcases eq_or_ne (Module.depth R K) ⊤ with hK | hK
  · simp only [hK, le_top]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hK
  by_contra hlt
  push Not at hlt
  rw [← hm] at hlt
  have h1 : ((m + 1 : ℕ) : ℕ∞) ≤ min (Module.depth R F) (Module.depth R M + 1) := by
    have := (ENat.add_one_le_iff (ENat.natCast_ne_top m)).mpr hlt
    simpa only [Nat.cast_succ, le_inf_iff, ne_eq, ENat.one_ne_top, not_false_eq_true,
      add_le_add_iff_left_of_ne_top] using this
  have := core (R := R) (m + 1) f g hf hfg hg (h1.trans (min_le_left _ _))
    (h1.trans (min_le_right _ _))
  rw [← hm] at this
  have h2 : (m + 1 : ℕ) ≤ m := by exact_mod_cast this
  omega

end P2mAB.DepthLemma

namespace P2mAB
namespace StablyFree

/-- The module admits a finite free resolution of length at most the specified bound. -/
def HasFFR (R : Type u) [CommRing R] : ℕ → (K : Type u) → [AddCommGroup K] → [Module R K] → Prop
  | 0, K, _, _ => Module.Finite R K ∧ Module.Free R K
  | n + 1, K, _, _ => ∃ (k : ℕ) (f : (Fin k → R) →ₗ[R] K),
      Function.Surjective f ∧ HasFFR R n (LinearMap.ker f)

variable {R : Type u} [CommRing R]

lemma hasFFR_zero_iff (K : Type u) [AddCommGroup K] [Module R K] :
    HasFFR R 0 K ↔ Module.Finite R K ∧ Module.Free R K := Iff.rfl

lemma hasFFR_succ_iff (n : ℕ) (K : Type u) [AddCommGroup K] [Module R K] :
    HasFFR R (n + 1) K ↔ ∃ (k : ℕ) (f : (Fin k → R) →ₗ[R] K),
      Function.Surjective f ∧ HasFFR R n (LinearMap.ker f) := Iff.rfl

section depth

variable [IsLocalRing R]

lemma length_le_depth {M : Type*} [AddCommGroup M] [Module R M] {rs : List R}
    (h1 : IsWeaklyRegular M rs) (h2 : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    (rs.length : ℕ∞) ≤ Module.depth R M :=
  le_sSup ⟨rs, h1, h2, rfl⟩

lemma exists_isWeaklyRegular_of_le_depth {M : Type*} [AddCommGroup M] [Module R M] (n : ℕ)
    (h : (n : ℕ∞) ≤ Module.depth R M) :
    ∃ rs : List R, IsWeaklyRegular M rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ n ≤ rs.length := by
  by_contra hcon
  push Not at hcon
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd (hcon [] (IsWeaklyRegular.nil R M) (by
      simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]))
      (by simp only [List.length_nil, lt_self_iff_false, not_false_eq_true])
  · have : Module.depth R M ≤ ((n - 1 : ℕ) : ℕ∞) := by
      apply sSup_le
      rintro _ ⟨rs, h1, h2, rfl⟩
      have := hcon rs h1 h2
      exact_mod_cast (by omega : rs.length ≤ n - 1)
    have h' : (n : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞) := h.trans this
    have : n ≤ n - 1 := by exact_mod_cast h'
    omega

lemma depth_eq_top_of_subsingleton (M : Type*) [AddCommGroup M] [Module R M] [Subsingleton M] :
    Module.depth R M = ⊤ := by
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  have h1 : IsWeaklyRegular M (List.replicate n (0 : R)) := by
    rw [isWeaklyRegular_iff]
    intro i _ a b _
    exact Subsingleton.elim a b
  have h2 : ∀ r ∈ List.replicate n (0 : R), r ∈ maximalIdeal R := by
    intro r hr
    rw [List.eq_of_mem_replicate hr]
    exact zero_mem _
  simpa only [ge_iff_le, List.length_replicate] using length_le_depth h1 h2

end depth

lemma le_depth_pi [IsRegularLocalRing R] (d : ℕ) (hd : ringKrullDim R = d) (k : ℕ) :
    (d : ℕ∞) ≤ Module.depth R (Fin k → R) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [depth_eq_top_of_subsingleton]; exact le_top
  · have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    have : Nontrivial (Fin k → R) := Function.nontrivial
    have hR : Module.depth R R = d := by
      have := IsRegularLocalRing.depth_self_eq_ringKrullDim R
      rw [hd] at this
      exact_mod_cast this
    obtain ⟨rs, h1, h2, h3⟩ := exists_isWeaklyRegular_of_le_depth (R := R) (M := R) d hR.ge
    have h1' : IsWeaklyRegular (Fin k → R) rs := (isWeaklyRegular_of_free).mpr h1
    exact le_trans (by exact_mod_cast h3) (length_le_depth h1' h2)

section syzygy

variable [IsRegularLocalRing R]

theorem hasFFR_of_le_depth (d : ℕ) (hd : ringKrullDim R = d) :
    ∀ n : ℕ, n ≤ d → ∀ (K : Type u) [AddCommGroup K] [Module R K] [Module.Finite R K],
      ((d - n : ℕ) : ℕ∞) ≤ Module.depth R K → HasFFR R n K := by
  intro n
  induction n with
  | zero =>
    intro _ K _ _ _ hK
    rw [hasFFR_zero_iff]
    refine ⟨inferInstance, ?_⟩
    rcases subsingleton_or_nontrivial K with hs | hs
    · exact Module.Free.of_subsingleton R K
    · apply Module.free_of_depth_eq_ringKrullDim_of_isRegularLocalRing R K
      have h1 : (.some (Module.depth R K) : WithBot ℕ∞) ≤ ringKrullDim R :=
        Module.depth_le_ringKrullDim
      rw [hd] at h1 ⊢
      have h1' : Module.depth R K ≤ d := by exact_mod_cast h1
      have h2 : (d : ℕ∞) ≤ Module.depth R K := by simpa only [tsub_zero] using hK
      have : Module.depth R K = d := le_antisymm h1' h2
      rw [this]; rfl
  | succ n ih =>
    intro hn K _ _ _ hK
    rw [hasFFR_succ_iff]
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R K
    refine ⟨k, f, hf, ih (by omega) _ ?_⟩
    have hDL := P2mAB.DepthLemma.min_depth_depth_add_one_le_depth_of_exact
      (LinearMap.ker f).subtype f
      (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map f) hf
    refine le_trans (le_min ?_ ?_) hDL
    · exact le_trans (show ((d - n : ℕ) : ℕ∞) ≤ (d : ℕ∞) by
        exact_mod_cast Nat.sub_le d n) (le_depth_pi d hd k)
    · have : ((d - n : ℕ) : ℕ∞) = ((d - (n + 1) : ℕ) : ℕ∞) + 1 := by
        norm_cast; omega
      rw [this]
      exact add_le_add hK le_rfl

theorem hasFFR (d : ℕ) (hd : ringKrullDim R = d) (K : Type u) [AddCommGroup K] [Module R K]
    [Module.Finite R K] : HasFFR R d K :=
  hasFFR_of_le_depth d hd d le_rfl K (by
    simp only [tsub_self, CharP.cast_eq_zero, zero_le])

end syzygy

end StablyFree
end P2mAB
end SchemeTheory.RegularLocalResolution
