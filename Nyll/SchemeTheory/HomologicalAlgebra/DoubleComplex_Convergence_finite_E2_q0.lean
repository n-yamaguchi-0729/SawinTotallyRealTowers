/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_DoubleComplex_Convergence_finite_E2_q0.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Nyll.SchemeTheory.Cohomology.Sheaves.DoubleComplex

/-!
Finiteness in the zero row of the second page of a convergent double complex.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.HomologicalAlgebra.Proofs
namespace DoubleComplex_Convergence_finite_E2_q0

universe u

noncomputable section

namespace DoubleComplex
open _root_.DoubleComplex
open _root_.DoubleComplex

section Extract

variable {R : Type u} [CommRing R]

theorem subquot_finite [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (s : SubQuot R M) : Module.Finite R s.carrier := by
  have : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  have : Module.Finite R ↥s.Z := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  exact Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.Quotient.mk_surjective _)

theorem filt_finite [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] {N : ℕ} (F : Fin (N + 1) → Submodule R M)
    (hF₀ : F 0 = ⊥) (hFmono : Monotone F)
    (hFgr : ∀ i : Fin N,
      Module.Finite R (↥(F i.succ) ⧸ (F i.castSucc).comap (F i.succ).subtype)) :
    ∀ i, Module.Finite R ↥(F i) := by
  intro i
  induction i using Fin.induction with
  | zero => rw [hF₀]; exact Module.Finite.iff_fg.mpr Submodule.fg_bot
  | succ j ih =>
    have := ih
    have hS : Module.Finite R ↥((F j.castSucc).comap (F j.succ).subtype) :=
      Module.Finite.equiv
        (Submodule.comapSubtypeEquivOfLe (hFmono (Fin.castSucc_le_succ j))).symm
    have hQ : Module.Finite R (↥(F j.succ) ⧸ (F j.castSucc).comap (F j.succ).subtype) := hFgr j
    exact Module.Finite.of_submodule_quotient ((F j.castSucc).comap (F j.succ).subtype)

namespace Convergence
open _root_.DoubleComplex.Convergence
end Convergence
open scoped _root_.DoubleComplex.Convergence in
theorem Convergence.finite_E2_q0 [IsNoetherianRing R]
    {E₂ : ℕ → ℕ → Type u} [∀ p q, AddCommGroup (E₂ p q)] [∀ p q, Module R (E₂ p q)]
    {H : ℕ → Type u} [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)] {N : ℕ}
    (conv : Convergence R E₂ H N)
    (hH : ∀ n, Module.Finite R (H n)) (hE₂ : ∀ p q, 1 ≤ q → Module.Finite R (E₂ p q))
    (p : ℕ) (hp : p ≤ N) : Module.Finite R (E₂ p 0) := by
  have hBfilt : ∀ i, Module.Finite R ↥(conv.Bfilt p i) := by
    refine filt_finite (conv.Bfilt p) (conv.Bfilt_bot p)
      (conv.Bfilt_mono p) (fun i => ?_)
    obtain ⟨p', q', hq', s, ⟨e⟩⟩ := conv.Bfilt_gr p i
    have := hE₂ p' q' hq'
    have := subquot_finite s
    exact Module.Finite.equiv e.symm
  have hEinf : Module.Finite R (conv.Einf p 0).carrier := by
    let pF : Fin (N + 1) := ⟨p, Nat.lt_succ_of_le hp⟩
    obtain ⟨e⟩ := conv.Hfilt_gr pF
    have := hH p
    have : IsNoetherian R (H p) := isNoetherian_of_isNoetherianRing_of_finite R (H p)
    have : Module.Finite R ↥(conv.Hfilt p pF.succ) :=
      Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    have hgrH : Module.Finite R
        (↥(conv.Hfilt p pF.succ) ⧸
          (conv.Hfilt p pF.castSucc).comap (conv.Hfilt p pF.succ).subtype) :=
      Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.Quotient.mk_surjective _)
    exact Module.Finite.equiv e
  have hB : Module.Finite R ↥(conv.Einf p 0).B := conv.Bfilt_top p ▸ hBfilt (Fin.last N)
  have hBc : Module.Finite R ↥((conv.Einf p 0).B.comap (conv.Einf p 0).Z.subtype) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe (conv.Einf p 0).hBZ).symm
  have hZ : Module.Finite R ↥(conv.Einf p 0).Z :=
    Module.Finite.of_submodule_quotient ((conv.Einf p 0).B.comap (conv.Einf p 0).Z.subtype)
  have : Module.Finite R ↥(⊤ : Submodule R (E₂ p 0)) := conv.hZ0 p ▸ hZ
  exact Module.Finite.equiv Submodule.topEquiv

end Extract

end DoubleComplex

theorem _root_.DoubleComplex.Convergence.finite_E2_q0 {R : Type u} [CommRing R] [IsNoetherianRing R]
    {E₂ : ℕ → ℕ → Type u} [∀ p q, AddCommGroup (E₂ p q)] [∀ p q, Module R (E₂ p q)]
    {H : ℕ → Type u} [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)] {N : ℕ}
    (conv : DoubleComplex.Convergence R E₂ H N)
    (hH : ∀ n, Module.Finite R (H n)) (hE₂ : ∀ p q, 1 ≤ q → Module.Finite R (E₂ p q))
    (p : ℕ) (hp : p ≤ N) : Module.Finite R (E₂ p 0) :=
  DoubleComplex_Convergence_finite_E2_q0.DoubleComplex.Convergence.finite_E2_q0 conv hH hE₂ p hp

end
end AlgebraicCurves.Foundations.HomologicalAlgebra.Proofs.DoubleComplex_Convergence_finite_E2_q0
end ProofImplementation
