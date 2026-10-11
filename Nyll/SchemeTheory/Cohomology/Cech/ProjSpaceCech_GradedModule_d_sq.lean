/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ProjSpaceCech_GradedModule_d_sq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule

/-!
The square of the graded-module Cech differential is zero.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_GradedModule_d_sq

universe u

noncomputable section

open Finset Function MvPolynomial

namespace ProjSpaceCech
open _root_.ProjSpaceCech
open _root_.ProjSpaceCech

section GradAltdSq

variable {R : Type u} [CommRing R] {n : ℕ}
variable (D : GradedModule R n)

namespace GradedModule
open _root_.ProjSpaceCech.GradedModule
end GradedModule
open scoped _root_.ProjSpaceCech.GradedModule in
theorem GradedModule.d_sq' (i : ℕ) :
    GradedModule.d D (i + 1) ∘ₗ GradedModule.d D i = 0 := by
  refine LinearMap.ext fun f => funext fun s => ?_
  rw [LinearMap.comp_apply, GradedModule.d_apply, LinearMap.zero_apply, Pi.zero_apply]
  simp only [GradedModule.d_apply, map_sum, map_smul, Finset.smul_sum, smul_smul,
    ← pow_add]
  simp only [GradedModule.faceRes]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  set S : Finset (Fin (i + 3) × Fin (i + 2)) := {ab | (ab.1 : ℕ) ≤ (ab.2 : ℕ)}
  rw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_bij
    (fun ab (hab : ab ∈ S) =>
      (ab.2.succ, Fin.castLT ab.1
        (Nat.lt_of_le_of_lt (Finset.mem_filter.mp hab).2 ab.2.isLt)))
    ?hmem ?hinj ?hsurj ?hterm
  case hmem =>
    rintro ⟨a, b⟩ hab
    simp only [S, Finset.compl_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_succ, not_le, Fin.val_castLT]
    exact Nat.lt_succ_of_le (Finset.mem_filter.mp hab).2
  case hinj =>
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    exact Prod.ext (Fin.eq_of_val_eq (by simpa using congrArg Fin.val h2))
      (Fin.succ_injective _ h1)
  case hsurj =>
    rintro ⟨a', b'⟩ hab'
    have hlt : (b' : ℕ) < (a' : ℕ) := by
      simpa [S, Finset.compl_filter, Finset.mem_filter, not_le] using hab'
    have ha'0 : a' ≠ 0 := fun h => by simp [h] at hlt
    refine ⟨(Fin.castSucc b', a'.pred ha'0), ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc,
        Fin.val_pred]; omega
    · exact Prod.ext (Fin.succ_pred a' ha'0)
        (Fin.eq_of_val_eq (by simp only [Fin.val_castLT, Fin.val_castSucc]))
  case hterm =>
    rintro ⟨a, b⟩ hab
    have hba : (a : ℕ) ≤ (b : ℕ) := (Finset.mem_filter.mp hab).2
    set a' : Fin (i + 2) := Fin.castLT a (Nat.lt_of_le_of_lt hba b.isLt)
    have halt : a' ≤ b := Fin.le_def.mpr (by simpa [a'] using hba)
    have hacs : a'.castSucc = a := Fin.eq_of_val_eq (by simp [a'])
    have hface :
        Idx.face n (Idx.face n s a) b
          = Idx.face n (Idx.face n s b.succ) a' := by
      apply Subtype.ext
      change s.1 ∘ (Fin.succAbove a ∘ Fin.succAbove b)
        = s.1 ∘ (Fin.succAbove b.succ ∘ Fin.succAbove a')
      rw [← hacs, Idx.succAbove_comp_succAbove halt]
    have hsign : ((-1 : R) ^ ((a : ℕ) + (b : ℕ)))
        = -((-1 : R) ^ (((b.succ : Fin (i + 3)) : ℕ) + (a' : ℕ))) := by
      simp only [Fin.val_succ, a', Fin.val_castLT]
      rw [show ((b : ℕ) + 1 + (a : ℕ)) = ((a : ℕ) + (b : ℕ)) + 1 from by ring, pow_succ]
      ring
    simp only [Fin.val_succ, a', Fin.val_castLT] at hsign ⊢
    rw [hsign, neg_smul]
    refine congrArg Neg.neg (congrArg₂ (· • ·) rfl ?_)
    have key : ∀ {t t' : Idx n i} (heq : t = t')
        {K K'} (h1 : Idx.img n t ⊆ K) (h1' : K ⊆ Idx.img n s)
        (h2 : Idx.img n t' ⊆ K') (h2' : K' ⊆ Idx.img n s),
        (GradedModule.secIncl D h1') ((GradedModule.secIncl D h1) (f t))
          = (GradedModule.secIncl D h2') ((GradedModule.secIncl D h2) (f t')) := by
      rintro t _ rfl K K' h1 h1' h2 h2'
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
        GradedModule.secIncl_trans, GradedModule.secIncl_trans]
    exact key hface (Idx.img_face_subset n _ b)
      (Idx.img_face_subset n s a)
      (Idx.img_face_subset n _ a')
      (Idx.img_face_subset n s b.succ)

open scoped _root_.ProjSpaceCech.GradedModule in
theorem GradedModule.range_d_le_ker (i : ℕ) :
    LinearMap.range (GradedModule.d D i)
      ≤ LinearMap.ker (GradedModule.d D (i + 1)) := by
  rintro _ ⟨f, rfl⟩
  exact LinearMap.congr_fun (GradedModule.d_sq' D i) f

end GradAltdSq

end ProjSpaceCech

theorem _root_.ProjSpaceCech.GradedModule.d_sq {R : Type u} [CommRing R] {n : ℕ} (D :
    ProjSpaceCech.GradedModule R n) (i : ℕ) :
    ProjSpaceCech.GradedModule.d D (i + 1) ∘ₗ ProjSpaceCech.GradedModule.d D i = 0 :=
  ProjSpaceCech.GradedModule.d_sq' D i

end
end AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_GradedModule_d_sq
end ProofImplementation
