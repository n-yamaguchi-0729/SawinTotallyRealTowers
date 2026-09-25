/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.MaximalEverywhereUnramifiedProP
import Mathlib.FieldTheory.Galois.Profinite

set_option autoImplicit false
/-!
# The Galois group of the maximal everywhere-unramified pro-p extension

The maximal compositum is Galois because each proof-indexed candidate layer is
either a finite Galois field or bottom, and arbitrary composita preserve
separability and normality. The resulting automorphism group carries only the
canonical Krull topology and profinite instances supplied by Mathlib; its
pro-`p` property is deferred to the finite-support argument.
-/

open scoped NumberField

noncomputable section

universe u

namespace ClassFieldTower.Martinet

/-- For a fixed intermediate field, the proof-indexed candidate layer in the
definition of `maximalEverywhereUnramifiedProP` is Galois. It is the field
itself when all candidate properties hold and bottom otherwise. -/
private theorem isGalois_candidateLayer
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)]
    (M : IntermediateField F (AlgebraicClosure F)) :
    IsGalois F
      ((⨆ (_ : FiniteDimensional F M)
          (_ : IsGalois F M)
          (_ : IsPGroup p (M ≃ₐ[F] M))
          (_ : NumberField M)
          (_ : IsEverywhereUnramified F M),
        M) : IntermediateField F (AlgebraicClosure F)) := by
  classical
  by_cases hFinite : FiniteDimensional F M
  · rw [iSup_pos hFinite]
    by_cases hGalois : IsGalois F M
    · rw [iSup_pos hGalois]
      by_cases hP : IsPGroup p (M ≃ₐ[F] M)
      · rw [iSup_pos hP]
        by_cases hNumberField : NumberField M
        · rw [iSup_pos hNumberField]
          let _ : NumberField M := hNumberField
          by_cases hUnramified : IsEverywhereUnramified F M
          · rw [iSup_pos hUnramified]
            exact hGalois
          · rw [iSup_neg hUnramified]
            infer_instance
        · rw [iSup_neg hNumberField]
          infer_instance
      · rw [iSup_neg hP]
        infer_instance
    · rw [iSup_neg hGalois]
      infer_instance
  · rw [iSup_neg hFinite]
    infer_instance

/-- The maximal everywhere-unramified pro-`p` compositum is a Galois
extension of the base field. -/
theorem maximalEverywhereUnramifiedProP_isGalois
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsGalois F (maximalEverywhereUnramifiedProP F p) := by
  rw [maximalEverywhereUnramifiedProP]
  let layer := fun M : IntermediateField F (AlgebraicClosure F) ↦
    ((⨆ (_ : FiniteDimensional F M)
        (_ : IsGalois F M)
        (_ : IsPGroup p (M ≃ₐ[F] M))
        (_ : NumberField M)
        (_ : IsEverywhereUnramified F M),
      M) : IntermediateField F (AlgebraicClosure F))
  change IsGalois F
    ((⨆ M, layer M) : IntermediateField F (AlgebraicClosure F))
  let hLayer : ∀ M, IsGalois F (layer M) := fun M ↦ by
    dsimp only [layer]
    exact isGalois_candidateLayer F p M
  let _ := hLayer
  exact
    { to_isSeparable :=
        IntermediateField.isSeparable_iSup F (AlgebraicClosure F)
      to_normal :=
        IntermediateField.normal_iSup F (AlgebraicClosure F) layer }

/-- The canonical Galois instance for the maximal compositum. -/
instance maximalEverywhereUnramifiedProP.instIsGalois
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsGalois F (maximalEverywhereUnramifiedProP F p) :=
  maximalEverywhereUnramifiedProP_isGalois F p

/-- The automorphism group of the maximal everywhere-unramified pro-`p`
compositum. Its pro-`p` property is established only after finite support. -/
def MaxEverywhereUnramifiedProPGaloisGroup
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)] : Type u :=
  maximalEverywhereUnramifiedProP F p ≃ₐ[F]
    maximalEverywhereUnramifiedProP F p

/-- The canonical group structure inherited from algebra automorphisms. -/
noncomputable instance MaxEverywhereUnramifiedProPGaloisGroup.instGroup
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)] :
    Group (MaxEverywhereUnramifiedProPGaloisGroup F p) :=
  inferInstanceAs
    (Group (maximalEverywhereUnramifiedProP F p ≃ₐ[F]
      maximalEverywhereUnramifiedProP F p))

/-- The canonical Krull topology inherited from algebra automorphisms. -/
noncomputable instance MaxEverywhereUnramifiedProPGaloisGroup.instTopologicalSpace
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)] :
    TopologicalSpace (MaxEverywhereUnramifiedProPGaloisGroup F p) :=
  inferInstanceAs
    (TopologicalSpace (maximalEverywhereUnramifiedProP F p ≃ₐ[F]
      maximalEverywhereUnramifiedProP F p))

/-- The canonical topological-group structure for the Krull topology. -/
instance MaxEverywhereUnramifiedProPGaloisGroup.instIsTopologicalGroup
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsTopologicalGroup (MaxEverywhereUnramifiedProPGaloisGroup F p) :=
  inferInstanceAs
    (IsTopologicalGroup (maximalEverywhereUnramifiedProP F p ≃ₐ[F]
      maximalEverywhereUnramifiedProP F p))

/-- Compactness inherited from the profinite Galois-group construction. -/
instance MaxEverywhereUnramifiedProPGaloisGroup.instCompactSpace
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)] :
    CompactSpace (MaxEverywhereUnramifiedProPGaloisGroup F p) :=
  inferInstanceAs
    (CompactSpace (maximalEverywhereUnramifiedProP F p ≃ₐ[F]
      maximalEverywhereUnramifiedProP F p))

/-- Hausdorffness inherited from the Krull topology. -/
instance MaxEverywhereUnramifiedProPGaloisGroup.instT2Space
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)] :
    T2Space (MaxEverywhereUnramifiedProPGaloisGroup F p) :=
  inferInstanceAs
    (T2Space (maximalEverywhereUnramifiedProP F p ≃ₐ[F]
      maximalEverywhereUnramifiedProP F p))

/-- Total disconnectedness inherited from the Krull topology. -/
instance MaxEverywhereUnramifiedProPGaloisGroup.instTotallyDisconnectedSpace
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)] :
    TotallyDisconnectedSpace
      (MaxEverywhereUnramifiedProPGaloisGroup F p) :=
  inferInstanceAs
    (TotallyDisconnectedSpace
      (maximalEverywhereUnramifiedProP F p ≃ₐ[F]
        maximalEverywhereUnramifiedProP F p))

end ClassFieldTower.Martinet
