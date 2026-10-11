/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FreeProC.Basic
import Nyll.ProCGroups.FiniteStepSolvableQuotients.Commutators.DerivedSeriesAndQuotients

/-!
# Pro C Groups / Free pro-C / Solvable Quotients

This module transports free pro-\(C\) data to finite-step solvable quotients
and their derived-series constructions.
-/

open scoped Topology

namespace ProCGroups.FreeProC

open ProCGroups.FiniteStepSolvableQuotients

universe u v w

variable {C : ProCGroups.FiniteGroupClass.{u}}
variable [Fact (ProCGroups.FiniteGroupClass.Variety C)]
variable [Fact (ProCGroups.FiniteGroupClass.IsomClosed C)]
variable {F : Type u} [TopologicalSpace F] [Group F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]

/-- The endomorphism induced by collapseToFinset on a maximal solvable quotient. -/
noncomputable def collapseToFinsetQuot
    {ι : Type v} [DecidableEq ι] (X : ι → F)
    (hFree : IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) ι F X)
    (S : Finset ι) (m : ℕ) :
    MaxSolvQuot F m →ₜ* MaxSolvQuot F m :=
  ProCGroups.FiniteStepSolvableQuotients.topMaxSolvQuotMap (hFree.collapseToFinset S) m

omit [Fact (ProCGroups.FiniteGroupClass.IsomClosed C)] in
/--
On the quotient, composing with \(\mathrm{collapseToFinsetQuot}\) leaves a map that is trivial
outside \(S\) unchanged.
-/
theorem comp_collapseToFinsetQuot_eq_of_eq_one_outside
    {ι : Type v} [DecidableEq ι] (X : ι → F)
    (hFree : IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) ι F X)
    {H : Type w} [TopologicalSpace H] [Group H] [T2Space H]
    (S : Finset ι) (m : ℕ) (φ : MaxSolvQuot F m →ₜ* H)
    (hφ : ∀ j, j ∉ S → φ (continuousToMaxSolvQuot F m (X j)) = 1) :
    φ.comp (collapseToFinsetQuot X hFree S m) = φ := by
  let ψ : F →ₜ* H := φ.comp (continuousToMaxSolvQuot F m)
  have hψ :
      ψ.comp (hFree.collapseToFinset S) = ψ := by
    exact
      hFree.comp_collapseToFinset_eq_of_eq_one_outside ψ S (by
        intro j hj
        exact hφ j hj)
  ext q
  obtain ⟨x, rfl⟩ := continuousToMaxSolvQuot_surjective (G := F) m q
  change ψ (hFree.collapseToFinset S x) = ψ x
  exact congrArg (fun f : F →ₜ* H => f x) hψ

/--
The map from the original maximal solvable quotient to the maximal solvable quotient of the
finite-support retract.
-/
noncomputable def finsetSupportRangeQuot
    {ι : Type v} [DecidableEq ι] (X : ι → F)
    (hFree : IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) ι F X)
    (S : Finset ι) (m : ℕ) :
    MaxSolvQuot F m →ₜ* MaxSolvQuot (hFree.FinsetSupportRetract S) m :=
  ProCGroups.FiniteStepSolvableQuotients.topMaxSolvQuotMap (hFree.collapseToFinsetRange S) m

/--
The map from the maximal solvable quotient of the finite-support retract to the original maximal
solvable quotient.
-/
noncomputable def finsetSupportInclusionQuot
    {ι : Type v} [DecidableEq ι] (X : ι → F)
    (hFree : IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) ι F X)
    (S : Finset ι) (m : ℕ) :
    MaxSolvQuot (hFree.FinsetSupportRetract S) m →ₜ* MaxSolvQuot F m :=
  ProCGroups.FiniteStepSolvableQuotients.topMaxSolvQuotMap (hFree.collapseToFinsetInclusion S) m

omit [Fact (ProCGroups.FiniteGroupClass.IsomClosed C)] in
/--
The quotient map induced by the finite-support retraction sends the class of `x` to the class of
its collapsed finite-support image.
-/
theorem finsetSupportRangeQuot_apply
    {ι : Type v} [DecidableEq ι] (X : ι → F)
    (hFree : IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) ι F X)
    (S : Finset ι) (m : ℕ) (x : F) :
    finsetSupportRangeQuot X hFree S m (continuousToMaxSolvQuot F m x) =
      continuousToMaxSolvQuot (hFree.FinsetSupportRetract S) m
        (hFree.collapseToFinsetRange S x) := by
  change
    QuotientGroup.map
        (N := topDerivedTop F m)
        (M := topDerivedTop (hFree.FinsetSupportRetract S) m)
        (f := (hFree.collapseToFinsetRange S : F →* hFree.FinsetSupportRetract S))
        (ProCGroups.FiniteStepSolvableQuotients.topDerivedTop_le_comap
          (G := F) (Q := hFree.FinsetSupportRetract S) (f := hFree.collapseToFinsetRange S) m)
        ((QuotientGroup.mk' (topDerivedTop F m)) x) =
      (QuotientGroup.mk' (topDerivedTop (hFree.FinsetSupportRetract S) m))
        (hFree.collapseToFinsetRange S x)
  rw [QuotientGroup.map_mk']
  rfl

omit [Fact (ProCGroups.FiniteGroupClass.IsomClosed C)] in
/--
The quotient map induced by inclusion of the finite-support retract sends the class of `x` to
the class of its image in the original free pro-\(C\) group.
-/
theorem finsetSupportInclusionQuot_apply
    {ι : Type v} [DecidableEq ι] (X : ι → F)
    (hFree : IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) ι F X)
    (S : Finset ι) (m : ℕ) (x : hFree.FinsetSupportRetract S) :
    finsetSupportInclusionQuot X hFree S m
        (continuousToMaxSolvQuot (hFree.FinsetSupportRetract S) m x) =
      continuousToMaxSolvQuot F m (hFree.collapseToFinsetInclusion S x) := by
  change
    QuotientGroup.map
        (N := topDerivedTop (hFree.FinsetSupportRetract S) m)
        (M := topDerivedTop F m)
        (f := (hFree.collapseToFinsetInclusion S : hFree.FinsetSupportRetract S →* F))
        (ProCGroups.FiniteStepSolvableQuotients.topDerivedTop_le_comap
          (G := hFree.FinsetSupportRetract S) (Q := F)
          (f := hFree.collapseToFinsetInclusion S) m)
        ((QuotientGroup.mk' (topDerivedTop (hFree.FinsetSupportRetract S) m)) x) =
      (QuotientGroup.mk' (topDerivedTop F m)) (hFree.collapseToFinsetInclusion S x)
  rw [QuotientGroup.map_mk']
  rfl

end ProCGroups.FreeProC
