/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafIdealFiltration
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_exists_idealPowSub_eq_bot
import Nyll.SchemeTheory.Cohomology.Cech.OModulePresheaf_cechFinite_of_affSES_mid
import Nyll.SchemeTheory.Cohomology.Cech.OModulePresheaf_cechFinite_of_affSES_right

/-!
Cech finiteness by devissage through powers of the vanishing ideal of a supporting closed subset.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs
namespace OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot

open _root_.AlgebraicGeometry
open _root_.CategoryTheory
open _root_.TopologicalSpace
open _root_.Opposite

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
namespace G4T
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

universe u

section Wrappers
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
  [IsSeparated π]
  {F₁ F₂ F₃ : OModulePresheaf π}
theorem cechFinite_of_affSES_mid' (K : V.OrderedAffineCover) (S : AffSES F₁ F₂ F₃) (h₁ :
    F₁.CechFinite K)
    (h₃ : F₃.CechFinite K) : F₂.CechFinite K := OModulePresheaf.cechFinite_of_affSES_mid S K h₁ h₃
theorem cechFinite_of_affSES_right' (K : V.OrderedAffineCover) (S : AffSES F₁ F₂ F₃) (h₁ :
    F₁.CechFinite K)
    (h₂ : F₂.CechFinite K) : F₃.CechFinite K := OModulePresheaf.cechFinite_of_affSES_right S K h₁ h₂
end Wrappers

section ZeroBase

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem cechFinite_zero (K : V.OrderedAffineCover) :
    OModulePresheaf.CechFinite (K := K) (OModulePresheaf.zero π) := by
  have hCF : ∀ q, Subsingleton
      (OModulePresheaf.cochain (OModulePresheaf.zero π) K q) :=
    fun q => ⟨fun a b => funext fun s => Subsingleton.elim _ _⟩
  exact ⟨(haveI := hCF 0; ⟨⟨∅, Subsingleton.elim _ _⟩⟩),
    fun i => (haveI := hCF (i + 1); ⟨⟨∅, Subsingleton.elim _ _⟩⟩)⟩

theorem cechFinite_idealPow_of_forall_subsingleton [IsSeparated π]
    (K : V.OrderedAffineCover) (I : V.IdealSheafData) (F : OModulePresheaf π) (N : ℕ)
    (hN : ∀ (q : ℕ) (s : K.Idx q),
      idealPowSub π I F N (K.inter s) = ⊥) :
    OModulePresheaf.CechFinite (K := K) (idealPow π I F N) := by
  have hCF : ∀ q, Subsingleton
      (OModulePresheaf.cochain (idealPow π I F N) K q) := fun q => by
    refine ⟨fun a b => funext fun s => Subtype.ext ?_⟩
    have hav := (Submodule.mem_bot R).mp (hN q s ▸ (a s).2 :
      (idealPowSub π I F N (K.inter s)).subtype (a s) ∈ ⊥)
    have hbv := (Submodule.mem_bot R).mp (hN q s ▸ (b s).2 :
      (idealPowSub π I F N (K.inter s)).subtype (b s) ∈ ⊥)
    exact hav.trans hbv.symm
  exact ⟨(haveI := hCF 0; ⟨⟨∅, Subsingleton.elim _ _⟩⟩),
    fun i => (haveI := hCF (i + 1); ⟨⟨∅, Subsingleton.elim _ _⟩⟩)⟩

theorem exists_cechFinite_idealPow [IsSeparated π] [IsLocallyNoetherian V]
    (K : V.OrderedAffineCover) (Y : Closeds V) (F : OModulePresheaf π)
    (hFc : OModulePresheaf.IsCoherent F) (hFq : OModulePresheaf.IsQuasicoherent F)
    (hFs : OModulePresheaf.SupportedIn F Y) :
    ∃ N, OModulePresheaf.CechFinite (K := K)
      (idealPow π (Scheme.IdealSheafData.vanishingIdeal Y) F N) := by
  let T : Type u := Σ q : Fin (Fintype.card K.ι), K.Idx q
  have : Fintype T := inferInstance
  choose Nqs hNqs using fun t : T => OModulePresheaf.exists_idealPowSub_eq_bot π Y F hFc hFq hFs
    ⟨K.inter t.2, K.isAffineOpen_inter π t.2⟩
  refine ⟨Finset.univ.sup Nqs,
    cechFinite_idealPow_of_forall_subsingleton π K _ F _ fun q s => ?_⟩
  rcases lt_or_ge q (Fintype.card K.ι) with hq | hq
  · exact le_bot_iff.mp
      ((hNqs ⟨⟨q, hq⟩, s⟩).symm ▸ idealPowSub_antitone π _ F
        (Finset.le_sup (Finset.mem_univ (⟨⟨q, hq⟩, s⟩ : T))) _)
  · have hcard := Fintype.card_le_of_injective s.1 s.2.injective
    rw [Fintype.card_fin] at hcard; omega

theorem cechFinite_of_forall_cechFinite_idealPowQuot [IsNoetherianRing R] [IsSeparated π]
    [IsLocallyNoetherian V] (K : V.OrderedAffineCover) (Y : Closeds V) (F : OModulePresheaf π)
    (hFc : OModulePresheaf.IsCoherent F) (hFq : OModulePresheaf.IsQuasicoherent F)
    (hFs : OModulePresheaf.SupportedIn F Y)
    (hStep : ∀ k, OModulePresheaf.CechFinite (K := K)
      (idealPowQuot π (Scheme.IdealSheafData.vanishingIdeal Y) F k)) :
    OModulePresheaf.CechFinite (K := K) F := by
  set I := Scheme.IdealSheafData.vanishingIdeal Y
  obtain ⟨N, hN⟩ := exists_cechFinite_idealPow π K Y F hFc hFq hFs
  have hSmul : ∀ j, OModulePresheaf.CechFinite (K := K)
      (idealPow π I F (N - j)) := fun j => by
    induction j with
    | zero => simpa using hN
    | succ j ih =>
      rcases Nat.lt_or_ge j N with hj | hj
      · have heq : N - j = (N - (j + 1)) + 1 := by omega
        exact cechFinite_of_affSES_mid' K
          (idealPowSES π I F (N - (j + 1))) (heq ▸ ih) (hStep _)
      · rw [Nat.sub_eq_zero_of_le (Nat.le_succ_of_le hj)]
        rw [Nat.sub_eq_zero_of_le hj] at ih; exact ih
  exact cechFinite_of_affSES_right' K
    (idealPowZeroSES π I F)
    (cechFinite_zero π K) (by simpa using hSmul N)

end ZeroBase

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicCurves.Cohomology.Cech.Proofs in
open _root_.AlgebraicGeometry
  OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot.AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_cechFinite_idealPowQuot {R :
    Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated
    π] [IsLocallyNoetherian V] (K : V.OrderedAffineCover) (Y : TopologicalSpace.Closeds V) (F :
    OModulePresheaf π) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hFs : F.SupportedIn Y)
    (hStep : ∀ k, (OModulePresheaf.idealPowQuot π (Scheme.IdealSheafData.vanishingIdeal Y) F
    k).CechFinite K) : F.CechFinite K :=
  AlgebraicGeometry.OModulePresheaf.G4T.cechFinite_of_forall_cechFinite_idealPowQuot π K Y F hFc
    hFq hFs hStep
end OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot
end AlgebraicCurves.Cohomology.Cech.Proofs
end ProofImplementation
