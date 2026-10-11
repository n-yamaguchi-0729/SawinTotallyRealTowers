/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.OpenSubgroup
import Nyll.ProCGroups.GroupTheory.CentralizerNormalizerCommensurator
import Nyll.ProCGroups.Order.Basic
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Separation
import Nyll.ProCGroups.Topologies.TopologicallyCharacteristicSubgroups

/-!
# Closed derived series and solvable quotients

This module defines the closed derived series of a topological group and its maximal finite-step
solvable quotients. It also records functoriality, closedness, and normality properties used to
compare these quotients under continuous homomorphisms.
-/

universe u v

namespace TopologicalGroup




/-- Closed-map properties descend to the restriction to a subgroup preimage. -/
lemma restrictPreimage_isClosedMap_of_isClosedMap
    {G : Type u} [TopologicalSpace G] [Group G]
    {Q : Type v} [TopologicalSpace Q] [Group Q]
    (π : G →ₜ* Q) (Q₁ : Subgroup Q)
    (hπ : IsClosedMap π)
    (hQ₁ : IsClosed (Q₁ : Set Q)) :
    IsClosedMap (ProCGroups.ContinuousMonoidHom.restrictPreimage π Q₁) := by
  let G₁ : Subgroup G := Q₁.comap (π : G →* Q)
  have hG₁ : IsClosed (G₁ : Set G) := hQ₁.preimage π.continuous
  intro s hs
  have hsG : IsClosed (((G₁ : Subgroup G).subtype : G₁ → G) '' s) :=
    hG₁.isClosedMap_subtype_val _ hs
  have himg :
      IsClosed ((fun x : G => π x) '' (((G₁ : Subgroup G).subtype : G₁ → G) '' s)) :=
    hπ _ hsG
  refine
    (hQ₁.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed).2 ?_
  change IsClosed ((fun y : Q₁ => (y : Q)) '' ((ProCGroups.ContinuousMonoidHom.restrictPreimage
      π Q₁) '' s))
  have hEq :
      (fun y : Q₁ => (y : Q)) '' ((ProCGroups.ContinuousMonoidHom.restrictPreimage π Q₁) '' s) =
        (fun x : G => π x) '' ((G₁.subtype : G₁ → G) '' s) := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨ProCGroups.ContinuousMonoidHom.restrictPreimage π Q₁ z, ⟨z, hz, rfl⟩, rfl⟩
  rw [hEq]
  exact himg

/--
If the image of a subgroup is contained in a closed subgroup, then the image of its closure is
contained there as well.
-/
lemma map_closure_le_of_map_le
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {Q : Type v} [TopologicalSpace Q] [Group Q]
    {G₁ : Subgroup G} {Q₁ : Subgroup Q} {f : G →ₜ* Q}
    (h₁ : G₁.map (f : G →* Q) ≤ Q₁)
    (hclosed : IsClosed (Q₁ : Set Q)) :
    (G₁.topologicalClosure).map (f : G →* Q) ≤ Q₁ := by
  have hMapsTo : Set.MapsTo (fun x : G => f x) (G₁ : Set G) (Q₁ : Set Q) := by
    intro x hx
    exact h₁ ⟨x, hx, rfl⟩
  have hMapsTo_cl :
      Set.MapsTo (fun x : G => f x) (_root_.closure (G₁ : Set G)) (Q₁ : Set Q) :=
    Set.MapsTo.closure_left hMapsTo f.continuous hclosed
  rintro y ⟨x, hx, rfl⟩
  exact hMapsTo_cl hx

/-- The image of a closure is contained in the closure of the image. -/
lemma map_closure_le_closure
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {Q : Type v} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    {G₁ : Subgroup G} {Q₁ : Subgroup Q} (f : G →ₜ* Q)
    (h₁ : G₁.map (f : G →* Q) ≤ Q₁) :
    (G₁.topologicalClosure).map (f : G →* Q) ≤ Q₁.topologicalClosure := by
  refine
    map_closure_le_of_map_le (f := f) (G₁ := G₁) (Q₁ := Q₁.topologicalClosure) ?_ ?_
  · exact le_trans h₁ (Subgroup.le_topologicalClosure (s := Q₁))
  · exact Subgroup.isClosed_topologicalClosure (s := Q₁)

/-- Closed maps send closed subgroups to closed images. -/
lemma isClosed_map_of_isClosedMap
    {G : Type u} [TopologicalSpace G] [Group G]
    {H : Type v} [TopologicalSpace H] [Group H]
    (f : G →ₜ* H) (hclosed : IsClosedMap f)
    (K : Subgroup G) (hK : IsClosed (K : Set G)) :
    IsClosed (((K.map (f : G →* H) : Subgroup H) : Set H)) := by
  have him : IsClosed ((fun x : G => f x) '' (K : Set G)) := hclosed _ hK
  have hEq :
      (fun x : G => f x) '' (K : Set G)
        = (((K.map (f : G →* H) : Subgroup H) : Set H)) := by
    exact image_subtype_eq_map (f := (f : G →* H)) (K := K)
  exact hEq ▸ him

/-- The kernel of the induced map is trivial under the stated comap equality hypothesis. -/
lemma ker_map_eq_bot_of_comap_eq
    {G : Type u} [Group G]
    {H : Type v} [Group H]
    {N : Subgroup G} {M : Subgroup H} [N.Normal] [M.Normal]
    (f : G →* H) (h : N ≤ M.comap f) (hcomap : M.comap f = N) :
    (QuotientGroup.map (N := N) (M := M) (f := f) h).ker = ⊥ := by
  calc
    (QuotientGroup.map (N := N) (M := M) (f := f) h).ker =
        Subgroup.map (QuotientGroup.mk' N) (Subgroup.comap f M) := by
          simpa using QuotientGroup.ker_map (N := N) (M := M) (f := f) h
    _ = Subgroup.map (QuotientGroup.mk' N) N := by simp only [hcomap, QuotientGroup.map_mk'_self]
    _ = ⊥ := by
      refine (Subgroup.map_eq_bot_iff (f := QuotientGroup.mk' N) (H := N)).2 ?_
      intro x hx
      simpa using hx

end TopologicalGroup

namespace MulEquiv

/-- Multiplicative equivalences transport torsion-freeness. -/
theorem isMulTorsionFree
    {M : Type u} [Monoid M]
    {N : Type v} [Monoid N]
    (e : M ≃* N) [IsMulTorsionFree M] :
    IsMulTorsionFree N := by
  exact Function.Injective.isMulTorsionFree (e.symm : N →* M) e.symm.injective

end MulEquiv

namespace ProCGroups.FiniteStepSolvableQuotients

/-- The closed commutator subgroup of a topological group. -/
abbrev closedCommutator
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (H K : Subgroup G) : Subgroup G :=
  (⁅H, K⁆).topologicalClosure

/-- The closed derived series starting from a subgroup. -/
def closedDerivedSeries
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (K : Subgroup G) : ℕ → Subgroup G
  | 0 => K
  | n + 1 => closedCommutator (closedDerivedSeries K n) (closedDerivedSeries K n)

/-- The `m`th closed derived subgroup of the whole topological group `G`. -/
abbrev topDerivedTop
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (m : ℕ) : Subgroup G :=
  closedDerivedSeries (G := G) (⊤ : Subgroup G) m

/-- Every term in the closed derived series of `G` is a closed subgroup. -/
instance topDerivedTop_isClosedInst
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {m : ℕ} :
    IsClosed (topDerivedTop G m : Set G) := by
  cases m with
  | zero =>
      change IsClosed ((⊤ : Subgroup G) : Set G)
      exact isClosed_univ
  | succ m =>
      simp only [topDerivedTop, closedDerivedSeries, closedCommutator]
      exact isClosed_closure

/-- Every term in the closed derived series of `G` is a normal subgroup. -/
instance topDerivedTop_normalInst
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {m : ℕ} :
    (topDerivedTop G m).Normal := by
  induction m with
  | zero =>
      change (⊤ : Subgroup G).Normal
      infer_instance
  | succ m ihm =>
      dsimp [topDerivedTop, closedDerivedSeries, closedCommutator]
      exact Subgroup.is_normal_topologicalClosure ⁅topDerivedTop G m, topDerivedTop G m⁆

/-- The quotient by the mth closed derived subgroup. -/
abbrev MaxSolvQuot
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (m : ℕ) : Type u :=
  G ⧸ topDerivedTop G m

/-- The natural quotient map to the maximal \(m\)-step solvable quotient. -/
abbrev toMaxSolvQuot
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (m : ℕ) :
    G →* MaxSolvQuot G m :=
  QuotientGroup.mk' (topDerivedTop G m)

/-- The natural quotient map as a continuous homomorphism. -/
abbrev continuousToMaxSolvQuot
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (m : ℕ) :
    G →ₜ* MaxSolvQuot G m :=
  { toMonoidHom := toMaxSolvQuot G m
    continuous_toFun := continuous_quotient_mk' }

/-- The preimage open subgroup induced by a continuous homomorphism. -/
abbrev preimageOpenSubgroup
    {G : Type u} [TopologicalSpace G] [Group G]
    {Q : Type v} [TopologicalSpace Q] [Group Q]
    (f : G →ₜ* Q) (H : OpenSubgroup Q) : OpenSubgroup G :=
  OpenSubgroup.comap (f := (f : G →* Q)) f.continuous H

scoped[ProCGroupsSolvableQuotients] notation "⁅" H "," K "⁆ₜ" =>
  ProCGroups.FiniteStepSolvableQuotients.closedCommutator H K
scoped[ProCGroupsSolvableQuotients] notation G "⟦" m "⟧ₜ" =>
  ProCGroups.FiniteStepSolvableQuotients.topDerivedTop G m
scoped[ProCGroupsSolvableQuotients] notation G "^ₘ" m =>
  ProCGroups.FiniteStepSolvableQuotients.MaxSolvQuot G m

open scoped ProCGroupsSolvableQuotients

/-- The zeroth closed derived subgroup is the whole topological group. -/
@[simp] lemma closedDerivedSeries_zero
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (K : Subgroup G) :
    closedDerivedSeries (G := G) K 0 = K := rfl

/--
The successor closed derived subgroup is the closed commutator subgroup of the previous derived
stage.
-/
@[simp] lemma closedDerivedSeries_succ
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (K : Subgroup G) (n : ℕ) :
    closedDerivedSeries (G := G) K (n + 1) =
      ⁅closedDerivedSeries (G := G) K n, closedDerivedSeries (G := G) K n⁆ₜ := rfl

/-- The zeroth term of the ambient closed derived series is the whole ambient group. -/
@[simp] lemma topDerivedTop_zero
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    G⟦0⟧ₜ = (⊤ : Subgroup G) := rfl

/--
The successor term of the ambient closed derived series is the closed commutator subgroup of the
previous term.
-/
@[simp] lemma topDerivedTop_succ
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (n : ℕ) :
    G⟦n + 1⟧ₜ = ⁅G⟦n⟧ₜ, G⟦n⟧ₜ⁆ₜ := rfl

/-- Closed commutators map monotonically under continuous homomorphisms. -/
theorem closedCommutator_map_mono
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {Q : Type v} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    {G₁ G₂ : Subgroup G} {Q₁ Q₂ : Subgroup Q} {f : G →ₜ* Q}
    (h₁ : G₁.map (f : G →* Q) ≤ Q₁)
    (h₂ : G₂.map (f : G →* Q) ≤ Q₂) :
    (⁅G₁, G₂⁆ₜ).map (f : G →* Q) ≤ ⁅Q₁, Q₂⁆ₜ := by
  dsimp [closedCommutator]
  have hcomm :
      (⁅G₁, G₂⁆).map (f : G →* Q) ≤ ⁅Q₁, Q₂⁆ := by
    calc
      (⁅G₁, G₂⁆).map (f : G →* Q) = ⁅G₁.map (f : G →* Q), G₂.map (f : G →* Q)⁆ := by
        simpa using Subgroup.map_commutator G₁ G₂ (f : G →* Q)
      _ ≤ ⁅Q₁, Q₂⁆ := Subgroup.commutator_mono h₁ h₂
  exact TopologicalGroup.map_closure_le_closure (f := f) (G₁ := ⁅G₁, G₂⁆) (Q₁ := ⁅Q₁, Q₂⁆) hcomm

/--
If target subgroups lie in the corresponding images, then their commutator lies in the image of
the source closed commutator.
-/
lemma commutator_le_map_closedCommutator
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {Q : Type v} [Group Q]
    (φ : G →* Q)
    {G₁ G₂ : Subgroup G} {Q₁ Q₂ : Subgroup Q}
    (h₁ : Q₁ ≤ G₁.map φ) (h₂ : Q₂ ≤ G₂.map φ) :
    ⁅Q₁, Q₂⁆ ≤ (⁅G₁, G₂⁆ₜ).map φ := by
  have h0 :
      ⁅Q₁, Q₂⁆ ≤ (⁅G₁, G₂⁆).map φ :=
    Subgroup.commutator_le_map_commutator
      (f := φ) (H₁ := G₁) (H₂ := G₂) (K₁ := Q₁) (K₂ := Q₂) h₁ h₂
  have hmono :
      (⁅G₁, G₂⁆).map φ ≤ (⁅G₁, G₂⁆ₜ).map φ := by
    simpa [closedCommutator] using
      Subgroup.map_mono (f := φ) (Subgroup.le_topologicalClosure (s := ⁅G₁, G₂⁆))
  exact le_trans h0 hmono

/--
The map carries the closed commutator subgroup to the corresponding closed commutator subgroup
under the stated equality hypothesis.
-/
theorem map_closedCommutator_eq_of_map_eq
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {Q : Type v} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    {G₁ G₂ : Subgroup G} {Q₁ Q₂ : Subgroup Q} {f : G →ₜ* Q}
    (h₁ : G₁.map (f : G →* Q) = Q₁)
    (h₂ : G₂.map (f : G →* Q) = Q₂)
    (hclosed : IsClosed (((⁅G₁,G₂⁆ₜ).map (f : G →* Q) : Subgroup Q) : Set Q)) :
    (⁅G₁, G₂⁆ₜ).map (f : G →* Q) = ⁅Q₁, Q₂⁆ₜ := by
  let φ : G →* Q := (f : G →* Q)
  have hle : (⁅G₁, G₂⁆ₜ).map φ ≤ ⁅Q₁, Q₂⁆ₜ := by
    simpa [φ] using
      closedCommutator_map_mono (f := f)
        (h₁ := by simpa using le_of_eq h₁)
        (h₂ := by simpa using le_of_eq h₂)
  have hge : ⁅Q₁, Q₂⁆ₜ ≤ (⁅G₁, G₂⁆ₜ).map φ := by
    dsimp [closedCommutator]
    refine
      Subgroup.topologicalClosure_minimal
        (s := ⁅Q₁, Q₂⁆) (t := (⁅G₁, G₂⁆ₜ).map φ) ?_ hclosed
    refine commutator_le_map_closedCommutator (φ := φ) (G₁ := G₁) (G₂ := G₂) ?_ ?_
    · simpa [φ] using ge_of_eq h₁
    · simpa [φ] using ge_of_eq h₂
  exact le_antisymm hle (by simpa [closedCommutator] using hge)

/--
Closed commutators of topologically characteristic subgroups are again topologically
characteristic.
-/
theorem closedCommutator_topologicallyCharacteristic
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (G₁ G₂ : Subgroup G)
    (h₁ : G₁.TopologicallyCharacteristic)
    (h₂ : G₂.TopologicallyCharacteristic) :
    (⁅G₁, G₂⁆ₜ).TopologicallyCharacteristic := by
  have hcomm : (⁅G₁, G₂⁆).TopologicallyCharacteristic := by
    infer_instance
  simpa [closedCommutator] using
    (Subgroup.TopologicallyCharacteristic.topologicalClosure
      (H := ⁅G₁, G₂⁆) (hH := hcomm))

/-- Restarting the ambient closed derived series adds indices. -/
@[simp] lemma topDerived_add
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (m n : ℕ) :
    closedDerivedSeries (G := G) (G⟦m⟧ₜ) n = G⟦m + n⟧ₜ := by
  induction n with
  | zero =>
      simp only [closedDerivedSeries_zero, add_zero]
  | succ n ihn =>
      rw [show m + (n + 1) = m + n + 1 by rw [Nat.add_assoc]]
      rw [topDerivedTop_succ]
      simp only [closedDerivedSeries_succ, ihn]

/-- The ambient closed derived series is antitone. -/
theorem topDerivedTop_antitone
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    Antitone (topDerivedTop G) := by
  apply antitone_nat_of_succ_le
  intro m
  dsimp [topDerivedTop, closedDerivedSeries, closedCommutator]
  exact
    Subgroup.topologicalClosure_minimal
      (s := ⁅G⟦m⟧ₜ, G⟦m⟧ₜ⁆)
      (t := G⟦m⟧ₜ)
      (Subgroup.commutator_le_self (G⟦m⟧ₜ))
      (by infer_instance)

/-- Every stage of the ambient closed derived series is topologically characteristic. -/
instance topDerivedTop_topologicallyCharacteristicInst
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {m : ℕ} :
    (topDerivedTop G m).TopologicallyCharacteristic := by
  induction m with
  | zero =>
      refine ⟨?_⟩
      intro e
      simp only [ContinuousMulEquiv.toMulEquiv_eq_coe, MulEquiv.toMonoidHom_eq_coe, topDerivedTop,
  closedDerivedSeries_zero, Subgroup.comap_top]
  | succ m ihm =>
      simpa [topDerivedTop, closedDerivedSeries] using
        closedCommutator_topologicallyCharacteristic
          (G₁ := G⟦m⟧ₜ) (G₂ := G⟦m⟧ₜ) ihm ihm

/-- The closed derived series is monotone under continuous homomorphisms. -/
theorem topDerived_map_le
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {Q : Type v} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (f : G →ₜ* Q) (m : ℕ) :
    (G⟦m⟧ₜ).map (f : G →* Q) ≤ Q⟦m⟧ₜ := by
  induction m with
  | zero =>
      simp only [topDerivedTop, closedDerivedSeries_zero, le_top]
  | succ m ih =>
      dsimp [topDerivedTop, closedDerivedSeries, closedCommutator]
      exact
        (TopologicalGroup.map_closure_le_closure (f := f)
          (G₁ := ⁅G⟦m⟧ₜ, G⟦m⟧ₜ⁆)
          (Q₁ := ⁅Q⟦m⟧ₜ, Q⟦m⟧ₜ⁆) <|
          by
            calc
              (⁅G⟦m⟧ₜ, G⟦m⟧ₜ⁆).map (f : G →* Q)
                  = ⁅(G⟦m⟧ₜ).map (f : G →* Q), (G⟦m⟧ₜ).map (f : G →* Q)⁆ := by
                      simpa using
                        (Subgroup.map_commutator (G⟦m⟧ₜ) (G⟦m⟧ₜ) (f : G →* Q))
              _ ≤ ⁅Q⟦m⟧ₜ, Q⟦m⟧ₜ⁆ := by
                    exact Subgroup.commutator_mono ih ih)

/-- The ambient closed derived series pulls back along continuous homomorphisms. -/
lemma topDerivedTop_le_comap
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {Q : Type v} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (f : G →ₜ* Q) (m : ℕ) :
    G⟦m⟧ₜ ≤ (Q⟦m⟧ₜ).comap (f : G →* Q) := by
  exact (Subgroup.map_le_iff_le_comap).1 (topDerived_map_le (f := f) m)

/--
A point in the ambient \(m\)-th derived subgroup lies in the first derived subgroup of any
larger subgroup containing the \((m-1)\)-st derived term.
-/
theorem mem_topDerived_one_of_mem_topDerived_of_le
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {K : Subgroup G} {m : ℕ} (hm : 1 ≤ m)
    (hK : G⟦m - 1⟧ₜ ≤ K)
    {x : G} (hx : x ∈ G⟦m⟧ₜ) :
    x ∈ closedDerivedSeries (G := G) K 1 := by
  have hmEq : m = (m - 1) + 1 := (tsub_add_cancel_of_le hm).symm
  have hx0 : x ∈ G⟦(m - 1) + 1⟧ₜ := hmEq ▸ hx
  rw [← topDerived_add (G := G) (m := m - 1) (n := 1)] at hx0
  have hmono :
      closedDerivedSeries (G := G) (G⟦m - 1⟧ₜ) 1 ≤ closedDerivedSeries (G := G) K 1 := by
    dsimp [closedDerivedSeries, closedCommutator]
    refine
      Subgroup.topologicalClosure_minimal
        (s := ⁅G⟦m - 1⟧ₜ, G⟦m - 1⟧ₜ⁆)
        (t := ⁅K, K⁆ₜ) ?_
        (Subgroup.isClosed_topologicalClosure (s := ⁅K, K⁆))
    exact (Subgroup.commutator_mono hK hK).trans (Subgroup.le_topologicalClosure _)
  exact hmono hx0

/--
The first derived subgroup of a closed subgroup maps back to the corresponding subgroup of the
ambient group.
-/
theorem topDerived_one_map_subtype_eq_of_isClosed_subgroup
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {H : Subgroup G} {K : Subgroup H} (hH : IsClosed (H : Set G)) :
    (closedDerivedSeries (G := H) K 1).map H.subtype =
      closedDerivedSeries (G := G) (K.map H.subtype) 1 := by
  have hclosedSubtype : IsClosedMap (H.subtype : H → G) := hH.isClosedMap_subtype_val
  have hclosure :
      closure ((fun y : H => (y : G)) '' (((⁅K, K⁆ : Subgroup H) : Set H))) =
        (fun y : H => (y : G)) '' closure (((⁅K, K⁆ : Subgroup H) : Set H)) :=
    hclosedSubtype.closure_image_eq_of_continuous continuous_subtype_val _
  have himg :
      ((fun y : H => (y : G)) '' (((⁅K, K⁆ : Subgroup H) : Set H))) =
        (((⁅K.map H.subtype, K.map H.subtype⁆ : Subgroup G) : Set G)) := by
    simpa [TopologicalGroup.image_subtype_eq_map] using
      congrArg (fun L : Subgroup G => (L : Set G))
        (Subgroup.map_commutator K K H.subtype)
  ext x
  change
    x ∈ ((fun y : H => (y : G)) '' ((((⁅K, K⁆).topologicalClosure : Subgroup H) : Set H))) ↔
      x ∈ (((⁅K.map H.subtype, K.map H.subtype⁆).topologicalClosure : Subgroup G) : Set G)
  change
    x ∈ ((fun y : H => (y : G)) '' closure (((⁅K, K⁆ : Subgroup H) : Set H))) ↔
      x ∈ closure (((⁅K.map H.subtype, K.map H.subtype⁆ : Subgroup G) : Set G))
  rw [← hclosure, himg]

/--
Surjective maps identify the stagewise closed derived subgroups once the commutator images are
closed.
-/
theorem topDerived_map_eq_of_surj
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {H : Type v} [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
    (f : G →ₜ* H) (hf : Function.Surjective f)
    (hclosed_comm :
      ∀ n : ℕ,
        IsClosed (((⁅G⟦n⟧ₜ, G⟦n⟧ₜ⁆ₜ).map (f : G →* H) : Subgroup H) : Set H))
    (n : ℕ) :
    (G⟦n⟧ₜ).map (f : G →* H) = H⟦n⟧ₜ := by
  induction n with
  | zero =>
      ext y
      constructor
      · rintro ⟨x, -, rfl⟩
        simp only [topDerivedTop, closedDerivedSeries_zero, MonoidHom.coe_ofClass, Subgroup.mem_top]
      · intro hy
        rcases hf y with ⟨x, rfl⟩
        exact ⟨x, by simp only [topDerivedTop, closedDerivedSeries_zero, Subgroup.coe_top,
            Set.mem_univ], rfl⟩
  | succ n ihn =>
      apply le_antisymm
      · exact topDerived_map_le (f := f) (m := n + 1)
      · dsimp [topDerivedTop, closedDerivedSeries, closedCommutator]
        refine
          Subgroup.topologicalClosure_minimal
            (s := ⁅H⟦n⟧ₜ, H⟦n⟧ₜ⁆)
            (t := (⁅G⟦n⟧ₜ, G⟦n⟧ₜ⁆ₜ).map (f : G →* H)) ?_
            (hclosed_comm n)
        calc
          ⁅H⟦n⟧ₜ, H⟦n⟧ₜ⁆
              = ⁅(G⟦n⟧ₜ).map (f : G →* H), (G⟦n⟧ₜ).map (f : G →* H)⁆ := by
                  simp only [ihn]
          _ = (⁅G⟦n⟧ₜ, G⟦n⟧ₜ⁆).map (f : G →* H) := by
                symm
                simpa using
                  (Subgroup.map_commutator (G⟦n⟧ₜ) (G⟦n⟧ₜ) (f : G →* H))
          _ ≤ (⁅G⟦n⟧ₜ, G⟦n⟧ₜ⁆ₜ).map (f : G →* H) := by
                exact Subgroup.map_mono (Subgroup.le_topologicalClosure _)

/--
Images of closed commutators of derived terms are closed when the source is compact and the
target is Hausdorff.
-/
theorem closedCommutator_topDerived_map_isClosed_of_compact
    {G H : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TopologicalSpace H] [Group H] [T2Space H]
    (f : G →ₜ* H) (n : ℕ) :
    IsClosed
      (((closedCommutator (topDerivedTop G n) (topDerivedTop G n)).map
        (f : G →* H) : Subgroup H) : Set H) := by
  let K : ClosedSubgroup G :=
    ⟨closedCommutator (topDerivedTop G n) (topDerivedTop G n), by
      dsimp [closedCommutator]
      exact isClosed_closure⟩
  change IsClosed ((((closedCommutator (topDerivedTop G n) (topDerivedTop G n)).map
    (f : G →* H) : Subgroup H) : Set H))
  exact
    (ProCGroups.Order.ClosedSubgroup.map K (f : G →* H) f.continuous_toFun).isClosed'

/-- The closed derived series is monotone in the initial subgroup. -/
theorem closedDerivedSeries_mono
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {K L : Subgroup G} (hKL : K ≤ L) (n : ℕ) :
    closedDerivedSeries (G := G) K n ≤ closedDerivedSeries (G := G) L n := by
  induction n with
  | zero =>
      simpa using hKL
  | succ n ih =>
      dsimp [closedDerivedSeries, closedCommutator]
      refine
        Subgroup.topologicalClosure_minimal
          (s := ⁅closedDerivedSeries (G := G) K n,
            closedDerivedSeries (G := G) K n⁆)
          (t := ⁅closedDerivedSeries (G := G) L n,
            closedDerivedSeries (G := G) L n⁆ₜ) ?_
          (Subgroup.isClosed_topologicalClosure
            (s := ⁅closedDerivedSeries (G := G) L n,
              closedDerivedSeries (G := G) L n⁆))
      exact
        (Subgroup.commutator_mono ih ih).trans
          (Subgroup.le_topologicalClosure
            (s := ⁅closedDerivedSeries (G := G) L n,
              closedDerivedSeries (G := G) L n⁆))

/--
The internal derived series of a closed subgroup maps to the corresponding ambient derived
series.
-/
theorem topDerived_map_subtype_eq_closedDerivedSeries_of_isClosed_subgroup
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : IsClosed (H : Set G)) (n : ℕ) :
    (topDerivedTop H n).map H.subtype =
      closedDerivedSeries (G := G) H n := by
  let incl : H →ₜ* G :=
    { toMonoidHom := H.subtype
      continuous_toFun := continuous_subtype_val }
  induction n with
  | zero =>
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, by simp only [topDerivedTop, closedDerivedSeries_zero, Subgroup.coe_top,
            Set.mem_univ], rfl⟩
  | succ n ih =>
      have hclosed :
          IsClosed
            (((closedCommutator (topDerivedTop H n) (topDerivedTop H n)).map
              (incl : H →* G) : Subgroup G) : Set G) := by
        exact
          TopologicalGroup.isClosed_map_of_isClosedMap
            (f := incl) hH.isClosedMap_subtype_val
            (K := closedCommutator (topDerivedTop H n) (topDerivedTop H n))
            (Subgroup.isClosed_topologicalClosure
              (s := ⁅topDerivedTop H n, topDerivedTop H n⁆))
      have hmap :=
        map_closedCommutator_eq_of_map_eq
          (f := incl) (h₁ := ih) (h₂ := ih) hclosed
      change
        (topDerivedTop H (n + 1)).map H.subtype =
          closedDerivedSeries (G := G) H (n + 1)
      exact hmap

/--
Higher ambient derived terms lie in the corresponding derived term of any open subgroup
containing the first derived term.
-/
theorem topDerivedTop_le_openSubgroup_pred_map_of_first_le
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (H : OpenSubgroup G) {m : ℕ} (hm : 1 ≤ m)
    (hfirst : topDerivedTop G 1 ≤ (H : Subgroup G)) :
    topDerivedTop G m ≤
      (topDerivedTop ↥(H : Subgroup G) (m - 1)).map
        (Subgroup.subtype (H : Subgroup G)) := by
  have hpred : 1 + (m - 1) = m := by
    simpa [Nat.add_comm] using
      Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (Nat.ne_of_gt hm))
  intro x hx
  have htop :
      closedDerivedSeries (G := G) (topDerivedTop G 1) (m - 1) =
        topDerivedTop G m := by
    simpa [hpred] using
      (topDerived_add (G := G) (m := 1) (n := m - 1))
  have hxseries :
      x ∈ closedDerivedSeries (G := G) (topDerivedTop G 1) (m - 1) := by
    rw [htop]
    exact hx
  have hxH :
      x ∈ closedDerivedSeries (G := G) (H : Subgroup G) (m - 1) :=
    closedDerivedSeries_mono hfirst (m - 1) hxseries
  have hHclosed : IsClosed (((H : Subgroup G) : Set G)) :=
    ProCGroups.openSubgroup_isClosed (G := G) H
  rw [topDerived_map_subtype_eq_closedDerivedSeries_of_isClosed_subgroup
    (G := G) (H := (H : Subgroup G)) hHclosed (m - 1)]
  exact hxH

/--
If a profinite element projects into all open-normal derived lifts and the corresponding ambient
derived term is trivial, then the element is trivial.
-/
theorem eq_one_of_mem_all_openNormalSubgroup_derived
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [TotallyDisconnectedSpace Q]
    {m : ℕ} (hm : 3 ≤ m)
    (hQm : topDerivedTop Q m = ⊥)
    {d : Q}
    (hproj :
      ∀ H : OpenNormalSubgroup Q,
        topDerivedTop Q 1 ≤ (H : Subgroup Q) →
        d ∈ (topDerivedTop ↥(H : Subgroup Q) (m - 1)).map
          (Subgroup.subtype (H : Subgroup Q))) :
    d = 1 := by
  classical
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  have hpred : 1 + (m - 1) = m := by
    simpa [Nat.add_comm] using Nat.succ_pred_eq_of_pos hmpos
  have hd_all : ∀ U : OpenNormalSubgroup Q, d ∈ (U : Subgroup Q) := by
    intro U
    let qU : Q →ₜ* Q ⧸ (U : Subgroup Q) :=
      ProCGroups.ProC.OpenNormalSubgroup.quotientProj U
    let K : Subgroup Q := topDerivedTop Q 1
    have hKnormal : K.Normal := by
      change (topDerivedTop Q 1).Normal
      infer_instance
    let Hsub : Subgroup Q := K ⊔ (U : Subgroup Q)
    have hHopen : IsOpen (Hsub : Set Q) := by
      exact
        Subgroup.isOpen_of_openSubgroup Hsub
          (show (U : Subgroup Q) ≤ Hsub from le_sup_right)
    let H : OpenNormalSubgroup Q :=
      { toOpenSubgroup :=
          { toSubgroup := Hsub
            isOpen' := hHopen }
        isNormal' := by
          dsimp [Hsub]
          infer_instance }
    have hKleH : topDerivedTop Q 1 ≤ (H : Subgroup Q) := by
      change K ≤ Hsub
      exact le_sup_left
    rcases hproj H hKleH with ⟨y, hy, hyd⟩
    let inclK : K →ₜ* Q :=
      { toMonoidHom := K.subtype
        continuous_toFun := continuous_subtype_val }
    let qK0 : K →ₜ* Q ⧸ (U : Subgroup Q) := qU.comp inclK
    let qKr : K →ₜ* qK0.toMonoidHom.range := ProCGroups.ContinuousMonoidHom.rangeRestrict qK0
    let : DiscreteTopology (Q ⧸ (U : Subgroup Q)) :=
      QuotientGroup.discreteTopology
        (ProCGroups.openNormalSubgroup_isOpen (G := Q) U)
    have hKclosed : IsClosed (K : Set Q) := by
      change IsClosed ((topDerivedTop Q 1 : Subgroup Q) : Set Q)
      infer_instance
    have hKmap :
        (topDerivedTop K (m - 1)).map K.subtype =
          closedDerivedSeries (G := Q) K (m - 1) :=
      topDerived_map_subtype_eq_closedDerivedSeries_of_isClosed_subgroup
        (G := Q) (H := K) hKclosed (m - 1)
    have hKmap_bot : (topDerivedTop K (m - 1)).map K.subtype = ⊥ := by
      calc
        (topDerivedTop K (m - 1)).map K.subtype =
            closedDerivedSeries (G := Q) K (m - 1) := hKmap
        _ = topDerivedTop Q (1 + (m - 1)) := by
              simpa [K] using
                (topDerived_add (G := Q) (m := 1) (n := m - 1))
        _ = topDerivedTop Q m := by rw [hpred]
        _ = ⊥ := hQm
    have hKder_bot : topDerivedTop K (m - 1) = ⊥ := by
      apply le_antisymm
      · intro z hz
        have hzker :
            z ∈ (K.subtype : K →* Q).ker := by
          exact
            (Subgroup.map_eq_bot_iff
              (f := (K.subtype : K →* Q))
              (H := topDerivedTop K (m - 1))).1 hKmap_bot hz
        have hzval : (z : Q) = 1 := by
          exact (MonoidHom.mem_ker.mp hzker)
        exact Subgroup.mem_bot.mpr (Subtype.ext hzval)
      · exact bot_le
    have hclosed_comm :
        ∀ n : ℕ,
          IsClosed
            (((closedCommutator (topDerivedTop K n) (topDerivedTop K n)).map
              (qKr : K →* qK0.toMonoidHom.range) :
                Subgroup qK0.toMonoidHom.range) : Set qK0.toMonoidHom.range) := by
      intro n
      exact isClosed_discrete _
    have hKrange_eq :
        (topDerivedTop K (m - 1)).map
            (qKr : K →* qK0.toMonoidHom.range) =
          topDerivedTop qK0.toMonoidHom.range (m - 1) := by
      exact
        topDerived_map_eq_of_surj
          (f := qKr)
          (MonoidHom.rangeRestrict_surjective qK0.toMonoidHom)
          hclosed_comm (m - 1)
    have hKrange_bot : topDerivedTop qK0.toMonoidHom.range (m - 1) = ⊥ := by
      rw [← hKrange_eq, hKder_bot]
      exact Subgroup.map_bot (f := (qKr : K →* qK0.toMonoidHom.range))
    have hqH_mem_Krange :
        ∀ z : H, qU z.1 ∈ qK0.toMonoidHom.range := by
      intro z
      have hzH : z.1 ∈ Hsub := z.2
      rcases
          (Subgroup.mem_sup_of_normal_right (s := K) (t := (U : Subgroup Q))).1
            hzH with
        ⟨k, hk, u, hu, hku⟩
      refine ⟨⟨k, hk⟩, ?_⟩
      change qU k = qU z.1
      rw [← hku]
      rw [map_mul]
      have hqu : qU u = 1 :=
        (ProCGroups.ProC.OpenNormalSubgroup.quotientProj_eq_one_iff
          (U := U) (x := u)).2 hu
      rw [hqu, mul_one]
    let qHK : ↥(H : Subgroup Q) →ₜ* qK0.toMonoidHom.range :=
      { toMonoidHom := qU.toMonoidHom.comp H.subtype |>.codRestrict
          qK0.toMonoidHom.range hqH_mem_Krange
        continuous_toFun :=
          (qU.continuous.comp continuous_subtype_val).subtype_mk hqH_mem_Krange }
    have hyK :
        qHK y ∈ topDerivedTop qK0.toMonoidHom.range (m - 1) := by
      exact topDerived_map_le (f := qHK) (m := m - 1) ⟨y, hy, rfl⟩
    have hqy_one : (qU y.1) = 1 := by
      have hybot : qHK y ∈ (⊥ : Subgroup qK0.toMonoidHom.range) := by
        rw [hKrange_bot] at hyK
        exact hyK
      have hsub : qHK y = 1 := by
        exact Subgroup.mem_bot.mp hybot
      exact congrArg Subtype.val hsub
    have hqd_one : qU d = 1 := by
      rw [← hyd]
      exact hqy_one
    exact
      (ProCGroups.ProC.OpenNormalSubgroup.quotientProj_eq_one_iff
        (U := U) (x := d)).mp hqd_one
  let Bot : ClosedSubgroup Q := ⊥
  let : ((Bot : Subgroup Q).Normal) := by
    change (⊥ : Subgroup Q).Normal
    infer_instance
  have hdbot : d ∈ (Bot : Subgroup Q) := by
    rw [ProCGroups.ProC.closedSubgroup_eq_sInf_openNormal (G := Q) Bot]
    simp only [Subgroup.mem_sInf, Set.mem_ofPred_eq]
    intro N hN
    let U : OpenNormalSubgroup Q :=
      { toOpenSubgroup :=
          { toSubgroup := N
            isOpen' := hN.1 }
        isNormal' := hN.2.2 }
    exact hd_all U
  exact Subgroup.mem_bot.mp hdbot

/-- Topological cyclic generation forces the first derived term to be trivial. -/
theorem topDerivedTop_one_eq_bot_of_topologicallyGenerates_singleton
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    [T2Space Q] (x : Q)
    (hgen : ProCGroups.Generation.TopologicallyGenerates (G := Q) ({x} : Set Q)) :
    topDerivedTop Q 1 = ⊥ := by
  have hcyc :
      (ProCGroups.Generation.closedSubgroupGenerated (G := Q) ({x} : Set Q) : Subgroup Q) =
        ⊤ := by
    unfold ProCGroups.Generation.TopologicallyGenerates at hgen
    simpa [ProCGroups.Generation.closedSubgroupGenerated] using hgen
  have hxcent_top : ProCGroups.GroupTheory.centralizerOf x = ⊤ := by
    simpa [hcyc] using
      ProCGroups.GroupTheory.centralizerOf_zpow_eq_closedSubgroupGenerated_of_topologicallyGenerates
        (G := Q) x (1 : ℤ) hgen
  have hcomm : ∀ a b : Q, a * b = b * a := by
    intro a b
    have hbcx : b ∈ ProCGroups.GroupTheory.centralizerOf x := by
      simp only [hxcent_top, Subgroup.mem_top]
    have hx_cb : x ∈ ProCGroups.GroupTheory.centralizerOf b := by
      rw [ProCGroups.GroupTheory.mem_centralizerOf_iff]
      exact (ProCGroups.GroupTheory.mem_centralizerOf_iff.mp hbcx).symm
    have hcyc_le_cb :
        (ProCGroups.Generation.closedSubgroupGenerated (G := Q) ({x} : Set Q) : Subgroup Q) ≤
          ProCGroups.GroupTheory.centralizerOf b := by
      exact
        ProCGroups.GroupTheory.closedSubgroupGenerated_le_centralizer_of_subset
          (G := Q) (S := ({x} : Set Q)) (T := ({b} : Set Q)) (by
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            subst y
            simpa [ProCGroups.GroupTheory.centralizerOf] using hx_cb)
    have ha_cb : a ∈ ProCGroups.GroupTheory.centralizerOf b := by
      have : a ∈ (ProCGroups.Generation.closedSubgroupGenerated (G := Q) ({x} : Set Q) :
          Subgroup Q) := by
        rw [hcyc]
        simp only [Subgroup.mem_top]
      exact hcyc_le_cb this
    exact ProCGroups.GroupTheory.mem_centralizerOf_iff.mp ha_cb
  have hcommutator_bot : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _
    rw [Subgroup.mem_centralizer_iff]
    intro b _
    exact hcomm b a
  change closedCommutator (⊤ : Subgroup Q) (⊤ : Subgroup Q) = ⊥
  dsimp [closedCommutator]
  rw [hcommutator_bot]
  apply le_antisymm
  · exact
      Subgroup.topologicalClosure_minimal
        (s := (⊥ : Subgroup Q)) (t := (⊥ : Subgroup Q)) le_rfl
        (isClosed_singleton (x := (1 : Q)))
  · exact Subgroup.le_topologicalClosure (s := (⊥ : Subgroup Q))

/-- The induced map on maximal finite-step solvable quotients. -/
def topMaxSolvQuotMap
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {Q : Type v} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (f : G →ₜ* Q) (m : ℕ) :
    (G^ₘ m) →ₜ* (Q^ₘ m) := by
  exact QuotientGroup.mapₜ (G⟦m⟧ₜ) (Q⟦m⟧ₜ) f (topDerivedTop_le_comap (f := f) m)

scoped[ProCGroupsSolvableQuotients] notation f "⟪" m "⟫" =>
  ProCGroups.FiniteStepSolvableQuotients.topMaxSolvQuotMap f m

open scoped ProCGroupsSolvableQuotients

/--
The induced map on finite-step solvable quotients is an equivalence under surjectivity and the
required kernel containment for the subgroup preimage.
-/
noncomputable def TopologicalGroup.restrictPreimage_topMaxSolvQuot_mulEquiv
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {Q : Type v} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    {π : G →ₜ* Q} {Q₁ : Subgroup Q} {m : ℕ}
    (hπ : Function.Surjective π)
    (hclosed : IsClosedMap (ProCGroups.ContinuousMonoidHom.restrictPreimage π Q₁))
    (hker :
      (ProCGroups.ContinuousMonoidHom.restrictPreimage π Q₁).ker ≤
        topDerivedTop ↥(Q₁.comap (π : G →* Q)) m) :
    MaxSolvQuot (Q₁.comap (π : G →* Q)) m ≃* MaxSolvQuot Q₁ m := by
  classical
  let G0 : Type u := Q₁.comap (π : G →* Q)
  let f : G0 →ₜ* Q₁ := ProCGroups.ContinuousMonoidHom.restrictPreimage π Q₁
  have hf : Function.Surjective f := by
    change Function.Surjective (ProCGroups.ContinuousMonoidHom.restrictPreimage π Q₁)
    exact ProCGroups.ContinuousMonoidHom.restrictPreimage_surjective π hπ Q₁
  have hclosed' : IsClosedMap f := by
    change IsClosedMap (ProCGroups.ContinuousMonoidHom.restrictPreimage π Q₁)
    exact hclosed
  have hker' : f.toMonoidHom.ker ≤ topDerivedTop G0 m := by
    change (ProCGroups.ContinuousMonoidHom.restrictPreimage π Q₁).toMonoidHom.ker ≤
      topDerivedTop (Q₁.comap (π : G →* Q)) m
    exact hker
  have hclosed_comm :
      ∀ n : ℕ,
        IsClosed (((⁅G0⟦n⟧ₜ, G0⟦n⟧ₜ⁆ₜ).map (f : G0 →* Q₁) : Subgroup Q₁) : Set Q₁) := by
    intro n
    refine
      TopologicalGroup.isClosed_map_of_isClosedMap (f := f) hclosed'
        (K := ⁅G0⟦n⟧ₜ, G0⟦n⟧ₜ⁆ₜ) ?_
    exact Subgroup.isClosed_topologicalClosure (s := ⁅G0⟦n⟧ₜ, G0⟦n⟧ₜ⁆)
  have hmap : (G0⟦m⟧ₜ).map (f : G0 →* Q₁) = Q₁⟦m⟧ₜ :=
    topDerived_map_eq_of_surj (f := f) hf hclosed_comm m
  have hcomap_eq :
      Subgroup.comap (f : G0 →* Q₁) (Q₁⟦m⟧ₜ) = G0⟦m⟧ₜ := by
    exact
      QuotientGroup.comap_eq_of_map_eq_of_ker_le
        (f := (f : G0 →* Q₁)) (N := G0⟦m⟧ₜ) (M := Q₁⟦m⟧ₜ) hmap hker'
  have hsurj :
      Function.Surjective ((f⟪m⟫) : MaxSolvQuot G0 m → MaxSolvQuot Q₁ m) := by
    have hcomp :
        Function.Surjective
          (fun x : G0 =>
            (QuotientGroup.mk : Q₁ → (Q₁ ⧸ Q₁⟦m⟧ₜ)) (f x)) :=
      (QuotientGroup.mk_surjective (s := Q₁⟦m⟧ₜ)).comp hf
    dsimp [topMaxSolvQuotMap, MaxSolvQuot]
    exact
      QuotientGroup.map_surjective_of_surjective
        (N := G0⟦m⟧ₜ)
        (M := Q₁⟦m⟧ₜ)
        (f := (f : G0 →* Q₁))
        (h := topDerivedTop_le_comap (f := f) m)
        hcomp
  have hker_eq_bot : (f⟪m⟫).toMonoidHom.ker = ⊥ := by
    have hker0 :
        (QuotientGroup.map
          (N := G0⟦m⟧ₜ)
          (M := Q₁⟦m⟧ₜ)
          (f := (f : G0 →* Q₁))
          (topDerivedTop_le_comap (f := f) m)).ker = ⊥ := by
      exact
        TopologicalGroup.ker_map_eq_bot_of_comap_eq
          (f := (f : G0 →* Q₁))
          (N := G0⟦m⟧ₜ) (M := Q₁⟦m⟧ₜ)
          (h := topDerivedTop_le_comap (f := f) m)
          hcomap_eq
    dsimp [topMaxSolvQuotMap, MaxSolvQuot, G0, f]
    exact hker0
  have hinj :
      Function.Injective ((f⟪m⟫) : MaxSolvQuot G0 m → MaxSolvQuot Q₁ m) := by
    have hinj0 : Function.Injective (f⟪m⟫).toMonoidHom :=
      (MonoidHom.ker_eq_bot_iff (f := (f⟪m⟫).toMonoidHom)).1 hker_eq_bot
    exact hinj0
  exact MulEquiv.ofBijective (((ProCGroups.ContinuousMonoidHom.restrictPreimage π
      Q₁)⟪m⟫).toMonoidHom)
    ⟨hinj, hsurj⟩

/-- The quotient map to the maximal \(m\)-step solvable quotient is surjective. -/
lemma continuousToMaxSolvQuot_surjective
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (m : ℕ) :
    Function.Surjective (continuousToMaxSolvQuot G m) := by
  change Function.Surjective (toMaxSolvQuot G m)
  exact QuotientGroup.mk_surjective (s := topDerivedTop G m)

/-- The quotient map kills exactly the \(m\)-th closed derived subgroup. -/
theorem continuousToMaxSolvQuot_eq_one_iff
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {m : ℕ} {x : G} :
    continuousToMaxSolvQuot G m x = 1 ↔ x ∈ topDerivedTop G m := by
  change toMaxSolvQuot G m x = 1 ↔ x ∈ topDerivedTop G m
  exact QuotientGroup.eq_one_iff (N := topDerivedTop G m) x

/--
The kernel of the ambient quotient map lands in the first closed derived subgroup of any
preimage open subgroup containing the previous derived term.
-/
theorem continuousToMaxSolvQuot_ker_le_topDerived_one_map_subtype_of_le
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {m : ℕ} (hm : 1 ≤ m)
    (H : OpenSubgroup (MaxSolvQuot G m))
    (hH :
      topDerivedTop G (m - 1) ≤
        ((H : Subgroup (MaxSolvQuot G m)).comap
          (continuousToMaxSolvQuot G m : G →* MaxSolvQuot G m))) :
    (continuousToMaxSolvQuot G m : G →* MaxSolvQuot G m).ker ≤
      (topDerivedTop
          ↥((preimageOpenSubgroup (continuousToMaxSolvQuot G m) H : OpenSubgroup G) :
            Subgroup G) 1).map
        (Subgroup.subtype
          ((preimageOpenSubgroup (continuousToMaxSolvQuot G m) H : OpenSubgroup G) :
            Subgroup G)) := by
  let Q : Type u := MaxSolvQuot G m
  let π : G →ₜ* Q := continuousToMaxSolvQuot G m
  let Hpre : OpenSubgroup G := preimageOpenSubgroup π H
  have hHpreOpen : IsOpen ((Hpre : Subgroup G) : Set G) := Hpre.isOpen'
  intro x hx
  have hxder : x ∈ topDerivedTop G m := by
    exact
      (continuousToMaxSolvQuot_eq_one_iff (G := G) (m := m) (x := x)).1
        ((MonoidHom.mem_ker).1 hx)
  have hxder' :
      x ∈ closedDerivedSeries (G := G)
        ((H : Subgroup Q).comap (π : G →* Q)) 1 := by
    simpa [π, Q] using
      (mem_topDerived_one_of_mem_topDerived_of_le (G := G) hm
        (by simpa [π, Q] using hH) hxder)
  have htopMap :
      ((⊤ : Subgroup ↥((H : Subgroup Q).comap (π : G →* Q))).map
        ((Subgroup.comap (π : G →* Q) H).subtype)) =
        (H : Subgroup Q).comap (π : G →* Q) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx'
      exact ⟨⟨x, hx'⟩, by simp only [Subgroup.coe_top, Set.mem_univ], rfl⟩
  have hmap :
      (topDerivedTop ↥((Hpre : Subgroup G)) 1).map ((Hpre : Subgroup G).subtype) =
        closedDerivedSeries (G := G) ((H : Subgroup Q).comap (π : G →* Q)) 1 := by
    have hmap0 :=
      topDerived_one_map_subtype_eq_of_isClosed_subgroup
        (G := G)
        (H := ((H : Subgroup Q).comap (π : G →* Q)))
        (K := (⊤ : Subgroup ↥((H : Subgroup Q).comap (π : G →* Q))))
        (Subgroup.isClosed_of_isOpen _ hHpreOpen)
    rw [htopMap] at hmap0
    change
      (topDerivedTop ↥((Hpre : Subgroup G)) 1).map ((Hpre : Subgroup G).subtype) =
        closedDerivedSeries (G := G) ((H : Subgroup Q).comap (π : G →* Q)) 1
    exact hmap0
  change x ∈ (topDerivedTop ↥((Hpre : Subgroup G)) 1).map ((Hpre : Subgroup G).subtype)
  rw [hmap]
  exact hxder'

/-- The first maximal solvable quotient is the topological abelianization. -/
theorem isMulTorsionFree_maxSolvQuot_one_of_isMulTorsionFree_topologicalAbelianization
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (hG : IsMulTorsionFree (TopologicalAbelianization G)) :
    IsMulTorsionFree (MaxSolvQuot G 1) := by
  change IsMulTorsionFree (TopologicalAbelianization G)
  exact hG

/--
The induced map between maximal finite-step solvable quotients of a subgroup preimage and the
target subgroup is an isomorphism under the expected kernel bound.
-/
theorem preimageOpenSubgroup_maxSolvQuot_mulEquiv_of_ker_le
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {Q : Type v} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (f : G →ₜ* Q) (hf : Function.Surjective f) (H : OpenSubgroup Q)
    (hclosed : IsClosedMap (ProCGroups.ContinuousMonoidHom.restrictPreimage f (H : Subgroup Q)))
    (n : ℕ)
    (hker :
      f.ker ≤
        (topDerivedTop
          ↥((preimageOpenSubgroup f H : OpenSubgroup G) : Subgroup G) n).map
            (Subgroup.subtype
              ((preimageOpenSubgroup f H : OpenSubgroup G) : Subgroup G))) :
    Nonempty
      (MaxSolvQuot ↥((preimageOpenSubgroup f H : OpenSubgroup G) : Subgroup G) n ≃*
        MaxSolvQuot ↥(H : Subgroup Q) n) := by
  let Hpre : OpenSubgroup G := preimageOpenSubgroup f H
  have hker' :
      (ProCGroups.ContinuousMonoidHom.restrictPreimage f (H : Subgroup Q)).ker ≤
        topDerivedTop ↥((Hpre : Subgroup G)) n := by
    intro x hx
    have hxker : x.1 ∈ f.ker := by
      change ProCGroups.ContinuousMonoidHom.restrictPreimage f (H : Subgroup Q) x = 1 at hx
      change f x.1 = 1
      exact congrArg Subtype.val hx
    have hxder :
        x.1 ∈
          (topDerivedTop ↥((Hpre : Subgroup G)) n).map
            ((Hpre : Subgroup G).subtype) :=
      hker hxker
    rcases hxder with ⟨y, hy, hyx⟩
    exact Subtype.ext hyx ▸ hy
  exact
    ⟨TopologicalGroup.restrictPreimage_topMaxSolvQuot_mulEquiv
      (π := f) (Q₁ := (H : Subgroup Q)) (m := n) hf hclosed hker'⟩

end ProCGroups.FiniteStepSolvableQuotients
