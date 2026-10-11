/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.QuotientGroup.Basic
import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.Script

/-!
# Reidemeister Schreier / Discrete / Presentations / Kernel Quotient

This module identifies a presented free-group kernel with its relator
quotient.  It packages the canonical surjection, computes its kernel, and
derives quotient equivalences for the conjugate and transversal relators.
-/

namespace ReidemeisterSchreier.Discrete.Presentations

/-- The kernel of the map from the presented group is the image of the free-group lift kernel. -/
theorem presentedGroup_toGroup_ker_eq_map_freeGroupLift_ker
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A}
    (hrels : ∀ r ∈ rels, FreeGroup.lift f r = 1) :
    (PresentedGroup.toGroup (rels := rels) (f := f) hrels).ker =
      Subgroup.map (PresentedGroup.mk rels) (FreeGroup.lift f).ker := by
  exact QuotientGroup.ker_lift (Subgroup.normalClosure rels) (FreeGroup.lift f)
    (PresentedGroup.to_group_eq_one_of_mem_closure hrels)

/--
The Reidemeister--Schreier map is determined on generators and respects the rewritten relator
relations.
-/
def presentedFreeKernelToPresentedKernelHom
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A}
    (hrels : ∀ r ∈ rels, FreeGroup.lift f r = 1) :
    (FreeGroup.lift f).ker →*
      (PresentedGroup.toGroup (rels := rels) (f := f) hrels).ker where
  toFun k :=
    ⟨PresentedGroup.mk rels k, by
      change FreeGroup.lift f (k : FreeGroup X) = 1
      exact k.property⟩
  map_one' := by
    ext
    simp only [OneMemClass.coe_one, map_one]
  map_mul' k l := by
    ext
    simp only [Subgroup.coe_mul, map_mul, MulMemClass.mk_mul_mk]

/-- Every element of the presented kernel lifts to an element of the free-group lift kernel. -/
theorem presentedFreeKernelToPresentedKernelHom_surjective
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A}
    (hrels : ∀ r ∈ rels, FreeGroup.lift f r = 1) :
    Function.Surjective (presentedFreeKernelToPresentedKernelHom hrels) := by
  intro y
  have hy :
      (y : PresentedGroup rels) ∈
        Subgroup.map (PresentedGroup.mk rels) (FreeGroup.lift f).ker := by
    rw [← presentedGroup_toGroup_ker_eq_map_freeGroupLift_ker hrels]
    exact y.property
  rcases hy with ⟨x, hx, hxy⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  ext
  exact hxy

/-- The kernel of the restricted map to the presented kernel is the pullback of the relator
normal closure. -/
theorem presentedFreeKernelToPresentedKernelHom_ker_eq_comap_normalClosure
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A}
    (hrels : ∀ r ∈ rels, FreeGroup.lift f r = 1) :
    (presentedFreeKernelToPresentedKernelHom hrels).ker =
      Subgroup.comap ((FreeGroup.lift f).ker.subtype) (Subgroup.normalClosure rels) := by
  ext k
  constructor
  · intro hk
    rw [MonoidHom.mem_ker] at hk
    have hkval := congrArg Subtype.val hk
    change PresentedGroup.mk rels (k : FreeGroup X) = 1 at hkval
    exact PresentedGroup.mk_eq_one_iff.mp hkval
  · intro hk
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change PresentedGroup.mk rels (k : FreeGroup X) = 1
    exact PresentedGroup.mk_eq_one_iff.mpr hk

/-- Quotienting the free lift kernel by the pulled-back relator closure gives the presented
kernel. -/
noncomputable def presentedFreeKernelRelatorQuotientEquivPresentedKernel
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A}
    (hrels : ∀ r ∈ rels, FreeGroup.lift f r = 1) :
    (FreeGroup.lift f).ker ⧸
        Subgroup.comap ((FreeGroup.lift f).ker.subtype) (Subgroup.normalClosure rels) ≃*
      (PresentedGroup.toGroup (rels := rels) (f := f) hrels).ker :=
  (QuotientGroup.quotientMulEquivOfEq
    (presentedFreeKernelToPresentedKernelHom_ker_eq_comap_normalClosure hrels).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (φ := presentedFreeKernelToPresentedKernelHom hrels)
        (presentedFreeKernelToPresentedKernelHom_surjective hrels))

/-- The relators in the free lift kernel obtained by conjugating defining relators by
arbitrary words. -/
def freeKernelConjugateRelatorSet
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A} :
    Set (FreeGroup.lift f).ker :=
  { z | ∃ g : FreeGroup X, ∃ r ∈ rels, (z : FreeGroup X) = g * r * g⁻¹ }

/-- The conjugate relators obtained using only conjugating words from a chosen transversal. -/
def freeKernelTransversalRelatorSet
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A}
    (T : Set (FreeGroup X)) :
    Set (FreeGroup.lift f).ker :=
  { z | ∃ t ∈ T, ∃ r ∈ rels, (z : FreeGroup X) = t * r * t⁻¹ }

/-- Every transversal conjugate relator is an unrestricted conjugate relator. -/
theorem freeKernelTransversalRelatorSet_subset_conjugateRelatorSet
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A}
    (T : Set (FreeGroup X)) :
    freeKernelTransversalRelatorSet (f := f) (rels := rels) T ⊆
      freeKernelConjugateRelatorSet (f := f) (rels := rels) := by
  intro z hz
  rcases hz with ⟨t, _ht, r, hr, hzval⟩
  exact ⟨t, r, hr, hzval⟩

/--
The normal closure of the free-kernel transversal relator set equals the normal closure of the
corresponding conjugate relator set.
-/
theorem freeKernelTransversalRelatorSet_normalClosure_eq_conjugateRelatorSet
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A}
    (hrels : ∀ r ∈ rels, FreeGroup.lift f r = 1) {T : Set (FreeGroup X)}
    (hT : Subgroup.IsComplement ((FreeGroup.lift f).ker : Set (FreeGroup X)) T) :
    Subgroup.normalClosure (freeKernelTransversalRelatorSet (f := f) (rels := rels) T) =
      Subgroup.normalClosure (freeKernelConjugateRelatorSet (f := f) (rels := rels)) := by
  let L : Subgroup (FreeGroup X) := (FreeGroup.lift f).ker
  let Sₜ : Set L := freeKernelTransversalRelatorSet (f := f) (rels := rels) T
  let S : Set L := freeKernelConjugateRelatorSet (f := f) (rels := rels)
  refine le_antisymm ?_ ?_
  · exact Subgroup.normalClosure_le_normal
      (fun z hz => Subgroup.subset_normalClosure
        (freeKernelTransversalRelatorSet_subset_conjugateRelatorSet T hz))
  · refine Subgroup.normalClosure_le_normal ?_
    intro z hz
    rcases hz with ⟨g, r, hr, hzval⟩
    rcases (hT.existsUnique g).exists with ⟨kt, hkt⟩
    let k : L := ⟨kt.1.1, kt.1.2⟩
    let t : FreeGroup X := kt.2.1
    have ht : t ∈ T := kt.2.2
    have hg : (k : FreeGroup X) * t = g := hkt
    have hwL : t * r * t⁻¹ ∈ L := by
      change FreeGroup.lift f (t * r * t⁻¹) = 1
      simp only [map_mul, hrels r hr, mul_one, map_inv, mul_inv_cancel]
    let w : L := ⟨t * r * t⁻¹, hwL⟩
    have hwSₜ : w ∈ Sₜ := by
      refine ⟨t, ht, r, hr, ?_⟩
      rfl
    let N : Subgroup L := Subgroup.normalClosure Sₜ
    have hwN : w ∈ N := Subgroup.subset_normalClosure hwSₜ
    have hconj : k * w * k⁻¹ ∈ N := by
      simpa [MulAut.conj_apply] using (Subgroup.normalClosure_normal.conj_mem w hwN k)
    have hzconj : z = k * w * k⁻¹ := by
      apply Subtype.ext
      change (z : FreeGroup X) =
        (k : FreeGroup X) * (w : FreeGroup X) * (k : FreeGroup X)⁻¹
      rw [hzval, ← hg]
      change ((k : FreeGroup X) * t) * r * ((k : FreeGroup X) * t)⁻¹ =
        (k : FreeGroup X) * (t * r * t⁻¹) * (k : FreeGroup X)⁻¹
      group
    simpa [Sₜ, N, hzconj] using hconj

/-- Every conjugate relator in the free lift kernel lies over the original relator normal
closure. -/
theorem freeKernelConjugateRelatorSet_subset_comap_normalClosure
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A} :
    freeKernelConjugateRelatorSet (f := f) (rels := rels) ⊆
      Subgroup.comap ((FreeGroup.lift f).ker.subtype) (Subgroup.normalClosure rels) := by
  intro z hz
  rcases hz with ⟨g, r, hr, hz⟩
  change (z : FreeGroup X) ∈ Subgroup.normalClosure rels
  rw [hz]
  exact Subgroup.conjugatesOfSet_subset_normalClosure
    (Group.mem_conjugatesOfSet_iff.mpr ⟨r, hr, isConj_iff.2 ⟨g, rfl⟩⟩)

/-- The normal closure of the conjugate relators is contained in the pulled-back relator closure. -/
theorem freeKernelConjugateRelatorSet_normalClosure_le_comap_normalClosure
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A} :
    Subgroup.normalClosure (freeKernelConjugateRelatorSet (f := f) (rels := rels)) ≤
      Subgroup.comap ((FreeGroup.lift f).ker.subtype) (Subgroup.normalClosure rels) := by
  exact Subgroup.normalClosure_le_normal
    (freeKernelConjugateRelatorSet_subset_comap_normalClosure (f := f) (rels := rels))

/-- Arbitrary conjugate relators normally generate the pullback of the original relator closure. -/
theorem freeKernelConjugateRelatorSet_normalClosure_eq_comap_normalClosure
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A}
    (hrels : ∀ r ∈ rels, FreeGroup.lift f r = 1) :
    Subgroup.normalClosure (freeKernelConjugateRelatorSet (f := f) (rels := rels)) =
      Subgroup.comap ((FreeGroup.lift f).ker.subtype) (Subgroup.normalClosure rels) := by
  let L : Subgroup (FreeGroup X) := (FreeGroup.lift f).ker
  let S : Set L := freeKernelConjugateRelatorSet (f := f) (rels := rels)
  let N : Subgroup L := Subgroup.normalClosure S
  have hle :
      N ≤ Subgroup.comap L.subtype (Subgroup.normalClosure rels) := by
    simpa [L, S, N] using
      freeKernelConjugateRelatorSet_normalClosure_le_comap_normalClosure (f := f) (rels := rels)
  have hconj :
      ∀ (g : FreeGroup X) (n : L), n ∈ N →
        MulAut.conjNormal (H := L) g n ∈ N := by
    intro g
    let θ : MulAut L := MulAut.conjNormal (H := L) g
    have hSmap : S ⊆ Subgroup.comap θ.toMonoidHom N := by
      intro z hz
      rcases hz with ⟨a, r, hr, hzval⟩
      refine Subgroup.subset_normalClosure ?_
      refine ⟨g * a, r, hr, ?_⟩
      calc
        ↑((MulEquiv.toMonoidHom θ) z) = g * (z : FreeGroup X) * g⁻¹ := by
          simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conjNormal_apply, θ]
        _ = g * a * r * (g * a)⁻¹ := by
          rw [hzval]
          group
    have hNmap : N ≤ Subgroup.comap θ.toMonoidHom N := by
      simpa [N] using Subgroup.normalClosure_le_normal hSmap
    exact fun n hn => hNmap hn
  let H : Subgroup (FreeGroup X) := Subgroup.map L.subtype N
  have hHnormal : H.Normal := by
    refine ⟨?_⟩
    intro x hx g
    rcases hx with ⟨n, hn, rfl⟩
    refine ⟨MulAut.conjNormal (H := L) g n, hconj g n hn, ?_⟩
    exact MulAut.conjNormal_apply g n
  have hrels_le_H : rels ⊆ H := by
    intro r hr
    have hrL : r ∈ L := by
      exact MonoidHom.mem_ker.mpr (hrels r hr)
    let z : L := ⟨r, hrL⟩
    have hzS : z ∈ S := by
      refine ⟨1, r, hr, ?_⟩
      simp only [one_mul, inv_one, mul_one, z]
    refine ⟨z, Subgroup.subset_normalClosure hzS, ?_⟩
    rfl
  have hnormalClosure_le_H : Subgroup.normalClosure rels ≤ H := by
    exact Subgroup.normalClosure_le_normal hrels_le_H
  refine le_antisymm hle ?_
  intro k hk
  have hkH : (k : FreeGroup X) ∈ H := hnormalClosure_le_H hk
  rcases hkH with ⟨n, hn, hnval⟩
  have hkn : k = n := Subtype.ext hnval.symm
  simpa [hkn] using hn

/-- Transversal conjugate relators normally generate the pullback of the original relator
closure. -/
theorem freeKernelTransversalRelatorSet_normalClosure_eq_comap_normalClosure
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A}
    (hrels : ∀ r ∈ rels, FreeGroup.lift f r = 1) {T : Set (FreeGroup X)}
    (hT : Subgroup.IsComplement ((FreeGroup.lift f).ker : Set (FreeGroup X)) T) :
    Subgroup.normalClosure (freeKernelTransversalRelatorSet (f := f) (rels := rels) T) =
      Subgroup.comap ((FreeGroup.lift f).ker.subtype) (Subgroup.normalClosure rels) :=
  (freeKernelTransversalRelatorSet_normalClosure_eq_conjugateRelatorSet hrels hT).trans
    (freeKernelConjugateRelatorSet_normalClosure_eq_comap_normalClosure hrels)

/-- The quotient of the free lift kernel by transversal relators is equivalent to the
presented kernel. -/
noncomputable def presentedFreeKernelTransversalRelatorQuotientEquivPresentedKernel
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A}
    (hrels : ∀ r ∈ rels, FreeGroup.lift f r = 1) {T : Set (FreeGroup X)}
    (hT : Subgroup.IsComplement ((FreeGroup.lift f).ker : Set (FreeGroup X)) T) :
    (FreeGroup.lift f).ker ⧸
        Subgroup.normalClosure (freeKernelTransversalRelatorSet (f := f) (rels := rels) T) ≃*
      (PresentedGroup.toGroup (rels := rels) (f := f) hrels).ker :=
  (QuotientGroup.quotientMulEquivOfEq
    (freeKernelTransversalRelatorSet_normalClosure_eq_comap_normalClosure hrels hT)).trans
      (presentedFreeKernelRelatorQuotientEquivPresentedKernel hrels)

/-- Pulling transversal relators back to a free basis gives a relator quotient equivalent to
the presented kernel. -/
noncomputable def presentedFreeKernelSchreierRelatorQuotientEquivPresentedKernel
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A}
    (hrels : ∀ r ∈ rels, FreeGroup.lift f r = 1) {T : Set (FreeGroup X)}
    (hT : Subgroup.IsComplement ((FreeGroup.lift f).ker : Set (FreeGroup X)) T)
    {Y : Type*} (e : FreeGroup Y ≃* (FreeGroup.lift f).ker) :
    FreeGroup Y ⧸
        Subgroup.normalClosure
          (freeGroupPullbackRelatorSet e
            (freeKernelTransversalRelatorSet (f := f) (rels := rels) T)) ≃*
      (PresentedGroup.toGroup (rels := rels) (f := f) hrels).ker :=
  (freeGroupPullbackRelatorQuotientEquiv e
    (freeKernelTransversalRelatorSet (f := f) (rels := rels) T)).trans
      (presentedFreeKernelTransversalRelatorQuotientEquivPresentedKernel hrels hT)

/--
Membership in the free-group pullback relator set is equivalent to the displayed relator
condition.
-/
@[simp] theorem mem_freeGroupPullbackRelatorSet_iff
    {Y G : Type*} [Group G] {e : FreeGroup Y ≃* G} {S : Set G} {y : FreeGroup Y} :
    y ∈ freeGroupPullbackRelatorSet e S ↔ e y ∈ S := by
  constructor
  · rintro ⟨s, hs, hsy⟩
    have hs_eq : s = e y := by
      calc
        s = e (e.symm s) := by simp only [MulEquiv.apply_symm_apply]
        _ = e y := congrArg e hsy
    simpa [hs_eq] using hs
  · intro hy
    exact ⟨e y, hy, by simp only [MulEquiv.symm_apply_apply]⟩

/-- A conjugate of a defining relator by a transversal word belongs to the transversal relator
set. -/
theorem freeKernelTransversalRelatorSet_mem
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A}
    (hrels : ∀ r ∈ rels, FreeGroup.lift f r = 1)
    {T : Set (FreeGroup X)} {t : FreeGroup X} (ht : t ∈ T)
    {r : FreeGroup X} (hr : r ∈ rels) :
    (⟨t * r * t⁻¹, by
      change FreeGroup.lift f (t * r * t⁻¹) = 1
      simp only [map_mul, hrels r hr, mul_one, map_inv, mul_inv_cancel]⟩ : (FreeGroup.lift f).ker) ∈
        freeKernelTransversalRelatorSet (f := f) (rels := rels) T := by
  exact ⟨t, ht, r, hr, rfl⟩

/-- The inverse image of a relator belongs to its pullback relator set. -/
theorem freeGroupPullbackRelator_mem
    {Y G : Type*} [Group G] (e : FreeGroup Y ≃* G) {S : Set G} {s : G}
    (hs : s ∈ S) :
    e.symm s ∈ freeGroupPullbackRelatorSet e S := by
  exact (mem_freeGroupPullbackRelatorSet_iff (e := e) (S := S) (y := e.symm s)).2
    (by simpa using hs)

/-- A pullback of an original relator lies in the normal closure of the pulled-back relator set. -/
theorem freeGroupPullbackRelator_mem_normalClosure
    {Y G : Type*} [Group G] (e : FreeGroup Y ≃* G) {S : Set G} {s : G}
    (hs : s ∈ S) :
    e.symm s ∈ Subgroup.normalClosure (freeGroupPullbackRelatorSet e S) :=
  Subgroup.subset_normalClosure (freeGroupPullbackRelator_mem e hs)

/--
A pulled-back transversal relator lies in the normal closure of the pulled-back transversal
relator set.
-/
theorem freeGroupPullback_transversalRelator_mem_normalClosure
    {X A Y : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A}
    (hrels : ∀ r ∈ rels, FreeGroup.lift f r = 1)
    {T : Set (FreeGroup X)} (e : FreeGroup Y ≃* (FreeGroup.lift f).ker)
    {t : FreeGroup X} (ht : t ∈ T) {r : FreeGroup X} (hr : r ∈ rels) :
    e.symm
        (⟨t * r * t⁻¹, by
          change FreeGroup.lift f (t * r * t⁻¹) = 1
          simp only [map_mul, hrels r hr, mul_one, map_inv, mul_inv_cancel]⟩ : (FreeGroup.lift
              f).ker) ∈
      Subgroup.normalClosure
        (freeGroupPullbackRelatorSet e
          (freeKernelTransversalRelatorSet (f := f) (rels := rels) T)) :=
  freeGroupPullbackRelator_mem_normalClosure e
    (freeKernelTransversalRelatorSet_mem hrels ht hr)

/--
A kernel word whose image lies in the target normal closure lies in the normal closure of the
transversal relators.
-/
theorem freeKernelElement_mem_transversalRelator_normalClosure_of_mem_normalClosure
    {X A : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A}
    (hrels : ∀ r ∈ rels, FreeGroup.lift f r = 1) {T : Set (FreeGroup X)}
    (hT : Subgroup.IsComplement ((FreeGroup.lift f).ker : Set (FreeGroup X)) T)
    {k : (FreeGroup.lift f).ker}
    (hk : (k : FreeGroup X) ∈ Subgroup.normalClosure rels) :
      k ∈ Subgroup.normalClosure
        (freeKernelTransversalRelatorSet (f := f) (rels := rels) T) := by
  rw [freeKernelTransversalRelatorSet_normalClosure_eq_comap_normalClosure hrels hT]
  exact hk

/--
A pulled-back free-group word lies in the source normal closure when its image lies in the
target normal closure.
-/
theorem freeGroupPullback_mem_normalClosure_of_image_mem
    {Y G : Type*} [Group G] (e : FreeGroup Y ≃* G) (S : Set G)
    {y : FreeGroup Y} (hy : e y ∈ Subgroup.normalClosure S) :
    y ∈ Subgroup.normalClosure (freeGroupPullbackRelatorSet e S) := by
  have hyMap :
      e y ∈
        Subgroup.map e.toMonoidHom
          (Subgroup.normalClosure (freeGroupPullbackRelatorSet e S)) := by
    rw [map_normalClosure_freeGroupPullbackRelatorSet e S]
    exact hy
  rcases hyMap with ⟨z, hz, hzmap⟩
  have hzy : z = y := e.injective hzmap
  simpa [hzy] using hz

/--
A pulled-back transversal relator lies in the source normal closure whenever the original word
lies in the target normal closure.
-/
theorem freeGroupPullback_transversalRelator_mem_normalClosure_of_mem_normalClosure
    {X A Y : Type*} [Group A] {rels : Set (FreeGroup X)} {f : X → A}
    (hrels : ∀ r ∈ rels, FreeGroup.lift f r = 1) {T : Set (FreeGroup X)}
    (hT : Subgroup.IsComplement ((FreeGroup.lift f).ker : Set (FreeGroup X)) T)
    (e : FreeGroup Y ≃* (FreeGroup.lift f).ker) {k : (FreeGroup.lift f).ker}
    (hk : (k : FreeGroup X) ∈ Subgroup.normalClosure rels) :
    e.symm k ∈
        Subgroup.normalClosure
          (freeGroupPullbackRelatorSet e
            (freeKernelTransversalRelatorSet (f := f) (rels := rels) T)) := by
  have hkSchreier :
      k ∈ Subgroup.normalClosure
        (freeKernelTransversalRelatorSet (f := f) (rels := rels) T) :=
    freeKernelElement_mem_transversalRelator_normalClosure_of_mem_normalClosure hrels hT hk
  apply freeGroupPullback_mem_normalClosure_of_image_mem e
      (freeKernelTransversalRelatorSet (f := f) (rels := rels) T)
  simpa using hkSchreier

end ReidemeisterSchreier.Discrete.Presentations
