/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ProjSpaceCech_GradedModule_Presentation_ker_isFG.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule

/-!
Finite generation of the kernel of a graded module presentation over a noetherian base.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_GradedModule_Presentation_ker_isFG

universe u

noncomputable section

open Finset Function MvPolynomial

namespace ProjSpaceCech
open _root_.ProjSpaceCech
open _root_.ProjSpaceCech

section KerFG

variable {R : Type u} [CommRing R] {n : ℕ} {D : GradedModule R n}
variable (σ : GradedModule.Presentation D)

local notation "S" => MvPolynomial (Fin (n + 1)) R

namespace GradedModule
open _root_.ProjSpaceCech.GradedModule
end GradedModule
open scoped _root_.ProjSpaceCech.GradedModule in
scoped instance GradedModule.F_module : Module S σ.F.M :=
  inferInstanceAs (Module S (σ.J → S))

open scoped _root_.ProjSpaceCech.GradedModule in
scoped instance GradedModule.F_scalarTower : IsScalarTower R S σ.F.M :=
  inferInstanceAs (IsScalarTower R S (σ.J → S))

open scoped _root_.ProjSpaceCech.GradedModule in
scoped instance GradedModule.FD_module (d : ℤ) : Module S (GradedModule.FD R n d).M :=
  inferInstanceAs (Module S S)

open scoped _root_.ProjSpaceCech.GradedModule in
scoped instance GradedModule.ker_module : Module S σ.ker.M :=
  GradedModule.F_module σ

open scoped _root_.ProjSpaceCech.GradedModule in
theorem GradedModule.F_xMul_eq_smul (j : Fin (n + 1)) (m : σ.F.M) :
    σ.F.xMul j m = (X j : S) • m := by
  funext k; rfl

open scoped _root_.ProjSpaceCech.GradedModule in
/-- The sum of the homogeneous components of the presentation kernel. -/
abbrev GradedModule.Kgr : Submodule R σ.F.M :=
  ⨆ d : ℤ, σ.F.grade d ⊓ σ.K

open scoped _root_.ProjSpaceCech.GradedModule in
theorem GradedModule.Kgr_xMul_stable (j : Fin (n + 1)) :
    ∀ m ∈ GradedModule.Kgr σ, σ.F.xMul j m ∈ GradedModule.Kgr σ := by
  have hmap : (GradedModule.Kgr σ).map (σ.F.xMul j) ≤ GradedModule.Kgr σ := by
    rw [GradedModule.Kgr, Submodule.map_iSup]
    refine iSup_le fun d => le_trans ?_ (le_iSup _ (d + 1))
    rintro _ ⟨m, ⟨hg, hK⟩, rfl⟩
    exact ⟨σ.F.xMul_mem_grade j d m hg, GradedModule.Presentation.K_xMul_stable σ j m hK⟩
  intro m hm; exact hmap ⟨m, hm, rfl⟩

open scoped _root_.ProjSpaceCech.GradedModule in
/-- The homogeneous presentation kernel as a submodule over the polynomial ring. -/
def GradedModule.KgrS : Submodule S σ.F.M where
  carrier := GradedModule.Kgr σ
  add_mem' := Submodule.add_mem _
  zero_mem' := Submodule.zero_mem _
  smul_mem' := fun p m hm => by
    induction p using MvPolynomial.induction_on with
    | C r =>
      have : (C r : S) • m = r • m := by
        funext k; exact MvPolynomial.C_mul'
      rw [this]; exact Submodule.smul_mem _ r hm
    | add p q hp hq =>
      rw [add_smul]; exact Submodule.add_mem _ hp hq
    | mul_X p j hp =>
      rw [mul_comm, mul_smul, ← GradedModule.F_xMul_eq_smul σ j]
      exact GradedModule.Kgr_xMul_stable σ j _ hp

open scoped _root_.ProjSpaceCech.GradedModule in
theorem GradedModule.mem_F_grade (d : ℤ) (m : σ.F.M) :
    m ∈ σ.F.grade d ↔ ∀ k, m k ∈ GradedModule.freeGrade R n (d + σ.d₀ k) := by
  exact ⟨fun h k => h k (Set.mem_univ k), fun h k _ => h k⟩

open scoped _root_.ProjSpaceCech.GradedModule in
theorem GradedModule.K_smul_stable (c : S) : ∀ m ∈ σ.K, c • m ∈ σ.K := by
  intro m hm
  induction c using MvPolynomial.induction_on with
  | C r =>
    have : (C r : S) • m = r • m := funext fun k => MvPolynomial.C_mul'
    rw [this]; exact Submodule.smul_mem _ r hm
  | add p q hp hq => rw [add_smul]; exact Submodule.add_mem _ hp hq
  | mul_X p j hp =>
    rw [mul_comm, mul_smul, ← GradedModule.F_xMul_eq_smul σ j]
    exact GradedModule.Presentation.K_xMul_stable σ j _ hp

open scoped _root_.ProjSpaceCech.GradedModule in
theorem GradedModule.freeGrade_smul_mem_grade {a e : ℤ} {c : S}
    (hc : c ∈ GradedModule.freeGrade R n a) {m : σ.F.M} (hm : m ∈ σ.F.grade e) :
    c • m ∈ σ.F.grade (e + a) := by
  rcases le_or_gt 0 a with ha | ha
  · rw [GradedModule.freeGrade_of_nonneg R n ha, mem_homogeneousSubmodule] at hc
    rw [GradedModule.mem_F_grade]
    intro k
    have hmk := (GradedModule.mem_F_grade σ e m).mp hm k
    have hsmul : (c • m) k = c • m k := rfl
    rcases le_or_gt 0 (e + σ.d₀ k) with he | he
    · rw [GradedModule.freeGrade_of_nonneg R n he] at hmk
      have hmk' : (m k).IsHomogeneous (e + σ.d₀ k).toNat := hmk
      rw [GradedModule.freeGrade_of_nonneg R n (by linarith : (0:ℤ) ≤ e + a + σ.d₀ k)]
      have hgoal : (c • m k).IsHomogeneous (a.toNat + (e + σ.d₀ k).toNat) := hc.mul hmk'
      rw [show (e + a + σ.d₀ k).toNat = a.toNat + (e + σ.d₀ k).toNat from by omega]
      exact hsmul ▸ hgoal
    · have hmk0 : m k = (0 : (GradedModule.FD R n (σ.d₀ k)).M) := by
        have hbot : GradedModule.freeGrade R n (e + σ.d₀ k) = ⊥ := by
          simp [GradedModule.freeGrade, not_le.mpr he]
        exact (hbot ▸ hmk : m k ∈ (⊥ : Submodule R S))
      rw [hsmul, hmk0, smul_zero]; exact Submodule.zero_mem _
  · simp only [GradedModule.freeGrade, not_le.mpr ha, ite_false, Submodule.mem_bot] at hc
    rw [hc, zero_smul]; exact Submodule.zero_mem _

open scoped _root_.ProjSpaceCech.GradedModule in
/-- The linear projection to the indicated integer grade of the shifted free presentation source. -/
def GradedModule.FProj (d : ℤ) : σ.F.M →ₗ[R] σ.F.M where
  toFun m k := if 0 ≤ d + σ.d₀ k then
    (homogeneousComponent (d + σ.d₀ k).toNat (m k) :
      (GradedModule.FD R n (σ.d₀ k)).M) else 0
  map_add' m₁ m₂ := funext fun k => by
    by_cases h : 0 ≤ d + σ.d₀ k
    · exact (ite_eq_left h).trans ((map_add _ _ _).trans
        (congrArg₂ (· + ·) (ite_eq_left h).symm (ite_eq_left h).symm))
    · exact (ite_eq_right h).trans
        ((zero_add 0).symm.trans (congrArg₂ (· + ·) (ite_eq_right h).symm (ite_eq_right h).symm))
  map_smul' r m := funext fun k => by
    by_cases h : 0 ≤ d + σ.d₀ k
    · exact (ite_eq_left h).trans ((map_smul _ _ _).trans (congrArg (r • ·) (ite_eq_left h).symm))
    · exact (ite_eq_right h).trans ((smul_zero r).symm.trans (congrArg (r • ·) (ite_eq_right
      h).symm))

open scoped _root_.ProjSpaceCech.GradedModule in
theorem GradedModule.FProj_apply (d : ℤ) (m : σ.F.M) (k : σ.J) :
    GradedModule.FProj σ d m k
      = if 0 ≤ d + σ.d₀ k then
          (homogeneousComponent (d + σ.d₀ k).toNat (m k) :
            (GradedModule.FD R n (σ.d₀ k)).M) else 0 := by
  rfl

open scoped _root_.ProjSpaceCech.GradedModule in
theorem GradedModule.FProj_apply_of_mem_grade (d e : ℤ) {m : σ.F.M}
    (hm : m ∈ σ.F.grade e) :
    GradedModule.FProj σ d m = if d = e then m else 0 := by
  funext k
  rw [GradedModule.FProj_apply]
  have hmk := (GradedModule.mem_F_grade σ e m).mp hm k
  by_cases hd : 0 ≤ d + σ.d₀ k
  · rw [ite_eq_left hd]
    by_cases he : 0 ≤ e + σ.d₀ k
    · rw [GradedModule.freeGrade_of_nonneg R n he] at hmk
      rw [homogeneousComponent_of_mem hmk]
      by_cases hde : d = e
      · erw [ite_eq_left (show (d + σ.d₀ k).toNat = (e + σ.d₀ k).toNat from
        by omega), ite_eq_left hde]
      · erw [ite_eq_right (show (d + σ.d₀ k).toNat ≠ (e + σ.d₀ k).toNat from fun h => hde (
        by omega)),
          ite_eq_right hde]; rfl
    · have hmk0 : m k = 0 := by
        simp only [GradedModule.freeGrade, he, ite_false] at hmk
        exact hmk
      rw [hmk0, ite_eq_right (show d ≠ e from fun h => he (h ▸ hd))]
      exact map_zero _
  · rw [ite_eq_right hd]
    by_cases hde : d = e
    · subst hde
      have hmk0 : m k = 0 := by
        simp only [GradedModule.freeGrade, hd, ite_false] at hmk
        exact hmk
      rw [ite_eq_left rfl]; exact hmk0.symm
    · rw [ite_eq_right hde]; rfl

namespace GradedModule
open _root_.ProjSpaceCech.GradedModule
namespace Presentation
open _root_.ProjSpaceCech.GradedModule.Presentation
end Presentation
end GradedModule
open scoped _root_.ProjSpaceCech.GradedModule _root_.ProjSpaceCech.GradedModule.Presentation in
theorem GradedModule.Presentation.ker_isFG' [IsNoetherianRing R] : GradedModule.IsFG σ.ker := by
  classical
  have : IsNoetherianRing S := MvPolynomial.isNoetherianRing
  have : IsNoetherian S σ.F.M := inferInstanceAs (IsNoetherian S (σ.J → S))
  obtain ⟨N, gen, hgen⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (IsNoetherian.noetherian (GradedModule.KgrS σ))
  have hdec : ∀ i : Fin N, ∃ p : ℤ →₀ σ.F.M,
      (∀ d, p d ∈ σ.F.grade d ⊓ σ.K) ∧ (p.sum fun _ x => x) = gen i := by
    intro i
    have hgm : gen i ∈ GradedModule.Kgr σ :=
      (hgen ▸ Submodule.subset_span (Set.mem_range_self i) :
        gen i ∈ (GradedModule.KgrS σ : Set σ.F.M))
    obtain ⟨p, hp, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hgm
    refine ⟨p, fun d => ?_, hsum⟩
    by_cases hd : d ∈ p.support
    · exact hp d
    · rw [Finsupp.notMem_support_iff.mp hd]; exact Submodule.zero_mem _
  choose pc hpc_mem hpc_sum using hdec
  let T : Type := Σ i : Fin N, (pc i).support
  let de : T → ℤ := fun t => (t.2 : ℤ)
  let pv : T → σ.F.M := fun t => pc t.1 t.2
  have hpv : ∀ t, pv t ∈ σ.F.grade (de t) ⊓ σ.K := fun t => hpc_mem t.1 (de t)
  have hgen_eq : ∀ i : Fin N, gen i = ∑ d ∈ (pc i).support, pc i d := fun i =>
    (hpc_sum i).symm.trans (Finsupp.sum_of_support_subset _ subset_rfl _ fun _ _ => rfl)
  let toS : (GradedModule.pi fun k => GradedModule.FD R n (-de k)).M → (T → S) :=
    fun f => f
  let homL : (GradedModule.pi fun k => GradedModule.FD R n (-de k)).M →ₗ[R] σ.F.M :=
    { toFun := fun f => ∑ t : T, toS f t • pv t
      map_add' := fun f g => by
        have h : ∀ t, toS (f + g) t = toS f t + toS g t := fun t => rfl
        simp only [h, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r f => by
        have h : ∀ t, toS (r • f) t = r • toS f t := fun t => rfl
        simp only [h, smul_assoc, ← Finset.smul_sum, RingHom.id_apply] }
  refine ⟨{
    J := T
    fJ := inferInstance
    d₀ := fun t => -de t
    hom := {
      toLinearMap := homL
      mem_grade := ?_
      xMul_comm := ?_ }
    surj := ?_ }⟩
  · intro d f hf
    change (∑ t : T, toS f t • pv t) ∈ σ.ker.grade d
    refine Submodule.sum_mem _ fun t _ => ?_
    have hft : toS f t ∈ GradedModule.freeGrade R n (d - de t) := by
      have := hf t (Set.mem_univ t)
      simp only at this
      exact this
    refine ⟨?_, GradedModule.K_smul_stable σ _ _ (hpv t).2⟩
    have := GradedModule.freeGrade_smul_mem_grade σ hft (hpv t).1
    simp only [show de t + (d - de t) = d from by ring] at this
    exact this
  · intro j
    refine LinearMap.ext fun f => ?_
    have hxm : ∀ t, toS ((GradedModule.pi
        fun k => GradedModule.FD R n (-de k)).xMul j f) t = (X j : S) * toS f t :=
      fun t => rfl
    change (∑ t : T, toS (_) t • pv t) = σ.F.xMul j (∑ t : T, toS f t • pv t)
    simp only [hxm, GradedModule.F_xMul_eq_smul σ j, Finset.smul_sum]
    exact Finset.sum_congr rfl fun t _ => mul_smul (X j) (toS f t) (pv t)
  · intro d m hm
    have hmS : m ∈ Submodule.span S (Set.range gen) :=
      hgen ▸ (le_iSup (fun e => σ.F.grade e ⊓ σ.K) d hm :
        m ∈ (GradedModule.KgrS σ : Set σ.F.M))
    obtain ⟨c, hc_eq⟩ :=
      (Submodule.mem_span_range_iff_exists_fun (R := S) (M := σ.F.M) (v := gen)).mp hmS
    have hmT : m = ∑ t : T, c t.1 • pv t := by
      have hsig : (∑ t : T, c t.1 • pv t : σ.F.M)
          = ∑ i : Fin N, ∑ e ∈ (pc i).support, c i • pc i e := by
        have hT : (Finset.univ : Finset T)
            = (Finset.univ : Finset (Fin N)).sigma (fun _ => Finset.univ) :=
          Finset.univ_sigma_univ.symm
        rw [hT, Finset.sum_sigma]
        exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_attach (pc i).support (fun e => c i • pc i e)
      rw [hsig, ← hc_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hgen_eq i, Finset.smul_sum]
    have hmT' : m = ∑ t : T, ∑ a ∈ Finset.range ((c t.1).totalDegree + 1),
        homogeneousComponent a (c t.1) • pv t := by
      simp only [← Finset.sum_smul, sum_homogeneousComponent, ← hmT]
    have hproj : m = ∑ t : T,
        (if 0 ≤ d - de t then homogeneousComponent (d - de t).toNat (c t.1) else 0) • pv t := by
      have h1 := (GradedModule.FProj_apply_of_mem_grade σ d d hm.1).trans (ite_eq_left rfl)
      rw [← h1, hmT', map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_sum]
      have hstep : ∀ a : ℕ, GradedModule.FProj σ d
          (homogeneousComponent a (c t.1) • pv t)
          = if d = de t + a then homogeneousComponent a (c t.1) • pv t else 0 := by
        intro a
        refine GradedModule.FProj_apply_of_mem_grade σ d (de t + a)
          (GradedModule.freeGrade_smul_mem_grade σ (a := (a : ℤ)) ?_ (hpv t).1)
        rw [GradedModule.freeGrade_of_nonneg R n (by exact_mod_cast Nat.zero_le a),
          show ((a : ℤ)).toNat = a from by omega, mem_homogeneousSubmodule]
        exact homogeneousComponent_isHomogeneous a (c t.1)
      simp only [hstep]
      rcases le_or_gt 0 (d - de t) with hdt | hdt
      · rw [ite_eq_left hdt]
        rcases lt_or_ge (d - de t).toNat ((c t.1).totalDegree + 1) with hlt | hge
        · rw [Finset.sum_eq_single (d - de t).toNat
            (fun a _ ha => ite_eq_right (fun h => ha (by omega)))
            (fun hnm => absurd (Finset.mem_range.mpr hlt) hnm),
            ite_eq_left (by omega)]
        · have hzero : homogeneousComponent (d - de t).toNat (c t.1) = 0 :=
            homogeneousComponent_eq_zero _ _ hge
          rw [hzero, zero_smul,
            Finset.sum_eq_zero fun a ha => ite_eq_right (fun h => by
              have := Finset.mem_range.mp ha; omega)]
      · rw [ite_eq_right (not_le.mpr hdt), zero_smul,
          Finset.sum_eq_zero fun a _ => ite_eq_right (fun h => by omega)]
    have hwit : ∀ t : T, (if 0 ≤ d - de t then homogeneousComponent (d - de t).toNat (c t.1) else 0)
        ∈ GradedModule.freeGrade R n (d - de t) := by
      intro t
      split_ifs with hdt
      · rw [GradedModule.freeGrade_of_nonneg R n hdt, mem_homogeneousSubmodule]
        exact homogeneousComponent_isHomogeneous _ _
      · exact Submodule.zero_mem _
    refine ⟨(fun t => if 0 ≤ d - de t then homogeneousComponent (d - de t).toNat (c t.1) else 0 :
        T → S), fun t _ => ?_, hproj.symm⟩
    have := hwit t
    simp only at this ⊢
    exact this

end KerFG

end ProjSpaceCech

theorem _root_.ProjSpaceCech.GradedModule.Presentation.ker_isFG {R : Type u} [CommRing R]
    [IsNoetherianRing R] {n : ℕ} {D : ProjSpaceCech.GradedModule R n}
    (σ : ProjSpaceCech.GradedModule.Presentation D) : ProjSpaceCech.GradedModule.IsFG σ.ker :=
  ProjSpaceCech.GradedModule.Presentation.ker_isFG' σ

end
end AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_GradedModule_Presentation_ker_isFG
end ProofImplementation
