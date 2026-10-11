/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted from Ideal.map_stabilizer_of_surjective and Ideal.map_inertia_of_surjective:
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/Invariant/Basic.lean#L486-L532
The finite-kernel calls are replaced by the existing profinite transitivity
and quotient-action surjectivity owners, with a separate quotient scope.
-/

import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Topology.Algebra.MulAction


/-!
# Inertia images through a profinite invariant kernel

The finite invariant-kernel argument extends to a compact totally disconnected
kernel acting continuously on the discrete ring. The two substantial inputs
are the existing profinite prime-orbit theorem and the existing surjectivity
of the quotient stabilizer action. The ring and group maps remain literal.
-/

noncomputable section

open MulAction
open scoped Pointwise

namespace SchemeTheory

private theorem kernel_smulCommClass
    {R S G G' : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [Group G'] [MulSemiringAction G S] [MulSemiringAction G' R]
    (f : G →* G') (H : Subgroup G) (hH : H ≤ f.ker)
    (hf : ∀ g x, algebraMap R S (f g • x) = g • algebraMap R S x) :
    SMulCommClass H R S := by
  constructor
  intro h r s
  have hkill : f (h : G) = 1 := hH h.property
  have hfix : (h : G) • algebraMap R S r = algebraMap R S r :=
    (hf (h : G) r).symm.trans (by rw [hkill, one_smul])
  rw [Algebra.smul_def, H.smul_def, H.smul_def, Algebra.smul_def, smul_mul', hfix]

/-- A profinite invariant kernel corrects a quotient action without changing
its original base residues. Quotient rings and their one canonical scalar
action occur only in this separate proof scope. -/
private theorem exists_inertia_correction_of_profinite
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [MulSemiringAction G S]
    (H : Subgroup G) [SMulCommClass H R S] [Algebra.IsInvariant R S H]
    [TopologicalSpace H] [CompactSpace H] [TotallyDisconnectedSpace H]
    [IsTopologicalGroup H] [TopologicalSpace S] [DiscreteTopology S] [ContinuousSMul H S]
    (p : Ideal R) (q : Ideal S) [q.LiesOver p] [q.IsPrime]
    (g : stabilizer G q)
    (hg : ∀ x : R, (g : G) • algebraMap R S x - algebraMap R S x ∈ q) :
    ∃ h : H, (h : G)⁻¹ * (g : G) ∈ q.inertia G := by
  let φ : (S ⧸ q) ≃ₐ[R ⧸ p] (S ⧸ q) :=
    { toRingEquiv := (Ideal.Quotient.stabilizerHom q (q.under ℤ) G g).toRingEquiv
      commutes' x := by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        have hx := hg x
        rw [← Ideal.Quotient.eq] at hx
        change (Ideal.Quotient.stabilizerHom q (q.under ℤ) G g)
            (algebraMap (R ⧸ p) (S ⧸ q) (Ideal.Quotient.mk p x)) =
          algebraMap (R ⧸ p) (S ⧸ q) (Ideal.Quotient.mk p x)
        rw [Ideal.Quotient.algebraMap_mk_of_liesOver,
          Ideal.Quotient.stabilizerHom_apply]
        exact hx }
  obtain ⟨h, hh⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H) p q φ
  let v : stabilizer G q := ⟨(h.val : G), h.property⟩⁻¹ * g
  refine ⟨h.val, ?_⟩
  change (v : G) ∈ q.inertia G
  rw [Ideal.coe_mem_inertia, ← Ideal.Quotient.ker_stabilizerHom q (q.under ℤ) G,
    MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
  rw [AlgEquiv.ext_iff] at hh ⊢
  exact hh

section Maps

variable {R S G G' : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [Group G'] [MulSemiringAction G S] [MulSemiringAction G' R]
  (f : G →* G') (H : Subgroup G) [Algebra.IsInvariant R S H]
  [TopologicalSpace H] [CompactSpace H] [TotallyDisconnectedSpace H]
  [IsTopologicalGroup H] [TopologicalSpace S] [DiscreteTopology S] [ContinuousSMul H S]
  (p : Ideal R) (q : Ideal S) [q.LiesOver p] [q.IsPrime]

/-- A surjective equivariant group map with profinite invariant kernel
surjects on the stabilizers of the actual prime and its contraction. -/
theorem map_stabilizer_of_surjective_of_profinite
    (hf_surj : Function.Surjective f) (hf_ker : H ≤ f.ker)
    (hf : ∀ g x, algebraMap R S (f g • x) = g • algebraMap R S x) :
    (stabilizer G q).map f = stabilizer G' p := by
  have : SMulCommClass H R S := kernel_smulCommClass f H hf_ker hf
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    ext x
    rw [SetLike.mem_coe, mem_stabilizer_iff] at hg
    simp_rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, q.over_def p, Ideal.mem_under,
      ← map_inv, hf, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hg]
  · intro g hg
    obtain ⟨g, rfl⟩ := hf_surj g
    have h : (g • q).under R = q.under R := by
      ext x
      rw [Ideal.mem_under, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← hf,
        ← Ideal.mem_under, ← q.over_def p, map_inv,
        ← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hg]
    obtain ⟨g', hg'⟩ :=
      Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (G := H) (g • q) q h
    refine ⟨(g' : G) * g, ?_, ?_⟩
    · change ((g' : G) * g) • q = q
      rw [mul_smul]
      exact hg'.symm
    · rw [map_mul, show f (g' : G) = 1 from hf_ker g'.property, one_mul]

/-- The original finite invariant-kernel inertia-image theorem with a
profinite kernel. Every residue correction is supplied by the existing
profinite quotient-action surjectivity theorem; no image equality is assumed. -/
theorem map_inertia_of_surjective_of_profinite
    (hf_surj : Function.Surjective f) (hf_ker : H ≤ f.ker)
    (hf : ∀ g x, algebraMap R S (f g • x) = g • algebraMap R S x) :
    (q.inertia G).map f = p.inertia G' := by
  have hstab := (map_stabilizer_of_surjective_of_profinite f H p q hf_surj hf_ker hf).ge
  have : SMulCommClass H R S := kernel_smulCommClass f H hf_ker hf
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩ x
    change f g • x - x ∈ p
    rw [q.over_def p, Ideal.mem_under, map_sub, hf]
    exact hg (algebraMap R S x)
  · intro g hg
    obtain ⟨g, hgq, rfl⟩ := hstab (p.inertia_le_stabilizer hg)
    let s : stabilizer G q := ⟨g, hgq⟩
    have hbase : ∀ x : R, (s : G) • algebraMap R S x - algebraMap R S x ∈ q := by
      intro x
      have hx : f g • x - x ∈ p := hg x
      rw [q.over_def p, Ideal.mem_under, map_sub, hf] at hx
      exact hx
    obtain ⟨h, hh⟩ := exists_inertia_correction_of_profinite H p q s hbase
    refine ⟨(h : G)⁻¹ * (s : G), hh, ?_⟩
    change f ((h : G)⁻¹ * g) = f g
    rw [map_mul, map_inv, show f (h : G) = 1 from hf_ker h.property, inv_one, one_mul]

end Maps

end SchemeTheory
