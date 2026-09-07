import ProCGroups.ProP.FinitePGroupMaximal
import Mathlib.GroupTheory.GroupAction.DomAct.Basic

set_option autoImplicit false
/-!
# Conjugation-invariant characters of finite p-groups

This file constructs nontrivial `ZMod p`-valued multiplicative characters on nontrivial normal
subgroups of finite `p`-groups.  Averaging is replaced by the fixed-point theorem for finite
`p`-group actions, so the resulting character is invariant under ambient conjugation.

The relative form additionally makes the character vanish on a prescribed proper normal
subgroup.  It is the finite quotient input for relative pro-`p` Nakayama arguments.
-/

open MulAction

namespace ClassFieldTower.ProP

noncomputable section

universe u

private theorem exists_nontrivial_character_of_finite_pGroup
    {p : Nat} [Fact p.Prime]
    {N : Type u} [Group N] [Finite N] [Nontrivial N]
    (hN : IsPGroup p N) :
    ∃ χ : N →* Multiplicative (ZMod p), χ ≠ 1 := by
  let _ : Nontrivial (Subgroup N) :=
    { exists_pair_ne :=
        ⟨(⊥ : Subgroup N), (⊤ : Subgroup N), bot_ne_top⟩ }
  obtain ⟨M, hM⟩ := IsCoatomic.exists_coatom (Subgroup N)
  let _ : M.Normal := isCoatom_normal_of_isPGroup hN hM
  let Q := HasQuotient.Quotient N M
  let _ : Nontrivial Q := quotient_nontrivial_of_isCoatom hM
  have hcard : Nat.card Q = p :=
    card_quotient_eq_prime_of_isCoatom_isPGroup hN hM
  let e : Q ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq hcard (by simp)
  let χ : N →* Multiplicative (ZMod p) :=
    e.toMonoidHom.comp (QuotientGroup.mk' M)
  refine ⟨χ, ?_⟩
  intro hχ
  have he : e.toMonoidHom = 1 := by
    ext q
    obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective M q
    change e q = 1
    rw [← hn]
    exact DFunLike.congr_fun hχ n
  obtain ⟨q, hq⟩ := exists_ne (1 : Q)
  apply hq
  apply e.injective
  rw [show e q = 1 from DFunLike.congr_fun he q]
  exact (map_one e).symm

/-- A nontrivial normal subgroup of a finite `p`-group admits a nontrivial character to
`Multiplicative (ZMod p)` that is invariant under conjugation by the ambient group. -/
theorem exists_nontrivial_conjugationInvariant_character_finite
    {p : Nat} [Fact p.Prime]
    {P : Type u} [Group P] [Finite P]
    (hP : IsPGroup p P)
    (N : Subgroup P) [N.Normal] (hN : N ≠ (⊥ : Subgroup P)) :
    ∃ χ : N →* Multiplicative (ZMod p),
      χ ≠ 1 ∧ ∀ (g : P) (n : N), χ (MulAut.conjNormal g n) = χ n := by
  let _ : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hN
  let _ : MulDistribMulAction P N :=
    MulDistribMulAction.compHom N (MulAut.conjNormal (G := P) (H := N))
  let Char := N →* Multiplicative (ZMod p)
  have hPD : IsPGroup p (DomMulAct P) := by
    intro g
    obtain ⟨k, hk⟩ := hP (DomMulAct.mk.symm g)
    refine ⟨k, ?_⟩
    apply DomMulAct.mk.symm.injective
    simpa using hk
  obtain ⟨χ₀, hχ₀⟩ :=
    exists_nontrivial_character_of_finite_pGroup (hP.to_subgroup N)
  let _ : Finite Char :=
    Finite.of_injective
      (fun χ : Char ↦ (χ : N → Multiplicative (ZMod p)))
      DFunLike.coe_injective
  let _ : Nontrivial Char :=
    { exists_pair_ne := ⟨χ₀, 1, hχ₀⟩ }
  have hCharP : IsPGroup p Char := by
    intro χ
    refine ⟨1, ?_⟩
    apply MonoidHom.ext
    intro n
    change (χ n) ^ (p ^ 1) = 1
    rw [pow_one]
    change p • (χ n).toAdd = 0
    exact ZModModule.char_nsmul_eq_zero p (χ n).toAdd
  obtain ⟨k, hkpos, hkcard⟩ :=
    hCharP.nontrivial_iff_card.mp (inferInstance : Nontrivial Char)
  have hpCard : p ∣ Nat.card Char := by
    rw [hkcard]
    exact dvd_pow_self p hkpos.ne'
  have hone : (1 : Char) ∈ fixedPoints (DomMulAct P) Char := by
    rw [mem_fixedPoints]
    intro g
    apply MonoidHom.ext
    intro n
    rfl
  obtain ⟨χ, hχFixed, hχNe⟩ :=
    hPD.exists_fixed_point_of_prime_dvd_card_of_fixed_point Char hpCard hone
  refine ⟨χ, hχNe.symm, ?_⟩
  intro g n
  have hfix := mem_fixedPoints.mp hχFixed (DomMulAct.mk g)
  exact DFunLike.congr_fun hfix n

/-- If `K < N` are normal subgroups of a finite `p`-group, there is a nontrivial ambient
conjugation-invariant character of `N` that vanishes on `K`. -/
theorem exists_conjugationInvariant_character_killing_of_lt_finite
    {p : Nat} [Fact p.Prime]
    {P : Type u} [Group P] [Finite P]
    (hP : IsPGroup p P)
    (K N : Subgroup P) [K.Normal] [N.Normal] (hKN : K < N) :
    ∃ χ : N →* Multiplicative (ZMod p),
      χ ≠ 1 ∧
        (∀ k : K, χ ⟨k, hKN.le k.2⟩ = 1) ∧
        ∀ (g : P) (n : N), χ (MulAut.conjNormal g n) = χ n := by
  let q : P →* HasQuotient.Quotient P K := QuotientGroup.mk' K
  let Nbar : Subgroup (HasQuotient.Quotient P K) := N.map q
  let _ : Nbar.Normal := Subgroup.Normal.map inferInstance q
    (QuotientGroup.mk'_surjective K)
  have hNbar : Nbar ≠ (⊥ : Subgroup (HasQuotient.Quotient P K)) := by
    intro hbot
    have hsup : K ⊔ N = K := by
      calc
        K ⊔ N = Nbar.comap q := by
          exact (QuotientGroup.comap_map_mk' K N).symm
        _ = (⊥ : Subgroup (HasQuotient.Quotient P K)).comap q := by
          rw [hbot]
        _ = K := by simp [q]
    exact hKN.2 (by rw [← hsup]; exact le_sup_right)
  have hQp : IsPGroup p (HasQuotient.Quotient P K) := hP.to_quotient K
  obtain ⟨χbar, hχbarNe, hχbarInv⟩ :=
    exists_nontrivial_conjugationInvariant_character_finite hQp Nbar hNbar
  let qN : N →* Nbar :=
    { toFun := fun n ↦ ⟨q n.1, ⟨n.1, n.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun x y ↦ Subtype.ext (map_mul q x.1 y.1) }
  have hqNsur : Function.Surjective qN := by
    intro y
    obtain ⟨x, hxN, hx⟩ := y.2
    exact ⟨⟨x, hxN⟩, Subtype.ext hx⟩
  let χ : N →* Multiplicative (ZMod p) := χbar.comp qN
  have hχNe : χ ≠ 1 := by
    intro hχ
    apply hχbarNe
    apply MonoidHom.ext
    intro y
    obtain ⟨n, hn⟩ := hqNsur y
    rw [← hn]
    exact DFunLike.congr_fun hχ n
  refine ⟨χ, hχNe, ?_, ?_⟩
  · intro k
    change χbar (qN ⟨k, hKN.le k.2⟩) = 1
    rw [show qN ⟨k, hKN.le k.2⟩ = 1 by
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := K) (x := k.1)).2 k.2]
    exact map_one χbar
  · intro g n
    change χbar (qN (MulAut.conjNormal g n)) = χbar (qN n)
    rw [show qN (MulAut.conjNormal g n) =
        MulAut.conjNormal (q g) (qN n) by
      apply Subtype.ext
      change q (g * n.1 * g⁻¹) = q g * q n.1 * (q g)⁻¹
      simp only [map_mul, map_inv]]
    exact hχbarInv (q g) (qN n)

end

end ClassFieldTower.ProP
