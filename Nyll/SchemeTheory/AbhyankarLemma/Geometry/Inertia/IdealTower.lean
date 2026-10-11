/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic

/-!
# Ideal-theoretic inertia in a tower

This file gives the source-level inertia restriction map for a tower of
normalizations.  It is formulated for equivariant actions on a tower of
rings, so it can be instantiated by the integral closures occurring in
SGA 1, Expose X, Lemma 3.6.
-/

noncomputable section

universe uR uS uT uG uH

namespace TameAbhyankar
namespace SGA1

attribute [local instance] Ideal.Quotient.field Module.Free.of_divisionRing

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
variable {G : Type uG} {H : Type uH}
variable [Group G] [Group H]
variable [MulSemiringAction G T] [MulSemiringAction H S]

section Restriction

variable (res : G →* H)
variable (P : Ideal S) (Q : Ideal T)

/-- Restriction of ideal-theoretic inertia along an equivariant tower map. -/
def idealInertiaRestriction
    [Q.LiesOver P]
    (hres : ∀ sigma : G, ∀ x : S,
      algebraMap S T (res sigma • x) = sigma • algebraMap S T x) :
    Q.toAddSubgroup.inertia G →* P.toAddSubgroup.inertia H where
  toFun sigma := ⟨res sigma, by
    rw [AddSubgroup.mem_inertia]
    intro x
    have htop : sigma • algebraMap S T x - algebraMap S T x ∈ Q :=
      sigma.property (algebraMap S T x)
    have hmap : algebraMap S T (res sigma • x - x) ∈ Q := by
      rw [map_sub, hres]
      exact htop
    have hcomap : res sigma • x - x ∈ Q.comap (algebraMap S T) :=
      hmap
    change res sigma • x - x ∈ P
    rw [Q.over_def P, Ideal.under_def]
    exact hcomap⟩
  map_one' := by
    apply Subtype.ext
    exact res.map_one
  map_mul' sigma tau := by
    apply Subtype.ext
    exact res.map_mul sigma tau

/-- The relative inertia of the kernel of the restriction homomorphism maps
canonically into top inertia. -/
def idealRelativeInertiaInclusion :
    Q.toAddSubgroup.inertia res.ker →* Q.toAddSubgroup.inertia G where
  toFun sigma := ⟨((sigma : res.ker) : G), sigma.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The relative inertia inclusion is injective. -/
theorem idealRelativeInertiaInclusion_injective :
    Function.Injective (idealRelativeInertiaInclusion (Q := Q) res) := by
  intro sigma tau h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun rho : Q.toAddSubgroup.inertia G => (rho : G)) h

/-- In a tower, relative inertia is exactly the kernel of restriction on
inertia groups. -/
theorem idealInertiaRestriction_ker_eq_range_relative
    [Q.LiesOver P]
    (hres : ∀ sigma : G, ∀ x : S,
      algebraMap S T (res sigma • x) = sigma • algebraMap S T x) :
    MonoidHom.ker (idealInertiaRestriction res P Q hres) =
      (idealRelativeInertiaInclusion (Q := Q) res).range := by
  ext sigma
  constructor
  · intro hsigma
    have hres_sigma : res (sigma : G) = 1 := by
      have h := congrArg Subtype.val
        (MonoidHom.mem_ker.mp hsigma)
      exact h
    let sigmaKer : res.ker := ⟨sigma, hres_sigma⟩
    have hsigmaKer : sigmaKer ∈ Q.toAddSubgroup.inertia res.ker :=
      sigma.property
    exact ⟨⟨sigmaKer, hsigmaKer⟩, rfl⟩
  · rintro ⟨sigmaKer, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact sigmaKer.1.property

end Restriction

section Surjectivity

variable [IsDedekindDomain R] [IsDedekindDomain S] [IsDedekindDomain T]
variable [Module.Finite R S] [Module.Finite S T] [Module.Finite R T]
variable [Module.IsTorsionFree R S] [Module.IsTorsionFree S T]
  [Module.IsTorsionFree R T]
variable [Finite G] [Finite H]
variable (res : G →* H)
variable [IsGaloisGroup G R T] [IsGaloisGroup H R S]
  [IsGaloisGroup res.ker S T]
variable (p : Ideal R) (P : Ideal S) (Q : Ideal T)
variable [p.IsMaximal] [P.IsMaximal] [Q.IsMaximal]
variable [P.LiesOver p] [Q.LiesOver P]
variable [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)]
  [Algebra.IsSeparable (S ⧸ P) (T ⧸ Q)]

/-- For a finite Galois tower with separable residue extensions, restriction
on inertia is surjective.  The proof is the order calculation used in
SGA 1: inertia orders are ramification indices, ramification indices multiply
in the tower, and relative inertia is the kernel. -/
theorem idealInertiaRestriction_surjective
    (hp : p ≠ ⊥)
    (hres : ∀ sigma : G, ∀ x : S,
      algebraMap S T (res sigma • x) = sigma • algebraMap S T x) :
    Function.Surjective (idealInertiaRestriction res P Q hres) := by
  let : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  let : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ Q) :=
    IsScalarTower.of_algebraMap_eq <| by
      rintro ⟨x⟩
      exact congrArg _ (IsScalarTower.algebraMap_apply R S T x)
  let : Algebra.IsSeparable (R ⧸ p) (T ⧸ Q) :=
    Algebra.IsSeparable.trans (R ⧸ p) (S ⧸ P) (T ⧸ Q)
  let f := idealInertiaRestriction res P Q hres
  let i := idealRelativeInertiaInclusion (Q := Q) res
  have hP : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  have htop :
      Nat.card (Q.toAddSubgroup.inertia G) = p.ramificationIdxIn T :=
    HilbertRamification.Dedekind.dedekindRamification_inertia_card_eq_ramificationIdxIn
      p Q G hp
  have hlower :
      Nat.card (P.toAddSubgroup.inertia H) = p.ramificationIdxIn S :=
    HilbertRamification.Dedekind.dedekindRamification_inertia_card_eq_ramificationIdxIn
      p P H hp
  have hrelative :
      Nat.card (Q.toAddSubgroup.inertia res.ker) =
        P.ramificationIdxIn T :=
    HilbertRamification.Dedekind.dedekindRamification_inertia_card_eq_ramificationIdxIn
      P Q res.ker hP
  have htower :
      p.ramificationIdxIn S * P.ramificationIdxIn T =
        p.ramificationIdxIn T :=
    Ideal.ramificationIdxIn_mul_ramificationIdxIn
      P H T G res.ker
  have hker : f.ker = i.range :=
    idealInertiaRestriction_ker_eq_range_relative res P Q hres
  have hcardKer :
      Nat.card f.ker = Nat.card (Q.toAddSubgroup.inertia res.ker) := by
    rw [hker]
    exact (Nat.card_congr
      (Equiv.ofInjective i
        (idealRelativeInertiaInclusion_injective (Q := Q) res))).symm
  have hcardDomain :
      Nat.card f.ker * Nat.card f.range =
        Nat.card (Q.toAddSubgroup.inertia G) := by
    rw [← Subgroup.index_ker f]
    exact f.ker.card_mul_index
  have hcardRange :
      Nat.card f.range = Nat.card (P.toAddSubgroup.inertia H) := by
    apply Nat.eq_of_mul_eq_mul_left
      (Nat.card_pos (α := Q.toAddSubgroup.inertia res.ker))
    calc
      Nat.card (Q.toAddSubgroup.inertia res.ker) * Nat.card f.range =
          Nat.card f.ker * Nat.card f.range := by rw [hcardKer]
      _ = Nat.card (Q.toAddSubgroup.inertia G) := hcardDomain
      _ = p.ramificationIdxIn T := htop
      _ = p.ramificationIdxIn S * P.ramificationIdxIn T := htower.symm
      _ = P.ramificationIdxIn T * p.ramificationIdxIn S := Nat.mul_comm _ _
      _ = Nat.card (Q.toAddSubgroup.inertia res.ker) *
          Nat.card (P.toAddSubgroup.inertia H) := by
            rw [hrelative, hlower]
  apply MonoidHom.range_eq_top.mp
  exact Subgroup.eq_top_of_card_eq f.range hcardRange

end Surjectivity

end SGA1
end TameAbhyankar
