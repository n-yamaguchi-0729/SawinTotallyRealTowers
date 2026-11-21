/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm

/-!
# Reindexing actual relative norms through coefficient homomorphisms

A proved comparison of individual coset actions determines the entire norm.
The sum is reindexed by an actual equivalence of its finite indexing types.
-/

@[expose] public section

universe u v u' v'

namespace ClassFormation

open KummerTheory CyclicCohomology
open scoped BigOperators

variable {G : Type u} [Group G] [TopologicalSpace G]
    {B S : Type*} [AddCommMonoid B] [Fintype S]

/-- A coset-action comparison identifies the actual norm with a mapped finite sum. -/
theorem relativeNorm_eq_mapped_sum (A : Rep.{v} ℤ G)
    (H J : ClosedSubgroup G) (hJH : J.toSubgroup ≤ H.toSubgroup)
    [Finite (H.toSubgroup ⧸ extensionSubgroup H J hJH)]
    (x : ambientFixedAddSubgroup A J) (i : B →+ A.V)
    (e : (H.toSubgroup ⧸ extensionSubgroup H J hJH) ≃ S) (f : S → B)
    (hf : ∀ q, relativeCosetAction A H J hJH x q = i (f (e q))) :
    (relativeNorm A H J hJH x).1 = i (∑ s, f s) := by
  let Q := H.toSubgroup ⧸ extensionSubgroup H J hJH
  let hQ : Fintype Q := Fintype.ofFinite Q
  change (∑ q : Q, relativeCosetAction A H J hJH x q) = i (∑ s, f s)
  rw [map_sum]
  exact (Finset.sum_congr rfl (fun q _ => hf q)).trans
    (e.sum_comp (fun s => i (f s)))

section Transport

variable {G' : Type u'} [Group G'] [TopologicalSpace G']
  {H J : ClosedSubgroup G} {H' J' : ClosedSubgroup G'}
  (hJH : J.toSubgroup ≤ H.toSubgroup) (hJ'H' : J'.toSubgroup ≤ H'.toSubgroup)
  (e : H.toSubgroup ≃* H'.toSubgroup)
  (he : ∀ s : H.toSubgroup, s.1 ∈ J.toSubgroup ↔ (e s).1 ∈ J'.toSubgroup)

/-- A comparison of lower groups preserving upper subgroup membership
transports their relative cosets, including for nonnormal extensions. -/
def relativeCosetEquivOfMulEquiv :
    (H.toSubgroup ⧸ extensionSubgroup H J hJH) ≃
      (H'.toSubgroup ⧸ extensionSubgroup H' J' hJ'H') :=
  Quotient.congr e.toEquiv (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    change (x⁻¹ * y).1 ∈ J.toSubgroup ↔ ((e x)⁻¹ * e y).1 ∈ J'.toSubgroup
    simpa only [map_mul, map_inv] using he (x⁻¹ * y))

/-- The relative coset comparison transports the actual automorphism representative. -/
@[simp]
theorem relativeCosetEquivOfMulEquiv_mk (x : H.toSubgroup) :
    relativeCosetEquivOfMulEquiv hJH hJ'H' e he (QuotientGroup.mk x) =
      QuotientGroup.mk (e x) :=
  rfl

/-- Equivariance over the lower groups transports the fixed coefficients of
their corresponding smaller subgroups. -/
def relativeFixedCoefficientsMap
    (A : Rep.{v} ℤ G) (A' : Rep.{v'} ℤ G')
    (f : A.V →+ A'.V)
    (hf : ∀ (s : H.toSubgroup) (a : A.V), f (A.ρ s.1 a) = A'.ρ (e s).1 (f a)) :
    ambientFixedAddSubgroup A J →+ ambientFixedAddSubgroup A' J' where
  toFun x := ⟨f x.1, by
    intro s'
    let t : H'.toSubgroup := ⟨s'.1, hJ'H' s'.2⟩
    obtain ⟨s, hs⟩ := e.surjective t
    have hsJ : s.1 ∈ J.toSubgroup := (he s).2 (hs.symm ▸ s'.2)
    have h := hf s x.1
    rw [x.2 ⟨s.1, hsJ⟩, hs] at h
    exact h.symm⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f x.1 y.1)

include he in
/-- An equivariant coefficient map commutes with relative norms when the
lower-group equivalence carries the upper subgroup to its counterpart. -/
theorem relativeNorm_map_of_equivariant
    (A : Rep.{v} ℤ G) (A' : Rep.{v'} ℤ G')
    [Finite (H.toSubgroup ⧸ extensionSubgroup H J hJH)]
    [Finite (H'.toSubgroup ⧸ extensionSubgroup H' J' hJ'H')]
    (f : A.V →+ A'.V)
    (hf : ∀ (s : H.toSubgroup) (a : A.V), f (A.ρ s.1 a) = A'.ρ (e s).1 (f a))
    (x : ambientFixedAddSubgroup A J) (x' : ambientFixedAddSubgroup A' J')
    (hx : f x.1 = x'.1) :
    f (relativeNorm A H J hJH x).1 = (relativeNorm A' H' J' hJ'H' x').1 := by
  let Q := H.toSubgroup ⧸ extensionSubgroup H J hJH
  let Q' := H'.toSubgroup ⧸ extensionSubgroup H' J' hJ'H'
  let eQ := relativeCosetEquivOfMulEquiv hJH hJ'H' e he
  let : Fintype Q := Fintype.ofFinite Q
  let : Fintype Q' := Fintype.ofFinite Q'
  change f (∑ q : Q, relativeCosetAction A H J hJH x q) =
    ∑ q : Q', relativeCosetAction A' H' J' hJ'H' x' q
  rw [map_sum]
  refine (Finset.sum_congr rfl (fun q _ => ?_)).trans
    (eQ.sum_comp (relativeCosetAction A' H' J' hJ'H' x'))
  refine Quotient.inductionOn' q ?_
  intro s
  change f (relativeCosetAction A H J hJH x (QuotientGroup.mk s)) =
    relativeCosetAction A' H' J' hJ'H' x' (QuotientGroup.mk (e s))
  rw [relativeCosetAction_mk, relativeCosetAction_mk, hf, hx]

end Transport

end ClassFormation
