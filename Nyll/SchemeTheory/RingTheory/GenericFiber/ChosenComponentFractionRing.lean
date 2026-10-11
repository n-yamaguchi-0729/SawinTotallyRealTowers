/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.GenericFiber.FractionRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maximal

/-!
# A chosen generic-fibre component as a fraction field

Let `K` be a fraction field of `R`, let `U` be an `R`-algebra, and let `m`
be a maximal ideal of the generic fibre `K ⊗[R] U`.  The quotient by `m`
is canonically a fraction field of `U` modulo the contraction of `m`.

The construction keeps the specified ideal `m`: its map from the quotient
of `U` is induced by the actual quotient map on the generic fibre.  This is
the bridge needed to compare a chosen generic component with a concrete
domain factor of `U` once that contraction is identified with the kernel of
the corresponding factor map.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uU uK

variable {R : Type uR} {U : Type uU} {K : Type uK}
variable [CommRing R] [CommRing U] [Algebra R U]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- The contraction to `U` of a chosen ideal in the generic fibre. -/
def genericFiberComponentBaseIdeal
    (m : Ideal (K ⊗[R] U)) : Ideal U :=
  m.comap
    (Algebra.TensorProduct.includeRight : U →ₐ[R] K ⊗[R] U).toRingHom

/-- The canonical map from the quotient by the contracted ideal to the
chosen generic-fibre quotient. -/
def genericFiberComponentQuotientRingHom
    (m : Ideal (K ⊗[R] U)) :
    (U ⧸ (genericFiberComponentBaseIdeal m)) →+* ((K ⊗[R] U) ⧸ m) :=
  Ideal.quotientMap m
    (Algebra.TensorProduct.includeRight : U →ₐ[R] K ⊗[R] U).toRingHom
    le_rfl

omit [IsFractionRing R K] in
@[simp]
theorem genericFiberComponentQuotientRingHom_mk
    (m : Ideal (K ⊗[R] U)) (x : U) :
    genericFiberComponentQuotientRingHom m
        (Ideal.Quotient.mk (genericFiberComponentBaseIdeal m) x) =
      Ideal.Quotient.mk m
        ((Algebra.TensorProduct.includeRight : U →ₐ[R] K ⊗[R] U) x) := by
  exact Ideal.quotientMap_mk
    (J := genericFiberComponentBaseIdeal m) (I := m) (x := x)

omit [IsFractionRing R K] in
/-- The canonical map from the contracted quotient is injective. -/
theorem genericFiberComponentQuotientRingHom_injective
    (m : Ideal (K ⊗[R] U)) :
    Function.Injective (genericFiberComponentQuotientRingHom m) := by
  exact Ideal.quotientMap_injective

/-- A field component selected by a maximal generic-fibre ideal is a
fraction field of the quotient by its contraction to the original algebra.

This is produced directly from the localization presentation
`K ⊗[R] U`: denominators are images of non-zero elements of `R`, and no
such denominator can lie in the contraction of a proper ideal upstairs. -/
theorem genericFiberComponentQuotient_isFractionRing
    (m : Ideal (K ⊗[R] U)) [m.IsMaximal] :
    let N := genericFiberComponentBaseIdeal m
    let Ω := ((K ⊗[R] U) ⧸ m)
    letI : Algebra (U ⧸ N) Ω :=
      (genericFiberComponentQuotientRingHom m).toAlgebra
    IsFractionRing (U ⧸ N) Ω := by
  let G := K ⊗[R] U
  let N := genericFiberComponentBaseIdeal m
  let Ω := G ⧸ m
  let M : Submonoid U :=
    Algebra.algebraMapSubmonoid U (nonZeroDivisors R)
  let : Algebra U G := Algebra.TensorProduct.rightAlgebra
  let : IsLocalization M G :=
    IsLocalization.tensorRight (R := R) (S := U) (A := K)
      (nonZeroDivisors R)
  let : m.IsPrime :=
    Ideal.IsMaximal.isPrime (inferInstance : m.IsMaximal)
  let : N.IsPrime := (inferInstance : m.IsPrime).comap
    (Algebra.TensorProduct.includeRight : U →ₐ[R] G).toRingHom
  let : Field Ω := Ideal.Quotient.field m
  let : Algebra (U ⧸ N) Ω :=
    (genericFiberComponentQuotientRingHom m).toAlgebra
  let : FaithfulSMul (U ⧸ N) Ω :=
    (faithfulSMul_iff_algebraMap_injective (U ⧸ N) Ω).mpr
      (genericFiberComponentQuotientRingHom_injective m)
  have hdisjoint : Disjoint (M : Set U) (N : Set U) := by
    rw [Set.disjoint_left]
    intro x hxM hxN
    have hxIdeal : algebraMap U G x ∈ m := hxN
    exact (inferInstance : m.IsPrime).ne_top
      (Ideal.eq_top_of_isUnit_mem m hxIdeal
        (IsLocalization.map_units G ⟨x, hxM⟩))
  apply IsFractionRing.of_field
  intro z
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨⟨x, s⟩, ht⟩ := IsLocalization.surj M t
  refine ⟨Ideal.Quotient.mk N x, Ideal.Quotient.mk N s, ?_⟩
  refine (eq_div_iff ?_).2 ?_
  · apply (map_ne_zero_iff _
      (FaithfulSMul.algebraMap_injective (U ⧸ N) Ω)).2
    intro hs
    have hsN : (s : U) ∈ N := Ideal.Quotient.eq_zero_iff_mem.mp hs
    exact (Set.disjoint_left.mp hdisjoint) s.property hsN
  · change Ideal.Quotient.mk m t * algebraMap U Ω s =
      algebraMap U Ω x
    simpa using congrArg (Ideal.Quotient.mk m) ht

/-- The canonical identification of a chosen generic-fibre component with
the fraction ring of the quotient by its contracted prime. -/
noncomputable def genericFiberComponentFractionRingEquiv
    (m : Ideal (K ⊗[R] U)) [m.IsMaximal] :
    ((K ⊗[R] U) ⧸ m) ≃+*
      FractionRing (U ⧸ genericFiberComponentBaseIdeal m) := by
  let G := K ⊗[R] U
  let N := genericFiberComponentBaseIdeal m
  let Ω := G ⧸ m
  letI : m.IsPrime :=
    Ideal.IsMaximal.isPrime (inferInstance : m.IsMaximal)
  letI : N.IsPrime := (inferInstance : m.IsPrime).comap
    (Algebra.TensorProduct.includeRight : U →ₐ[R] G).toRingHom
  letI : Field Ω := Ideal.Quotient.field m
  letI : Algebra (U ⧸ N) Ω :=
    (genericFiberComponentQuotientRingHom m).toAlgebra
  letI : IsFractionRing (U ⧸ N) Ω :=
    genericFiberComponentQuotient_isFractionRing m
  exact (FractionRing.algEquiv (A := U ⧸ N) Ω).symm.toRingEquiv

@[simp]
theorem genericFiberComponentFractionRingEquiv_quotient_mk
    (m : Ideal (K ⊗[R] U)) [m.IsMaximal] (x : U) :
    genericFiberComponentFractionRingEquiv m
        (genericFiberComponentQuotientRingHom m
          (Ideal.Quotient.mk (genericFiberComponentBaseIdeal m) x)) =
      algebraMap (U ⧸ genericFiberComponentBaseIdeal m)
        (FractionRing (U ⧸ genericFiberComponentBaseIdeal m))
        (Ideal.Quotient.mk (genericFiberComponentBaseIdeal m) x) := by
  let G := K ⊗[R] U
  let N := genericFiberComponentBaseIdeal m
  let Ω := G ⧸ m
  let : m.IsPrime :=
    Ideal.IsMaximal.isPrime (inferInstance : m.IsMaximal)
  let : N.IsPrime := (inferInstance : m.IsPrime).comap
    (Algebra.TensorProduct.includeRight : U →ₐ[R] G).toRingHom
  let : Field Ω := Ideal.Quotient.field m
  let : Algebra (U ⧸ N) Ω :=
    (genericFiberComponentQuotientRingHom m).toAlgebra
  let : IsFractionRing (U ⧸ N) Ω :=
    genericFiberComponentQuotient_isFractionRing m
  change (FractionRing.algEquiv (A := U ⧸ N) Ω).symm
      (algebraMap (U ⧸ N) Ω (Ideal.Quotient.mk N x)) =
    algebraMap (U ⧸ N) (FractionRing (U ⧸ N))
      (Ideal.Quotient.mk N x)
  simp

end EtaleFundamentalGroups

end
