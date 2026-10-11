/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.Algebra.JacobsonRigidity
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Rigidity at a prime of an unramified domain

Maps out of an essentially finite type unramified algebra into a local ring
are determined by congruence modulo its maximal ideal. Localizing a domain
at a prime applies that criterion to endomorphisms agreeing modulo the prime. Injectivity
of the actual localization map then proves equality in the original domain.
-/

noncomputable section

namespace Algebra.FormallyUnramified

universe u v w

/-- Maps from an unramified algebra into a local ring are determined by
reduction modulo its maximal ideal. The Jacobson equality and the actual
quotient-map comparison are proved in this local-ring owner. -/
theorem algHom_ext_of_sub_mem_maximalIdeal
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [FormallyUnramified R A] [EssFiniteType R A] [IsLocalRing B]
    {f g : A →ₐ[R] B}
    (hfg : ∀ a : A, f a - g a ∈ IsLocalRing.maximalIdeal B) : f = g := by
  apply comp_injective_of_le_jacobson (R := R) (A := A) (B := B)
    (IsLocalRing.maximalIdeal B)
    (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal B) bot_ne_top).symm.le
  apply AlgHom.ext
  intro a
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) (f a) =
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) (g a)
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem
    (I := IsLocalRing.maximalIdeal B) (f a) (g a)).mpr (hfg a)

/-- An endomorphism of an unramified domain is determined by its reduction
at any prime. No finiteness or normality condition on the base is needed. -/
theorem algHom_ext_of_sub_mem_prime
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] [IsDomain S]
    [FormallyUnramified R S] [EssFiniteType R S]
    (q : Ideal S) [q.IsPrime]
    {f g : S →ₐ[R] S} (hfg : ∀ a : S, f a - g a ∈ q) : f = g := by
  let T := Localization.AtPrime q
  let ι : S →ₐ[R] T := IsScalarTower.toAlgHom R S T
  have hloc : ι.comp f = ι.comp g := by
    apply algHom_ext_of_sub_mem_maximalIdeal (R := R) (A := S) (B := T)
    intro a
    change algebraMap S T (f a) - algebraMap S T (g a) ∈ IsLocalRing.maximalIdeal T
    rw [← map_sub]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff T q (f a - g a)).mpr (hfg a)
  apply AlgHom.ext
  intro a
  apply FaithfulSMul.algebraMap_injective S T
  exact AlgHom.congr_fun hloc a

end Algebra.FormallyUnramified
