/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.IntegralClosure.PrimeAwayIntersection
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.Basic

/-!
# Gluing across two principal opens after flat base change

Two relatively prime principal localizations of a domain intersect in the
base ring when one parameter is prime. Flat tensor products preserve this
equalizer. This supplies the scalar extension step on completion overlaps;
neither normality nor Noetherianity of the tensor product is required.
-/


noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace SchemeTheory

universe u v w w'

private theorem existsUnique_tensor_pair_of_inf_eq_bot
    {R : Type u} [CommRing R] {F : Type v} [CommRing F] [Algebra R F]
    [FaithfulSMul R F] (A B : Subalgebra R F) (hAB : A ⊓ B = ⊥)
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Flat R M]
    (a : M ⊗[R] A) (b : M ⊗[R] B)
    (hab : (A.val.toLinearMap.lTensor M) a = (B.val.toLinearMap.lTensor M) b) :
    ∃! m : M, m ⊗ₜ[R] (1 : A) = a ∧ m ⊗ₜ[R] (1 : B) = b := by
  let d : R →ₗ[R] A × B := (Algebra.linearMap R A).prod (Algebra.linearMap R B)
  let e : A × B →ₗ[R] F :=
    A.val.toLinearMap.comp (LinearMap.fst R A B) -
      B.val.toLinearMap.comp (LinearMap.snd R A B)
  have hExact : Function.Exact d e := by
    intro z
    constructor
    · intro hz
      have heq : (z.1 : F) = (z.2 : F) := sub_eq_zero.mp hz
      have hmem : (z.1 : F) ∈ A ⊓ B := ⟨z.1.2, heq.symm ▸ z.2.2⟩
      rw [hAB, Algebra.mem_bot] at hmem
      obtain ⟨r, hr⟩ := hmem
      refine ⟨r, Prod.ext (Subtype.ext hr) (Subtype.ext (hr.trans heq))⟩
    · rintro ⟨r, rfl⟩
      change algebraMap R F r - algebraMap R F r = 0
      exact sub_self _
  have hd : Function.Injective d := by
    intro r s hrs
    apply FaithfulSMul.algebraMap_injective R F
    exact congrArg (fun z : A × B ↦ (z.1 : F)) hrs
  let t := TensorProduct.prodRight R R M A B
  let k : M →ₗ[R] (M ⊗[R] A) × (M ⊗[R] B) :=
    t.toLinearMap.comp ((d.lTensor M).comp (TensorProduct.rid R M).symm.toLinearMap)
  have hk (m : M) : k m = (m ⊗ₜ[R] (1 : A), m ⊗ₜ[R] (1 : B)) := by
    change (TensorProduct.prodRight R R M A B)
      (m ⊗ₜ[R] (algebraMap R A 1, algebraMap R B 1)) = _
    rw [map_one, map_one]
    exact TensorProduct.prodRight_tmul R R M A B m (1, 1)
  have hki : Function.Injective k :=
    t.injective.comp ((Module.Flat.lTensor_preserves_injective_linearMap d hd).comp
      (TensorProduct.rid R M).symm.injective)
  have he : e.lTensor M =
      ((A.val.toLinearMap.lTensor M).comp (LinearMap.fst R _ _) -
        (B.val.toLinearMap.lTensor M).comp (LinearMap.snd R _ _)).comp t.toLinearMap := by
    apply TensorProduct.ext'
    intro m z
    simp only [LinearMap.lTensor_tmul, e, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, TensorProduct.tmul_sub,
      LinearEquiv.coe_coe, t, TensorProduct.prodRight_tmul]
  let z : M ⊗[R] (A × B) := t.symm (a, b)
  have hz : e.lTensor M z = 0 := by
    rw [he]
    change (A.val.toLinearMap.lTensor M) (t z).1 -
      (B.val.toLinearMap.lTensor M) (t z).2 = 0
    rw [show t z = (a, b) from t.apply_symm_apply (a, b)]
    exact sub_eq_zero.mpr hab
  obtain ⟨u, hu⟩ := (Module.Flat.lTensor_exact M hExact z).mp hz
  have hku : k ((TensorProduct.rid R M) u) = (a, b) := by
    change t ((d.lTensor M) ((TensorProduct.rid R M).symm
      ((TensorProduct.rid R M) u))) = (a, b)
    rw [LinearEquiv.symm_apply_apply, hu]
    exact t.apply_symm_apply (a, b)
  refine ⟨(TensorProduct.rid R M) u, ?_, ?_⟩
  · rw [hk] at hku
    exact Prod.mk.inj hku
  · intro m hm
    apply hki
    rw [hk, hku, hm.1, hm.2]

/-- Compatible sections over two prime-away localizations glue uniquely
after tensoring with any flat module. -/
theorem existsUnique_tensor_primeAwayPair
    {R : Type u} [CommRing R] [IsDomain R]
    (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]
    {x y : R} (hx : Prime x) (hy : y ≠ 0) (hxy : ¬ x ∣ y)
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Flat R M]
    (a : M ⊗[R] Localization.subalgebra.ofField F (Submonoid.powers x)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hx.ne_zero)))
    (b : M ⊗[R] Localization.subalgebra.ofField F (Submonoid.powers y)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hy)))
    (hab :
      ((Localization.subalgebra.ofField F (Submonoid.powers x)
        (Submonoid.powers_le.mpr
          (mem_nonZeroDivisors_iff_ne_zero.mpr hx.ne_zero))).val.toLinearMap.lTensor M) a =
      ((Localization.subalgebra.ofField F (Submonoid.powers y)
        (Submonoid.powers_le.mpr
          (mem_nonZeroDivisors_iff_ne_zero.mpr hy))).val.toLinearMap.lTensor M) b) :
    ∃! m : M, m ⊗ₜ[R] 1 = a ∧ m ⊗ₜ[R] 1 = b := by
  apply existsUnique_tensor_pair_of_inf_eq_bot _ _ _ M a b hab
  apply le_antisymm
  · intro z hz
    exact EtaleFundamentalGroups.mem_bot_of_mem_localizationAway_pair_of_prime
      hx hy hxy z hz.1 hz.2
  · exact bot_le

section LinearMaps

variable {R : Type u} [CommRing R] [IsDomain R]
variable (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]
variable {x y : R} (hx : Prime x) (hy : y ≠ 0) (hxy : ¬ x ∣ y)

local notation "Aₓ" => Localization.subalgebra.ofField F (Submonoid.powers x)
  (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hx.ne_zero))
local notation "Aᵧ" => Localization.subalgebra.ofField F (Submonoid.powers y)
  (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hy))

include hxy in
/-- Equality can be tested on the two principal localizations. -/
theorem tensor_primeAwayPair_ext
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Flat R M]
    {m n : M} (ha : m ⊗ₜ[R] (1 : Aₓ) = n ⊗ₜ[R] (1 : Aₓ))
    (hb : m ⊗ₜ[R] (1 : Aᵧ) = n ⊗ₜ[R] (1 : Aᵧ)) : m = n := by
  have hcompat :
      ((Aₓ).val.toLinearMap.lTensor M) (n ⊗ₜ[R] (1 : Aₓ)) =
        ((Aᵧ).val.toLinearMap.lTensor M) (n ⊗ₜ[R] (1 : Aᵧ)) := by
    simp only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, map_one]
  exact (existsUnique_tensor_primeAwayPair F hx hy hxy M
    (n ⊗ₜ[R] (1 : Aₓ)) (n ⊗ₜ[R] (1 : Aᵧ)) hcompat).unique
      ⟨ha, hb⟩ ⟨rfl, rfl⟩

include hxy in
/-- Compatible local linear maps to a flat module extend uniquely. A
commuting action of another ring is preserved by the extension, so this
also applies to linear maps over a completion or a tensor overlap. -/
theorem existsUnique_linearMap_tensor_primeAwayPair
    (S : Type*) [Semiring S]
    (P : Type w') [AddCommGroup P] [Module S P]
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Flat R M]
    [Module S M] [SMulCommClass R S M]
    (fa : P →ₗ[S] M ⊗[R] Aₓ) (fb : P →ₗ[S] M ⊗[R] Aᵧ)
    (hab : ∀ p : P, ((Aₓ).val.toLinearMap.lTensor M) (fa p) =
      ((Aᵧ).val.toLinearMap.lTensor M) (fb p)) :
    ∃! f : P →ₗ[S] M, ∀ p : P,
      f p ⊗ₜ[R] 1 = fa p ∧ f p ⊗ₜ[R] 1 = fb p := by
  have hex (p : P) : ∃! m : M,
      m ⊗ₜ[R] (1 : Aₓ) = fa p ∧ m ⊗ₜ[R] (1 : Aᵧ) = fb p :=
    existsUnique_tensor_primeAwayPair F hx hy hxy M (fa p) (fb p)
      (hab p)
  choose f hf using fun p => (hex p).exists
  let g : P →ₗ[S] M :=
    { toFun := f
      map_add' := by
        intro p q
        apply (hex (p + q)).unique (hf (p + q))
        constructor
        · rw [TensorProduct.add_tmul, (hf p).1, (hf q).1, map_add]
        · rw [TensorProduct.add_tmul, (hf p).2, (hf q).2, map_add]
      map_smul' := by
        intro r p
        apply (hex (r • p)).unique (hf (r • p))
        constructor
        · rw [← TensorProduct.smul_tmul', (hf p).1, map_smul, RingHom.id_apply]
        · rw [← TensorProduct.smul_tmul', (hf p).2, map_smul, RingHom.id_apply] }
  refine ⟨g, hf, ?_⟩
  intro g' hg'
  exact LinearMap.ext fun p => (hex p).unique (hg' p) (hf p)

end LinearMaps

end SchemeTheory
