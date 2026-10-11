/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Descent.PrimeAwayPairGluing
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Extending algebra maps across a pair of principal opens

Flat Hartogs extension preserves the multiplicative structure: the algebra
identities can be checked after the two principal localizations. These are
the maps used to extend the actual completion-overlap isomorphism.
-/

noncomputable section

namespace SchemeTheory

open scoped TensorProduct nonZeroDivisors

universe u v w w'

variable {R : Type u} [CommRing R] [IsDomain R]
variable (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]
variable {x y : R} (hx : Prime x) (hy : y ≠ 0) (hxy : ¬ x ∣ y)

local notation "Aₓ" => Localization.subalgebra.ofField F (Submonoid.powers x)
  (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hx.ne_zero))
local notation "Aᵧ" => Localization.subalgebra.ofField F (Submonoid.powers y)
  (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hy))

include hxy in
/-- Compatible local algebra maps to a flat algebra extend uniquely. -/
theorem existsUnique_algHom_tensor_primeAwayPair
    (S : Type*) [CommRing S]
    (P : Type w') [CommRing P] [Algebra S P]
    (M : Type w) [CommRing M] [Algebra R M] [Module.Flat R M]
    [Algebra S M] [SMulCommClass R S M]
    (fa : P →ₐ[S] M ⊗[R] Aₓ) (fb : P →ₐ[S] M ⊗[R] Aᵧ)
    (hab : ∀ p : P, ((Aₓ).val.toLinearMap.lTensor M) (fa p) =
      ((Aᵧ).val.toLinearMap.lTensor M) (fb p)) :
    ∃! f : P →ₐ[S] M, ∀ p : P,
      f p ⊗ₜ[R] 1 = fa p ∧ f p ⊗ₜ[R] 1 = fb p := by
  obtain ⟨g, hg, _⟩ := existsUnique_linearMap_tensor_primeAwayPair F hx hy hxy
    S P M fa.toLinearMap fb.toLinearMap hab
  let ix : M →ₐ[S] M ⊗[R] Aₓ := Algebra.TensorProduct.includeLeft
  let iy : M →ₐ[S] M ⊗[R] Aᵧ := Algebra.TensorProduct.includeLeft
  have hone : g 1 = 1 := by
    apply tensor_primeAwayPair_ext F hx hy hxy M
    · exact (hg 1).1.trans ((map_one fa).trans (map_one ix).symm)
    · exact (hg 1).2.trans ((map_one fb).trans (map_one iy).symm)
  have hmul (p q : P) : g (p * q) = g p * g q := by
    apply tensor_primeAwayPair_ext F hx hy hxy M
    · calc
        ix (g (p * q)) = fa (p * q) := (hg (p * q)).1
        _ = fa p * fa q := map_mul fa p q
        _ = ix (g p) * ix (g q) :=
          congrArg₂ (· * ·) (hg p).1.symm (hg q).1.symm
        _ = ix (g p * g q) := (map_mul ix (g p) (g q)).symm
    · calc
        iy (g (p * q)) = fb (p * q) := (hg (p * q)).2
        _ = fb p * fb q := map_mul fb p q
        _ = iy (g p) * iy (g q) :=
          congrArg₂ (· * ·) (hg p).2.symm (hg q).2.symm
        _ = iy (g p * g q) := (map_mul iy (g p) (g q)).symm
  refine ⟨AlgHom.ofLinearMap g hone hmul, hg, ?_⟩
  intro f hf
  apply AlgHom.ext
  intro p
  exact tensor_primeAwayPair_ext F hx hy hxy M
    ((hf p).1.trans (hg p).1.symm) ((hf p).2.trans (hg p).2.symm)

include hxy in
/-- A compatible pair of local algebra isomorphisms extends to an actual
algebra isomorphism. Both directions are constructed by flat Hartogs extension. -/
theorem exists_algEquiv_tensor_primeAwayPair
    (S : Type*) [CommRing S]
    (P : Type w') [CommRing P] [Algebra R P] [Algebra S P]
    [SMulCommClass R S P] [Module.Flat R P]
    (M : Type w) [CommRing M] [Algebra R M] [Algebra S M]
    [SMulCommClass R S M] [Module.Flat R M]
    (ea : P ⊗[R] Aₓ ≃ₐ[S] M ⊗[R] Aₓ)
    (eb : P ⊗[R] Aᵧ ≃ₐ[S] M ⊗[R] Aᵧ)
    (hab : ∀ p : P,
      ((Aₓ).val.toLinearMap.lTensor M) (ea (p ⊗ₜ[R] 1)) =
        ((Aᵧ).val.toLinearMap.lTensor M) (eb (p ⊗ₜ[R] 1)))
    (hba : ∀ m : M,
      ((Aₓ).val.toLinearMap.lTensor P) (ea.symm (m ⊗ₜ[R] 1)) =
        ((Aᵧ).val.toLinearMap.lTensor P) (eb.symm (m ⊗ₜ[R] 1))) :
    ∃ e : P ≃ₐ[S] M,
      (∀ p : P, e p ⊗ₜ[R] 1 = ea (p ⊗ₜ[R] 1) ∧
        e p ⊗ₜ[R] 1 = eb (p ⊗ₜ[R] 1)) ∧
      (∀ m : M, e.symm m ⊗ₜ[R] 1 = ea.symm (m ⊗ₜ[R] 1) ∧
        e.symm m ⊗ₜ[R] 1 = eb.symm (m ⊗ₜ[R] 1)) := by
  obtain ⟨f, hf, _⟩ := existsUnique_algHom_tensor_primeAwayPair F hx hy hxy S P M
    (ea.toAlgHom.comp Algebra.TensorProduct.includeLeft)
    (eb.toAlgHom.comp Algebra.TensorProduct.includeLeft) hab
  obtain ⟨g, hg, _⟩ := existsUnique_algHom_tensor_primeAwayPair F hx hy hxy S M P
    (ea.symm.toAlgHom.comp Algebra.TensorProduct.includeLeft)
    (eb.symm.toAlgHom.comp Algebra.TensorProduct.includeLeft) hba
  have hfg : f.comp g = AlgHom.id S M := by
    apply AlgHom.ext
    intro m
    apply tensor_primeAwayPair_ext F hx hy hxy M
    · calc
        f (g m) ⊗ₜ[R] (1 : Aₓ) = ea (g m ⊗ₜ[R] 1) := (hf (g m)).1
        _ = ea (ea.symm (m ⊗ₜ[R] 1)) := congrArg ea (hg m).1
        _ = m ⊗ₜ[R] 1 := ea.apply_symm_apply _
    · calc
        f (g m) ⊗ₜ[R] (1 : Aᵧ) = eb (g m ⊗ₜ[R] 1) := (hf (g m)).2
        _ = eb (eb.symm (m ⊗ₜ[R] 1)) := congrArg eb (hg m).2
        _ = m ⊗ₜ[R] 1 := eb.apply_symm_apply _
  have hgf : g.comp f = AlgHom.id S P := by
    apply AlgHom.ext
    intro p
    apply tensor_primeAwayPair_ext F hx hy hxy P
    · calc
        g (f p) ⊗ₜ[R] (1 : Aₓ) = ea.symm (f p ⊗ₜ[R] 1) := (hg (f p)).1
        _ = ea.symm (ea (p ⊗ₜ[R] 1)) := congrArg ea.symm (hf p).1
        _ = p ⊗ₜ[R] 1 := ea.symm_apply_apply _
    · calc
        g (f p) ⊗ₜ[R] (1 : Aᵧ) = eb.symm (f p ⊗ₜ[R] 1) := (hg (f p)).2
        _ = eb.symm (eb (p ⊗ₜ[R] 1)) := congrArg eb.symm (hf p).2
        _ = p ⊗ₜ[R] 1 := eb.symm_apply_apply _
  exact ⟨AlgEquiv.ofAlgHom f g hfg hgf, hf, hg⟩

end SchemeTheory
