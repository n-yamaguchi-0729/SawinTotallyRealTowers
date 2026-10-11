/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutEquiv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable

/-!
# Semilinear conjugation and restriction to the separable closure

The chosen automorphism of the algebraic closure restricts to the separable
closure. Both directions use that same automorphism and its actual inverse.
-/

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]

/-- Restrict the chosen semilinear automorphism of the algebraic closure to
its separable closure, without assuming that the base field is perfect. -/
def separableClosureEquivOfEquiv (τ : K ≃+* K) :
    SeparableClosure K ≃+* SeparableClosure K := by
  let e : AlgebraicClosure K ≃+* AlgebraicClosure K :=
    IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ
  refine
    { toFun := fun x => ⟨e (x : AlgebraicClosure K),
        IsSeparable.of_equiv_equiv τ e
          (IsAlgClosure.equivOfEquiv_comp_algebraMap
            (AlgebraicClosure K) (AlgebraicClosure K) τ).symm x.property⟩
      invFun := fun x => ⟨e.symm (x : AlgebraicClosure K),
        IsSeparable.of_equiv_equiv τ.symm e.symm
          (IsAlgClosure.equivOfEquiv_symm_comp_algebraMap
            (AlgebraicClosure K) (AlgebraicClosure K) τ).symm x.property⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply (x : AlgebraicClosure K))
      right_inv := fun x => Subtype.ext (e.apply_symm_apply (x : AlgebraicClosure K))
      map_mul' := fun x y => Subtype.ext (map_mul e
        (x : AlgebraicClosure K) (y : AlgebraicClosure K))
      map_add' := fun x y => Subtype.ext (map_add e
        (x : AlgebraicClosure K) (y : AlgebraicClosure K)) }

/-- The forward map is the actual chosen map on the algebraic closure. -/
theorem separableClosureEquivOfEquiv_apply_coe
    (τ : K ≃+* K) (x : SeparableClosure K) :
    (separableClosureEquivOfEquiv τ x : AlgebraicClosure K) =
      IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ
        (x : AlgebraicClosure K) := rfl

/-- The inverse is the inverse of the same chosen map, not a separate choice. -/
theorem separableClosureEquivOfEquiv_symm_apply_coe
    (τ : K ≃+* K) (x : SeparableClosure K) :
    ((separableClosureEquivOfEquiv τ).symm x : AlgebraicClosure K) =
      (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ).symm
        (x : AlgebraicClosure K) := rfl

/-- The restriction retains the original semilinearity over the base field. -/
theorem separableClosureEquivOfEquiv_algebraMap (τ : K ≃+* K) (x : K) :
    separableClosureEquivOfEquiv τ (algebraMap K (SeparableClosure K) x) =
      algebraMap K (SeparableClosure K) (τ x) := by
  apply Subtype.ext
  change IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ
    (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (τ x)
  exact IsAlgClosure.equivOfEquiv_algebraMap
    (AlgebraicClosure K) (AlgebraicClosure K) τ x

/-- Restriction to the separable closure commutes with conjugation by the
same actual semilinear automorphism of the algebraic closure. -/
theorem separableClosureAutEquiv_absoluteGaloisConjugate
    (τ : K ≃+* K) (σ : Gal(AlgebraicClosure K/K)) :
    ValuationTheory.Completion.separableClosureAutEquiv K
        (absoluteGaloisConjugate τ σ) =
      semilinearGaloisConjugate τ (separableClosureEquivOfEquiv τ)
        (separableClosureEquivOfEquiv_algebraMap τ)
        (ValuationTheory.Completion.separableClosureAutEquiv K σ) := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  rw [ValuationTheory.Completion.separableClosureAutEquiv_apply,
    absoluteGaloisConjugate_apply, semilinearGaloisConjugate_apply,
    separableClosureEquivOfEquiv_apply_coe,
    ValuationTheory.Completion.separableClosureAutEquiv_apply,
    separableClosureEquivOfEquiv_symm_apply_coe]

end KummerTheory
