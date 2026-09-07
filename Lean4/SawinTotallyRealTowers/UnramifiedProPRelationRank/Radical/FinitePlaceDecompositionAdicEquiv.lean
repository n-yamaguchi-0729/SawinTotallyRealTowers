import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceCyclotomicMuPKummerComparison
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality

set_option autoImplicit false
/-!
# The actual decomposition--adic Galois equivalence

The previously constructed forward map is conjugation by algebraic-closure
equivalences.  Its inverse is continuous by the same semilinear conjugation
theorem; no compactness instance or new Galois structure is installed.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open NumberField IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

private theorem fieldAlgebra_isTorsionFree_forAdicEquiv
    {K L : Type} [Field K] [Field L] [Algebra K L] :
    Module.IsTorsionFree K L :=
  Module.IsTorsionFree.of_smul_eq_zero fun r x h ↦ by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with hr | hx
    · exact Or.inl ((algebraMap K L).injective (by simpa using hr))
    · exact Or.inr hx

local instance finitePlaceCompletionClosureSourceTorsionFree
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    Module.IsTorsionFree (NumberField.HeightOneSpectrum.adicAbv F v).Completion
      (AlgebraicClosure (NumberField.HeightOneSpectrum.adicAbv F v).Completion) :=
  fieldAlgebra_isTorsionFree_forAdicEquiv

local instance finitePlaceCompletionClosureTargetTorsionFree
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    Module.IsTorsionFree (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) :=
  fieldAlgebra_isTorsionFree_forAdicEquiv

/-- The actual algebraic-closure equivalence underlying the completion comparison. -/
noncomputable def finitePlaceCompletionAlgebraicClosureRingEquiv
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    AlgebraicClosure (NumberField.HeightOneSpectrum.adicAbv F v).Completion ≃+*
      AlgebraicClosure (v.adicCompletion F) :=
  IsAlgClosure.equivOfEquiv _ _ (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv

@[simp] theorem finitePlaceCompletionAlgebraicClosureRingEquiv_algebraMap
    (v : HeightOneSpectrum (RingOfIntegers F))
    (x : (NumberField.HeightOneSpectrum.adicAbv F v).Completion) :
    finitePlaceCompletionAlgebraicClosureRingEquiv F v (algebraMap _ _ x) =
      algebraMap (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F))
        (relativeFinitePlaceCompletionAlgEquiv v x) :=
  IsAlgClosure.equivOfEquiv_algebraMap _ _ _ _

/-- The completion-model comparison, with its explicit continuous inverse. -/
noncomputable def finitePlaceCompletionAbsoluteGaloisContinuousMulEquiv
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    Field.absoluteGaloisGroup
        (NumberField.HeightOneSpectrum.adicAbv F v).Completion ≃ₜ*
      Field.absoluteGaloisGroup (v.adicCompletion F) := by
  let C := (NumberField.HeightOneSpectrum.adicAbv F v).Completion
  let C' := v.adicCompletion F
  let c : C ≃+* C' :=
    (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let e : AlgebraicClosure C ≃+* AlgebraicClosure C' :=
    finitePlaceCompletionAlgebraicClosureRingEquiv F v
  let g := LocalClassFieldTheory.semilinearGaloisGroupCongr C C'
      (AlgebraicClosure C) (AlgebraicClosure C') c e
      (IsAlgClosure.equivOfEquiv_algebraMap _ _ c)
  refine
    { toMulEquiv := g
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · exact (finitePlaceCompletionAbsoluteGaloisSemilinearCongr F v).continuous
  · have he : ∀ x : C',
        e.symm (algebraMap C' (AlgebraicClosure C') x) =
          algebraMap C (AlgebraicClosure C) (c.symm x) :=
      IsAlgClosure.equivOfEquiv_symm_algebraMap _ _ c
    exact RamificationTheory.Field.absoluteGaloisGroup.semilinear_conjugation_continuous
      c.symm e.symm he g.symm.toMonoidHom (fun _ ↦ rfl)

@[simp] theorem finitePlaceCompletionAbsoluteGaloisContinuousMulEquiv_apply
    (v : HeightOneSpectrum (RingOfIntegers F))
    (sigma : Field.absoluteGaloisGroup
      (NumberField.HeightOneSpectrum.adicAbv F v).Completion) :
    finitePlaceCompletionAbsoluteGaloisContinuousMulEquiv F v sigma =
      finitePlaceCompletionAbsoluteGaloisSemilinearCongr F v sigma := rfl

theorem finitePlaceCompletionAbsoluteGaloisSemilinearCongr_bijective
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    Function.Bijective (finitePlaceCompletionAbsoluteGaloisSemilinearCongr F v) :=
  (finitePlaceCompletionAbsoluteGaloisContinuousMulEquiv F v).bijective

theorem finitePlaceDecompositionToAdicAbsoluteGaloisGroup_bijective
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    Function.Bijective (finitePlaceDecompositionToAdicAbsoluteGaloisGroup F v) :=
  (finitePlaceCompletionAbsoluteGaloisSemilinearCongr_bijective F v).comp
    (finitePlaceDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup F v).bijective

/-- The actual algebraic-localization map is a topological equivalence, with
the same forward map used by finite-place cohomology restriction. -/
noncomputable def finitePlaceDecompositionAdicContinuousMulEquiv
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    finitePlaceAbsoluteDecompositionGroup F v ≃ₜ*
      Field.absoluteGaloisGroup (v.adicCompletion F) :=
  (finitePlaceDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup F v).trans
    (finitePlaceCompletionAbsoluteGaloisContinuousMulEquiv F v)

@[simp] theorem finitePlaceDecompositionAdicContinuousMulEquiv_apply
    (v : HeightOneSpectrum (RingOfIntegers F))
    (sigma : finitePlaceAbsoluteDecompositionGroup F v) :
    finitePlaceDecompositionAdicContinuousMulEquiv F v sigma =
      finitePlaceDecompositionToAdicAbsoluteGaloisGroup F v sigma := rfl

end ClassFieldTower.Martinet.Shafarevich
