import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.RelativeUnramifiedFixedField
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.UnramifiedFixedFieldCompositum
import ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields
import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.FiniteUnramifiedField
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFinrankTransfer
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension
import ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

noncomputable section

namespace LocalClassFieldTheory

open ClassFormation CyclicCohomology RamificationTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open scoped ValuativeRel

variable (K : Type) [Field K]

/-- An actual finite Galois intermediate field gives its finite abstract
fixed subgroup, with finiteness supplied by the actual Galois quotient. -/
abbrev finiteAbstractFieldOfGaloisIntermediateField
    (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsGalois K F] :
    FiniteAbstractField (Gal(SeparableClosure K / K)) where
  field := closedFixingSubgroup K (SeparableClosure K) F
  finite := by
    apply Nat.finite_of_card_ne_zero
    change F.fixingSubgroup.relIndex ⊤ ≠ 0
    rw [Subgroup.relIndex_top_right,
      ← IntermediateField.finrank_eq_fixingSubgroup_index (F := K) (SeparableClosure K) F]
    exact Module.finrank_pos.ne'

/-- The abstract package returns precisely the original intermediate field. -/
theorem fixedField_finiteAbstractFieldOfGaloisIntermediateField
    (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsGalois K F] :
    abstractFixedField K (SeparableClosure K)
      (finiteAbstractFieldOfGaloisIntermediateField K F).field = F :=
  InfiniteGalois.fixedField_fixingSubgroup F

private theorem finrank_inclusion_congr
    (A B C D : IntermediateField K (SeparableClosure K))
    (hAB : A = B) (hCD : C = D) (hAC : A ≤ C) (hBD : B ≤ D) :
    letI : Algebra A C := (IntermediateField.inclusion hAC).toRingHom.toAlgebra
    letI : Algebra B D := (IntermediateField.inclusion hBD).toRingHom.toAlgebra
    Module.finrank A C = Module.finrank B D := by
  subst B
  subst D
  rfl

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The relative degree-kernel field over an actual finite Galois field is
the compositum with the standard unramified field of degree `f * m`. -/
theorem relativeUnramifiedFixedField_actual_eq_sup
    (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsGalois K F]
    (m : ℕ) (hm : 0 < m) :
    relativeUnramifiedFixedField K
      (finiteAbstractFieldOfGaloisIntermediateField K F) m hm =
        F ⊔ localFiniteUnramifiedField K
          (((finiteAbstractFieldOfGaloisIntermediateField K F).residueDegree
            (localResidueDatum K) : ℕ) * m)
          (Nat.mul_pos
            ((finiteAbstractFieldOfGaloisIntermediateField K F).residueDegree
              (localResidueDatum K)).property hm) := by
  have h := relativeUnramifiedFixedField_eq_sup_standard K
    (finiteAbstractFieldOfGaloisIntermediateField K F) m hm
  rw [fixedField_finiteAbstractFieldOfGaloisIntermediateField K F] at h
  exact h

/-- Normality of the two actual factors makes the common field Galois
also over the original local base. -/
theorem relativeUnramifiedFixedField_actual_isGalois
    (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsGalois K F]
    (m : ℕ) (hm : 0 < m) :
    IsGalois K (relativeUnramifiedFixedField K
      (finiteAbstractFieldOfGaloisIntermediateField K F) m hm) := by
  rw [relativeUnramifiedFixedField_actual_eq_sup K F m hm]
  infer_instance


/-- The original actual field embeds in its unramified common extension. -/
theorem le_relativeUnramifiedFixedField_actual
    (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsGalois K F]
    (m : ℕ) (hm : 0 < m) :
    F ≤ relativeUnramifiedFixedField K
      (finiteAbstractFieldOfGaloisIntermediateField K F) m hm := by
  rw [relativeUnramifiedFixedField_actual_eq_sup K F m hm]
  exact le_sup_left

/-- The degree over the original actual field is the prescribed `m`,
for its literal intermediate-field inclusion. -/
theorem relativeUnramifiedFixedField_actual_finrank
    (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsGalois K F]
    (m : ℕ) (hm : 0 < m) :
    letI : Algebra F (relativeUnramifiedFixedField K
        (finiteAbstractFieldOfGaloisIntermediateField K F) m hm) :=
      (IntermediateField.inclusion
        (le_relativeUnramifiedFixedField_actual K F m hm)).toRingHom.toAlgebra
    Module.finrank F (relativeUnramifiedFixedField K
      (finiteAbstractFieldOfGaloisIntermediateField K F) m hm) = m := by
  let H := finiteAbstractFieldOfGaloisIntermediateField K F
  let N := relativeUnramifiedFixedField K H m hm
  have hF : abstractFixedField K (SeparableClosure K) H.field = F :=
    fixedField_finiteAbstractFieldOfGaloisIntermediateField K F
  have hF0N : abstractFixedField K (SeparableClosure K) H.field ≤ N :=
    abstractFixedField_le K (SeparableClosure K)
      (relativeUnramifiedFiniteExtension K H m hm).below
  have hdegree := finrank_inclusion_congr K
    (abstractFixedField K (SeparableClosure K) H.field) F N N hF rfl hF0N
    (le_relativeUnramifiedFixedField_actual K F m hm)
  exact hdegree.symm.trans (relativeUnramifiedFixedField_finrank K H m hm)


/-- Scalars from the original field act through its actual inclusion. -/
@[reducible]
def relativeUnramifiedFixedField_actual_algebra
    (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsGalois K F]
    (m : ℕ) (hm : 0 < m) :
    Algebra F (relativeUnramifiedFixedField K
      (finiteAbstractFieldOfGaloisIntermediateField K F) m hm) :=
  (IntermediateField.inclusion
    (le_relativeUnramifiedFixedField_actual K F m hm)).toRingHom.toAlgebra

attribute [local instance] relativeUnramifiedFixedField_actual_algebra

section BaseValuations

variable (F : IntermediateField K (SeparableClosure K))
  [FiniteDimensional K F] [IsGalois K F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation F)]

/-- The abstract absolute residue degree is the residue degree of the
original actual intermediate field. -/
theorem finiteAbstractFieldOfGaloisIntermediateField_residueDegree :
    ((finiteAbstractFieldOfGaloisIntermediateField K F).residueDegree
      (localResidueDatum K) : ℕ) = Module.finrank 𝓀[K] 𝓀[F] := by
  let H := finiteAbstractFieldOfGaloisIntermediateField K F
  let E := abstractFixedField K (SeparableClosure K) H.field
  have hE : E = F := fixedField_finiteAbstractFieldOfGaloisIntermediateField K F
  have hTransfer : ∀ (L : IntermediateField K (SeparableClosure K)), L = E →
      ∀ [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
        [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
        [FiniteDimensional K L],
        (H.residueDegree (localResidueDatum K) : ℕ) = Module.finrank 𝓀[K] 𝓀[L] := by
    intro L hL
    subst L
    intro vE tE localE extKE finiteKE
    exact localResidueDatum_residueDegree_eq_residueFinrank K H
  exact hTransfer F hE.symm

/-- Choosing the actual ramification index as relative unramified degree
makes the absolute standard factor have exactly the degree of `F/K`. -/
theorem relativeUnramifiedFixedField_ramification_eq_sup_sameDegree :
    ∃ he : 0 < (𝓂[F] : Ideal 𝒪[F]).ramificationIdx 𝒪[K],
      relativeUnramifiedFixedField K
        (finiteAbstractFieldOfGaloisIntermediateField K F)
        ((𝓂[F] : Ideal 𝒪[F]).ramificationIdx 𝒪[K]) he =
      F ⊔ localFiniteUnramifiedField K (Module.finrank K F) Module.finrank_pos := by
  have : IsIntegralClosure 𝒪[F] 𝒪[K] F :=
    localCompleteDVF_integerRing_isIntegralClosure K F
  have : Module.Finite 𝒪[K] 𝒪[F] := localCompleteDVF_integerRing_moduleFinite K F
  have hfund :=
    maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank_of_isIntegralClosure K F
  have hp : (𝓂[K] : Ideal 𝒪[K]) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal 𝒪[K])
      (IsDiscreteValuationRing.not_isField 𝒪[K])
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp] at hfund
  have he : 0 < (𝓂[F] : Ideal 𝒪[F]).ramificationIdx 𝒪[K] := by
    have hprod : 0 < (𝓂[F] : Ideal 𝒪[F]).ramificationIdx 𝒪[K] *
        Module.finrank 𝓀[K] 𝓀[F] := by
      rw [hfund]
      exact Module.finrank_pos
    exact Nat.pos_of_mul_pos_right hprod
  refine ⟨he, ?_⟩
  have hdegree :
      ((finiteAbstractFieldOfGaloisIntermediateField K F).residueDegree
        (localResidueDatum K) : ℕ) * (𝓂[F] : Ideal 𝒪[F]).ramificationIdx 𝒪[K] =
      Module.finrank K F := by
    rw [finiteAbstractFieldOfGaloisIntermediateField_residueDegree K F, Nat.mul_comm]
    exact hfund
  have hsup := relativeUnramifiedFixedField_actual_eq_sup K F
    ((𝓂[F] : Ideal 𝒪[F]).ramificationIdx 𝒪[K]) he
  simpa only [hdegree] using hsup

end BaseValuations

section ActualValuations

variable (F : IntermediateField K (SeparableClosure K))
  [FiniteDimensional K F] [IsGalois K F] (m : ℕ) (hm : 0 < m)
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel (relativeUnramifiedFixedField K
    (finiteAbstractFieldOfGaloisIntermediateField K F) m hm)]
  [TopologicalSpace (relativeUnramifiedFixedField K
    (finiteAbstractFieldOfGaloisIntermediateField K F) m hm)]
  [IsNonarchimedeanLocalField (relativeUnramifiedFixedField K
    (finiteAbstractFieldOfGaloisIntermediateField K F) m hm)]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation (relativeUnramifiedFixedField K
      (finiteAbstractFieldOfGaloisIntermediateField K F) m hm))]
  [Valuation.HasExtension (ValuativeRel.valuation F)
    (ValuativeRel.valuation (relativeUnramifiedFixedField K
      (finiteAbstractFieldOfGaloisIntermediateField K F) m hm))]

/-- Unramifiedness over the literal original field, for the compatible
valuations and the canonical inclusion of that field. -/
theorem relativeUnramifiedFixedField_actual_isUnramifiedValuedExtension
    [FiniteDimensional F (relativeUnramifiedFixedField K
      (finiteAbstractFieldOfGaloisIntermediateField K F) m hm)]
    [Module.Finite 𝒪[F] 𝒪[relativeUnramifiedFixedField K
      (finiteAbstractFieldOfGaloisIntermediateField K F) m hm]] :
    IsUnramifiedValuedExtension F (relativeUnramifiedFixedField K
      (finiteAbstractFieldOfGaloisIntermediateField K F) m hm) := by
  let H := finiteAbstractFieldOfGaloisIntermediateField K F
  let N := relativeUnramifiedFixedField K H m hm
  let E := abstractFixedField K (SeparableClosure K) H.field
  have hE : E = F := fixedField_finiteAbstractFieldOfGaloisIntermediateField K F
  have hTransfer : ∀ (L : IntermediateField K (SeparableClosure K)) (hLN : L ≤ N),
      L = E →
      (letI : Algebra L N := (IntermediateField.inclusion hLN).toRingHom.toAlgebra
       ∀ [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
         [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
         [Valuation.HasExtension (ValuativeRel.valuation L) (ValuativeRel.valuation N)]
         [FiniteDimensional L N] [Module.Finite 𝒪[L] 𝒪[N]],
         IsUnramifiedValuedExtension L N) := by
    intro L hLN hL
    subst L
    let : Algebra E N := relativeUnramifiedFixedField_algebra K H m hm
    intro vE tE localE extKE extEN finiteEN integralFinite
    have hExtEN : Valuation.HasExtension (ValuativeRel.valuation E)
        (ValuativeRel.valuation N) := extEN
    have hFiniteEN : FiniteDimensional E N :=
      relativeUnramifiedFixedField_finiteDimensional K H m hm
    have hIntegralFinite : Module.Finite 𝒪[E] 𝒪[N] := integralFinite
    exact relativeUnramifiedFixedField_isUnramifiedValuedExtension K H m hm
  exact hTransfer F (le_relativeUnramifiedFixedField_actual K F m hm) hE.symm

end ActualValuations

end LocalClassFieldTheory
end
