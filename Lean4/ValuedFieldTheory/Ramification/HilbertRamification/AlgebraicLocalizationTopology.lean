/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization
import ValuedFieldTheory.Ramification.HilbertRamification.DecompositionField
import Mathlib.FieldTheory.Galois.Profinite

set_option autoImplicit false
/-!
# Topological decomposition--localization comparison

The algebraic localization comparison is algebraically a `MulEquiv`.  This file establishes its
finite-support continuity input: fixing one element of the algebraic localization only requires
fixing finitely many elements of the original algebraic extension.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open scoped Topology

universe u v

section GeneralLocalization

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable [IsGalois K L]
variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
variable (w : AbsoluteValueExtension vK L)

local instance generalLocalizationBaseAlgebra : Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra (K := K) w.1

local instance generalLocalizationBaseSMul : SMul K w.1.Completion :=
  (AbsoluteValue.extensionCompletionAlgebra (K := K) w.1).toSMul

local instance generalLocalizationCompletionAlgebra :
    Algebra vK.Completion w.1.Completion :=
  AbsoluteValue.completionAlgebra vK w.1 w.2

private abbrev localization :=
  AbsoluteValue.algebraicLocalization vK w.1 w.2

omit [IsGalois K L] in
/-- The action on any one algebraic-localization element is controlled by finitely many elements
of the original algebraic extension.  This is the pointwise source for continuity of the
decomposition--localization comparison in the Krull topologies. -/
theorem algebraicLocalization_fixing_finite_support
    (z : localization vK w) :
    ∃ S : Finset L, ∀ σ : absoluteValueDecompositionGroup K w.1,
      (∀ x ∈ S, (σ.1 : L ≃ₐ[K] L) x = x) →
        decompositionGroupToLocalization vK hvK w σ z = z := by
  let E : IntermediateField vK.Completion w.1.Completion :=
    IntermediateField.adjoin vK.Completion
      (Set.range (AbsoluteValue.toCompletion w.1))
  change E at z
  classical
  apply IntermediateField.adjoin_induction
      (p := fun y (hy : y ∈ E) ↦
        ∃ S : Finset L, ∀ σ : absoluteValueDecompositionGroup K w.1,
          (∀ x ∈ S, (σ.1 : L ≃ₐ[K] L) x = x) →
            decompositionGroupToLocalization vK hvK w σ ⟨y, hy⟩ = ⟨y, hy⟩)
      (s := Set.range (AbsoluteValue.toCompletion w.1))
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨{x}, fun σ hσ ↦ ?_⟩
    change decompositionGroupToLocalization vK hvK w σ
      (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) = _
    rw [decompositionGroupToLocalization_toLocalization]
    exact congrArg (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2)
      (hσ x (Finset.mem_singleton_self x))
  · intro y
    refine ⟨∅, fun σ _ ↦ ?_⟩
    exact (decompositionGroupToLocalization vK hvK w σ).commutes y
  · intro x y hx hy
    rintro ⟨Sx, hSx⟩ ⟨Sy, hSy⟩
    refine ⟨Sx ∪ Sy, fun σ hσ ↦ ?_⟩
    change decompositionGroupToLocalization vK hvK w σ
      (⟨x, hx⟩ + ⟨y, hy⟩) = ⟨x, hx⟩ + ⟨y, hy⟩
    rw [map_add, hSx σ (fun a ha ↦ hσ a (Finset.mem_union_left Sy ha)),
      hSy σ (fun a ha ↦ hσ a (Finset.mem_union_right Sx ha))]
  · intro x hx
    rintro ⟨S, hS⟩
    refine ⟨S, fun σ hσ ↦ ?_⟩
    change decompositionGroupToLocalization vK hvK w σ
      (⟨x, hx⟩⁻¹) = ⟨x, hx⟩⁻¹
    rw [map_inv₀, hS σ hσ]
  · intro x y hx hy
    rintro ⟨Sx, hSx⟩ ⟨Sy, hSy⟩
    refine ⟨Sx ∪ Sy, fun σ hσ ↦ ?_⟩
    change decompositionGroupToLocalization vK hvK w σ
      (⟨x, hx⟩ * ⟨y, hy⟩) = ⟨x, hx⟩ * ⟨y, hy⟩
    rw [map_mul, hSx σ (fun a ha ↦ hσ a (Finset.mem_union_left Sy ha)),
      hSy σ (fun a ha ↦ hσ a (Finset.mem_union_right Sx ha))]

/-- The algebraic decomposition--localization comparison as a monoid homomorphism. -/
noncomputable def decompositionGroupToAlgebraicLocalizationMonoidHom :
    absoluteValueDecompositionGroup K w.1 →*
      (localization vK w ≃ₐ[vK.Completion] localization vK w) :=
  (decompositionGroupEquivAlgebraicLocalizationAut vK hvK w).toMonoidHom

private theorem algEquiv_fix_of_fin_generates
    {F A : Type*} [Field F] [Field A] [Algebra F A]
    (E : IntermediateField F A) {n : ℕ} (b : Fin n → E)
    (hb : Submodule.span F (Set.range b) = ⊤)
    (sigma : A ≃ₐ[F] A)
    (hsigma : ∀ i, sigma (b i : A) = b i) (z : E) :
    sigma (z : A) = z := by
  have hlinear :
      sigma.toLinearEquiv.toLinearMap.comp E.val.toLinearMap =
        E.val.toLinearMap :=
    LinearMap.ext_on_range hb fun i ↦ hsigma i
  exact DFunLike.congr_fun hlinear z

private theorem absoluteValueDecompositionGroup_fixing_finset_mem_nhds
    (S : Finset L) :
    {sigma : absoluteValueDecompositionGroup K w.1 |
      ∀ x ∈ S, (sigma.1 : L ≃ₐ[K] L) x = x} ∈ 𝓝 1 := by
  classical
  apply mem_nhds_iff.mpr
  refine ⟨⋂ x : S,
      (Subtype.val : absoluteValueDecompositionGroup K w.1 → Gal(L / K)) ⁻¹'
        (MulAction.stabilizer Gal(L / K) x.1 : Set Gal(L / K)), ?_, ?_⟩
  · intro sigma hsigma x hx
    exact Set.mem_iInter.mp hsigma ⟨x, hx⟩
  · refine ⟨isOpen_iInter_of_finite fun x ↦ ?_, ?_⟩
    · exact (stabilizer_isOpen_of_isIntegral (K := K) x.1).preimage
        continuous_subtype_val
    · exact Set.mem_iInter.mpr fun _ ↦ rfl

/-- The subgroup of the decomposition group fixing one algebraic-localization element. -/
noncomputable def algebraicLocalizationStabilizerSubgroup
    (z : localization vK w) :
    Subgroup (absoluteValueDecompositionGroup K w.1) :=
  (MulAction.stabilizer
    (localization vK w ≃ₐ[vK.Completion] localization vK w) z).comap
      (decompositionGroupToAlgebraicLocalizationMonoidHom vK hvK w)

@[simp] theorem mem_algebraicLocalizationStabilizerSubgroup_iff
    (z : localization vK w) (sigma : absoluteValueDecompositionGroup K w.1) :
    sigma ∈ algebraicLocalizationStabilizerSubgroup vK hvK w z ↔
      decompositionGroupToAlgebraicLocalizationMonoidHom vK hvK w sigma z = z :=
  Iff.rfl

/-- The stabilizer of one algebraic-localization element has open preimage in the decomposition
group. -/
theorem decompositionGroupToAlgebraicLocalization_stabilizer_isOpen
    (z : localization vK w) :
    IsOpen (algebraicLocalizationStabilizerSubgroup vK hvK w z :
      Set (absoluteValueDecompositionGroup K w.1)) := by
  apply Subgroup.isOpen_of_mem_nhds
  rcases algebraicLocalization_fixing_finite_support vK hvK w z with ⟨S, hS⟩
  exact Filter.mem_of_superset
    (absoluteValueDecompositionGroup_fixing_finset_mem_nhds vK w S) fun sigma hsigma ↦
      (mem_algebraicLocalizationStabilizerSubgroup_iff vK hvK w z sigma).2
        (hS sigma hsigma)

/-- The preimage of a finite-stage fixing subgroup is a neighborhood of the identity in the
decomposition group. -/
theorem decompositionGroupToAlgebraicLocalization_fixingSubgroup_mem_nhds
    (E : IntermediateField vK.Completion (localization vK w))
    [FiniteDimensional vK.Completion E] :
    {sigma : absoluteValueDecompositionGroup K w.1 |
        decompositionGroupToAlgebraicLocalizationMonoidHom vK hvK w sigma ∈
          E.fixingSubgroup} ∈ 𝓝 1 := by
  let phi := decompositionGroupToAlgebraicLocalizationMonoidHom vK hvK w
  rcases Module.Finite.exists_fin (R := vK.Completion) (M := E) with
    ⟨n, b, hb⟩
  apply mem_nhds_iff.mpr
  refine ⟨⋂ i, (algebraicLocalizationStabilizerSubgroup
      vK hvK w (b i : localization vK w) :
        Set (absoluteValueDecompositionGroup K w.1)), ?_, ?_⟩
  · intro sigma hsigma
    change phi sigma ∈ E.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    exact algEquiv_fix_of_fin_generates E b hb (phi sigma)
      (fun i ↦ (mem_algebraicLocalizationStabilizerSubgroup_iff
        vK hvK w (b i : localization vK w) sigma).1
          (Set.mem_iInter.mp hsigma i)) ⟨z, hz⟩
  · refine ⟨isOpen_iInter_of_finite fun i ↦ ?_, ?_⟩
    · exact decompositionGroupToAlgebraicLocalization_stabilizer_isOpen
        vK hvK w (b i : localization vK w)
    · exact Set.mem_iInter.mpr fun i ↦
        (algebraicLocalizationStabilizerSubgroup vK hvK w
          (b i : localization vK w)).one_mem

/-- The decomposition--localization comparison is continuous for the two Krull topologies. -/
theorem decompositionGroupToAlgebraicLocalization_continuous :
    Continuous (decompositionGroupEquivAlgebraicLocalizationAut vK hvK w) := by
  let _ : Algebra.IsAlgebraic vK.Completion (localization vK w) :=
    AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2
  let phi := decompositionGroupToAlgebraicLocalizationMonoidHom vK hvK w
  change Continuous phi
  apply continuous_of_continuousAt_one phi
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro U hU
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff
      vK.Completion (localization vK w) U).1 hU with ⟨E, hE, hEU⟩
  let : FiniteDimensional vK.Completion E := hE
  exact Filter.mem_of_superset
    (decompositionGroupToAlgebraicLocalization_fixingSubgroup_mem_nhds
      vK hvK w E) fun sigma hsigma ↦ hEU hsigma

/-- The decomposition group and the algebraic-localization Galois group are canonically
isomorphic as topological groups. -/
noncomputable def decompositionGroupContinuousMulEquivAlgebraicLocalizationAut :
    absoluteValueDecompositionGroup K w.1 ≃ₜ*
      (localization vK w ≃ₐ[vK.Completion] localization vK w) := by
  letI : Algebra.IsAlgebraic vK.Completion (localization vK w) :=
    AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2
  letI : T2Space (localization vK w ≃ₐ[vK.Completion] localization vK w) :=
    krullTopology_t2
  letI : CompactSpace (absoluteValueDecompositionGroup K w.1) :=
    isCompact_iff_compactSpace.mp
      (absoluteValueDecompositionGroup_isClosed K w.1).isCompact
  let h := Continuous.homeoOfEquivCompactToT2
    (f := (decompositionGroupEquivAlgebraicLocalizationAut vK hvK w).toEquiv)
    (decompositionGroupToAlgebraicLocalization_continuous vK hvK w)
  exact
    { toMulEquiv := decompositionGroupEquivAlgebraicLocalizationAut vK hvK w
      continuous_toFun := h.continuous
      continuous_invFun := h.symm.continuous }

end GeneralLocalization

end ClassFieldTower.Martinet.Shafarevich
