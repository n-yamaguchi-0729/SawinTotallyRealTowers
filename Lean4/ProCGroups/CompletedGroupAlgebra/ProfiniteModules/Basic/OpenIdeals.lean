import ProCGroups.CompletedGroupAlgebra.ProfiniteModules.Basic.Generators

set_option autoImplicit false

/-!
# Open ideals in profinite rings

This file develops open-ideal bases at zero in profinite rings, proves their quotients finite, and
derives the finite-open-ideal quotient basis and linear-topology properties.
-/

open scoped Topology

namespace CompletedGroupAlgebra

universe u v w z

/-- Open ideals form a neighborhood basis at zero. -/
def HasOpenIdealBasisAtZero (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] : Prop :=
  ∀ U ∈ 𝓝 (0 : Λ), ∃ I : Ideal Λ, IsOpen (I : Set Λ) ∧ (I : Set Λ) ⊆ U

/-- Open ideals with finite quotient form a neighborhood basis at zero. -/
def HasFiniteOpenIdealQuotientBasis (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] : Prop :=
  ∀ U ∈ 𝓝 (0 : Λ), ∃ I : Ideal Λ,
    IsOpen (I : Set Λ) ∧ (I : Set Λ) ⊆ U ∧ Nonempty (Fintype (Λ ⧸ I))

/-- An open ideal of a compact topological ring has finite additive quotient. -/
theorem finite_quotient_of_openIdeal
    (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    [CompactSpace Λ]
    (I : Ideal Λ) (hI : IsOpen (I : Set Λ)) :
    Nonempty (Fintype (Λ ⧸ I)) := by
  have : Finite (Λ ⧸ I) :=
    AddSubgroup.quotient_finite_of_isOpen I.toAddSubgroup hI
  exact ⟨Fintype.ofFinite (Λ ⧸ I)⟩

/--
Proposition 5.1.2(d/e), linear-topology interface: a profinite ring whose topology is linear has
a fundamental system of open ideals with finite quotient.
-/
theorem profiniteRing_hasFiniteOpenIdealQuotientBasis_of_linearTopology
    (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] [IsLinearTopology Λ Λ]
    [IsTopologicalRing Λ] [CompactSpace Λ] :
    HasFiniteOpenIdealQuotientBasis Λ := by
  intro U hU
  rcases ((IsLinearTopology.hasBasis_open_ideal).mem_iff.mp hU) with
    ⟨I, hIopen, hIU⟩
  exact ⟨I, hIopen, hIU, finite_quotient_of_openIdeal Λ I hIopen⟩

/-- Proposition 5.1.2(d/e), linear-topology part for profinite rings. -/
theorem profiniteRing_isLinearTopology
    (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    [CompactSpace Λ] [T2Space Λ] [TotallyDisconnectedSpace Λ] :
    IsLinearTopology Λ Λ := by
  let : ContinuousSMul Λ Λ :=
    ContinuousSMul.mk (by simpa [smul_eq_mul] using continuous_mul)
  exact profiniteModule_isLinearTopology Λ Λ

/--
Proposition 5.1.2(d/e): a profinite ring has a fundamental system of open ideals with finite
quotient.
-/
theorem profiniteRing_hasFiniteOpenIdealQuotientBasis
    (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    [CompactSpace Λ] [T2Space Λ] [TotallyDisconnectedSpace Λ] :
    HasFiniteOpenIdealQuotientBasis Λ := by
  let : IsLinearTopology Λ Λ := profiniteRing_isLinearTopology Λ
  exact profiniteRing_hasFiniteOpenIdealQuotientBasis_of_linearTopology Λ

/-- Proposition 5.1.2(d): a profinite ring has a basis of open ideals at zero. -/
theorem profiniteRing_hasOpenIdealBasisAtZero
    (Λ : Type u) [Ring Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    [CompactSpace Λ] [T2Space Λ] [TotallyDisconnectedSpace Λ] :
    HasOpenIdealBasisAtZero Λ := by
  intro U hU
  rcases profiniteRing_hasFiniteOpenIdealQuotientBasis Λ U hU with
    ⟨I, hIopen, hIU, _hfin⟩
  exact ⟨I, hIopen, hIU⟩

end CompletedGroupAlgebra
