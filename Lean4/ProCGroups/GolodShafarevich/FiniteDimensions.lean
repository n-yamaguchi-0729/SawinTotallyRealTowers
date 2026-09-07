import ProCGroups.GolodShafarevich.GradedPieces
import Mathlib.LinearAlgebra.Dimension.RankNullity

set_option autoImplicit false
/-!
# Finite augmentation-dimension sequences

For a finite target group, the dimensions of the augmentation truncations
form a bounded monotone sequence and hence eventually stabilize.  The
degree-zero truncation is the one-dimensional augmentation quotient.
-/

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra
open ProCGroups

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The canonical mod-`p` augmentation as an algebra homomorphism over its
coefficient field. -/
def modPCanonicalAugmentationAlgHom :
    ModPCompletedGroupAlgebra p G →ₐ[ZMod p] ZMod p where
  toRingHom := completedGroupAlgebraCanonicalAugmentationInClass
    (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
  commutes' :=
    completedGroupAlgebraCanonicalAugmentationInClass_algebraMap
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The canonical mod-`p` augmentation, regarded as a linear map over its
coefficient field. -/
def modPCanonicalAugmentationLinearMap :
    ModPCompletedGroupAlgebra p G →ₗ[ZMod p] ZMod p :=
  (modPCanonicalAugmentationAlgHom (p := p) (G := G)).toLinearMap

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
@[simp] theorem modPCanonicalAugmentationLinearMap_apply
    (x : ModPCompletedGroupAlgebra p G) :
    modPCanonicalAugmentationLinearMap (p := p) (G := G) x =
      completedGroupAlgebraCanonicalAugmentationInClass
        (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p) x :=
  rfl

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The canonical mod-`p` augmentation ideal is closed. -/
theorem isClosed_modPAugmentationIdeal :
    IsClosed
      ((modPAugmentationIdeal p G :
        Ideal (ModPCompletedGroupAlgebra p G)) :
          Set (ModPCompletedGroupAlgebra p G)) := by
  change IsClosed
    ((completedGroupAlgebraCanonicalAugmentationInClass
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)) ⁻¹' {0})
  exact isClosed_singleton.preimage
    (continuous_completedGroupAlgebraCanonicalAugmentationInClass
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p))

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The first closed augmentation power is the augmentation ideal itself. -/
theorem closedAugmentationPower_one_eq_modPAugmentationIdeal :
    closedAugmentationPower p G 1 = modPAugmentationIdeal p G := by
  rw [closedAugmentationPower, Submodule.pow_one]
  ext x
  change x ∈ closure
      (((modPAugmentationIdeal p G :
        Ideal (ModPCompletedGroupAlgebra p G)) :
          Set (ModPCompletedGroupAlgebra p G))) ↔
    x ∈ modPAugmentationIdeal p G
  rw [(isClosed_modPAugmentationIdeal (p := p) (G := G)).closure_eq]
  rfl

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The degree-zero truncation is the augmentation quotient and has dimension
one over `ZMod p`. -/
@[simp] theorem truncatedAugmentationDimension_zero :
    truncatedAugmentationDimension (p := p) (G := G) 0 = 1 := by
  let ε := modPCanonicalAugmentationLinearMap (p := p) (G := G)
  have hker :
      shiftedClosedAugmentationSubmodule (p := p) (G := G) 0 0 = ε.ker := by
    ext x
    change x ∈ closedAugmentationPower p G 1 ↔ ε x = 0
    rw [closedAugmentationPower_one_eq_modPAugmentationIdeal]
    rfl
  have hsurj : Function.Surjective ε :=
    completedGroupAlgebraCanonicalAugmentationInClass_surjective
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
  unfold truncatedAugmentationDimension
  calc
    Module.finrank (ZMod p)
        (ShiftedAugmentationTruncation (p := p) (G := G) 0 0) =
        Module.finrank (ZMod p)
          (ModPCompletedGroupAlgebra p G ⧸ ε.ker) :=
      (Submodule.quotEquivOfEq _ _ hker).finrank_eq
    _ = Module.finrank (ZMod p) (ZMod p) :=
      (ε.quotKerEquivOfSurjective hsurj).finrank_eq
    _ = 1 := Module.finrank_self (ZMod p)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- For a finite group, augmentation-truncation dimensions increase with the
cutoff. -/
theorem truncatedAugmentationDimension_monotone [Finite G] :
    Monotone (truncatedAugmentationDimension (p := p) (G := G)) := by
  let _ : Finite (ModPCompletedGroupAlgebra p G) :=
    finite_modPCompletedGroupAlgebra
  let _ : Module.Finite (ZMod p) (ModPCompletedGroupAlgebra p G) :=
    Module.Finite.of_finite
  intro m n hmn
  let S (k : ℕ) : Submodule (ZMod p) (ModPCompletedGroupAlgebra p G) :=
    shiftedClosedAugmentationSubmodule (p := p) (G := G) k 0
  have hsub : S n ≤ S m := by
    intro x hx
    change x ∈ closedAugmentationPower p G (n + 1) at hx
    change x ∈ closedAugmentationPower p G (m + 1)
    exact closedAugmentationPower_antitone (p := p) (G := G)
      (Nat.add_le_add_right hmn 1) hx
  change Module.finrank (ZMod p)
      (ModPCompletedGroupAlgebra p G ⧸ S m) ≤
    Module.finrank (ZMod p)
      (ModPCompletedGroupAlgebra p G ⧸ S n)
  exact (Submodule.factor hsub).finrank_le_finrank_of_surjective
    (Submodule.factor_surjective hsub)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- For a finite group, every truncation dimension is bounded by the
dimension of the completed group algebra. -/
theorem truncatedAugmentationDimension_le [Finite G] (N : ℕ) :
    truncatedAugmentationDimension (p := p) (G := G) N ≤
      Module.finrank (ZMod p) (ModPCompletedGroupAlgebra p G) := by
  let _ : Finite (ModPCompletedGroupAlgebra p G) :=
    finite_modPCompletedGroupAlgebra
  let _ : Module.Finite (ZMod p) (ModPCompletedGroupAlgebra p G) :=
    Module.Finite.of_finite
  unfold truncatedAugmentationDimension ShiftedAugmentationTruncation
  exact (shiftedClosedAugmentationSubmodule (p := p) (G := G) N 0).mkQ
    |>.finrank_le_finrank_of_surjective
      (Submodule.mkQ_surjective _)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The finite-group truncation dimensions admit a uniform natural-number
bound. -/
theorem truncatedAugmentationDimension_bounded [Finite G] :
    ∃ C, ∀ N, truncatedAugmentationDimension (p := p) (G := G) N ≤ C :=
  ⟨Module.finrank (ZMod p) (ModPCompletedGroupAlgebra p G),
    truncatedAugmentationDimension_le (p := p) (G := G)⟩

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- A finite group's bounded monotone truncation-dimension sequence is
eventually constant. -/
theorem truncatedAugmentationDimension_eventuallyConstant [Finite G] :
    ∃ M, ∀ N, M ≤ N →
      truncatedAugmentationDimension (p := p) (G := G) N =
        truncatedAugmentationDimension (p := p) (G := G) M := by
  obtain ⟨b, M, hM⟩ := converges_of_monotone_of_bounded
    (truncatedAugmentationDimension_monotone (p := p) (G := G))
    (truncatedAugmentationDimension_le (p := p) (G := G))
  exact ⟨M, fun N hMN ↦ (hM N hMN).trans (hM M le_rfl).symm⟩

end

end ClassFieldTower.ProP
