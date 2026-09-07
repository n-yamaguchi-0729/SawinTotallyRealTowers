import GaloisCohomology.ProP.PresentationQuotientEquiv
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.ProfiniteIntegerH2
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum

set_option autoImplicit false
/-!
# Vanishing of local unramified degree-two cohomology

For a nonarchimedean local field, the continuous residue-degree map is onto the profinite
integers.  Its kernel is the kernel of the residue action, and the corresponding quotient is
therefore continuously equivalent to `ZHatMul`.  Continuous degree-two cohomology of this
unramified quotient with trivial `ZMod p` coefficients vanishes.
-/

open CategoryTheory LocalFieldTheory
open scoped Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology
open ClassFormation
open LocalClassFieldTheory
open ProCGroups
open RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The kernel of the local residue degree is exactly the kernel of the residue action. -/
theorem localResidueDegree_ker_eq_residueAction_ker :
    MonoidHom.ker (localResidueDegree K).toMonoidHom =
      MonoidHom.ker (localSeparableResidueAlgAction K).toMonoidHom := by
  ext sigma
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro hsigma
    change residueAbsoluteDegreeIn
        (decompositionResidueField K (localSeparableValuationSubring K))
        (selectedResidueField (localSeparableValuationSubring K))
        (localSeparableResidueAlgAction K sigma) = 1 at hsigma
    have hdegree :
        residueAbsoluteDegreeIn
            (decompositionResidueField K (localSeparableValuationSubring K))
            (selectedResidueField (localSeparableValuationSubring K))
            (localSeparableResidueAlgAction K sigma) =
          residueAbsoluteDegreeIn
            (decompositionResidueField K (localSeparableValuationSubring K))
            (selectedResidueField (localSeparableValuationSubring K)) 1 := by
      simpa using hsigma
    exact (residueAbsoluteFrobeniusEquivIn
      (decompositionResidueField K (localSeparableValuationSubring K))
      (selectedResidueField (localSeparableValuationSubring K))).symm.injective hdegree
  · intro hsigma
    change localSeparableResidueAlgAction K sigma = 1 at hsigma
    change residueAbsoluteDegreeIn
        (decompositionResidueField K (localSeparableValuationSubring K))
        (selectedResidueField (localSeparableValuationSubring K))
        (localSeparableResidueAlgAction K sigma) = 1
    rw [hsigma]
    exact map_one _

/-- The Galois quotient detected by the local residue-degree map. -/
abbrev LocalUnramifiedGaloisQuotient :=
  Gal(SeparableClosure K / K) ⧸
    MonoidHom.ker (localResidueDegree K).toMonoidHom

/-- The local unramified Galois quotient is continuously equivalent to the profinite integers. -/
noncomputable def localUnramifiedQuotientContinuousMulEquiv :
    LocalUnramifiedGaloisQuotient K ≃ₜ* ZHatMul := by
  let q := localResidueDegree K
  letI : CompactSpace q.range := isCompact_iff_compactSpace.mp <| by
    simpa using isCompact_range q.continuous_toFun
  let er : q.range ≃ₜ* ZHatMul :=
    ContinuousMulEquiv.ofBijectiveCompactToT2 (Subgroup.subtype q.range)
      continuous_subtype_val
      ⟨Subtype.coe_injective, by
        intro z
        obtain ⟨sigma, hsigma⟩ := localResidueDegree_surjective K z
        exact ⟨⟨q sigma, ⟨sigma, rfl⟩⟩, hsigma⟩⟩
  exact (ContinuousMonoidHom.quotientKerContinuousMulEquivRange q).trans er

variable (p : ℕ) [Fact p.Prime]

/-- Pullback along the unramified quotient equivalence identifies its degree-two cohomology
with degree-two cohomology of the profinite integers. -/
noncomputable def localUnramifiedQuotientH2LinearEquiv :
    continuousCohomologyZModPLifted p ZHatMul 2 ≃ₗ[ZMod p]
      continuousCohomologyZModPLifted p (LocalUnramifiedGaloisQuotient K) 2 :=
  continuousCohomologyZModPLiftedLinearEquiv
    (localUnramifiedQuotientContinuousMulEquiv K) 2

/-- Continuous `H²` of the local unramified quotient with trivial `ZMod p` coefficients
vanishes. -/
theorem localUnramifiedQuotientH2_subsingleton :
    Subsingleton
      (continuousCohomologyZModPLifted p (LocalUnramifiedGaloisQuotient K) 2) := by
  let e := localUnramifiedQuotientH2LinearEquiv K p
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  congr 1
  exact @Subsingleton.elim
    (continuousCohomologyZModPLifted p ZHatMul 2)
    (ClassFieldTower.Cohomology.ProfiniteInteger.degree_two_subsingleton (p := p)) a b

end ClassFieldTower.Martinet.Shafarevich
