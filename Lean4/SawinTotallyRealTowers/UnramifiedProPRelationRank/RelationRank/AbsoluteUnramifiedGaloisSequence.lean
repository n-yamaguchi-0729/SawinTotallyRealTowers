import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.MaximalEverywhereUnramifiedProPGalois
import Mathlib.Algebra.Exact.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Topology.Algebra.Group.Quotient

set_option autoImplicit false
/-!
# The absolute-to-unramified Galois sequence

Restriction from the absolute Galois group to the maximal everywhere-unramified pro-`p`
extension is a continuous quotient map.  Its closed normal kernel is the subgroup fixing that
extension, and quotienting by the kernel gives a continuous group equivalence with the relative
Galois group.

The construction is valid for every prime `p`; no oddness assumption is needed for this Galois-
theoretic step.
-/

open scoped NumberField

noncomputable section

universe u

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Martinet

variable (F : Type u) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

private abbrev M := maximalEverywhereUnramifiedProP F p

private noncomputable instance absoluteGaloisGroup_compactSpace :
    CompactSpace (Field.absoluteGaloisGroup F) :=
  inferInstanceAs
    (CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))

/-- Restriction of absolute automorphisms to the maximal everywhere-unramified pro-`p`
extension. -/
noncomputable def absoluteToMaxEverywhereUnramifiedProP :
    Field.absoluteGaloisGroup F →ₜ*
      MaxEverywhereUnramifiedProPGaloisGroup F p where
  toMonoidHom := AlgEquiv.restrictNormalHom (M F p)
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous (M F p)

/-- Absolute restriction onto the maximal everywhere-unramified pro-`p` Galois group is
surjective. -/
theorem absoluteToMaxEverywhereUnramifiedProP_surjective :
    Function.Surjective (absoluteToMaxEverywhereUnramifiedProP F p) :=
  AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure F)

/-- The closed subgroup of the absolute Galois group fixing the maximal everywhere-unramified
pro-`p` extension. -/
def absoluteUnramifiedKernel : ClosedSubgroup (Field.absoluteGaloisGroup F) where
  toSubgroup := (M F p).fixingSubgroup
  isClosed' := InfiniteGalois.fixingSubgroup_isClosed (M F p)

/-- The kernel of absolute restriction is exactly the fixing subgroup of the maximal
everywhere-unramified pro-`p` extension. -/
theorem absoluteToMaxEverywhereUnramifiedProP_ker :
    (absoluteToMaxEverywhereUnramifiedProP F p).toMonoidHom.ker =
      (absoluteUnramifiedKernel F p).toSubgroup := by
  exact IntermediateField.restrictNormalHom_ker (M F p)

/-- The absolute unramified kernel is normal. -/
instance absoluteUnramifiedKernel_normal :
    (absoluteUnramifiedKernel F p).Normal := by
  change (M F p).fixingSubgroup.Normal
  rw [← IntermediateField.restrictNormalHom_ker (M F p)]
  exact MonoidHom.normal_ker _

/-- Continuous inclusion of the absolute unramified kernel. -/
def absoluteUnramifiedKernelInclusion :
    absoluteUnramifiedKernel F p →ₜ* Field.absoluteGaloisGroup F where
  toMonoidHom := (absoluteUnramifiedKernel F p).toSubgroup.subtype
  continuous_toFun := continuous_subtype_val

/-- Inclusion of the absolute unramified kernel is injective. -/
theorem absoluteUnramifiedKernelInclusion_injective :
    Function.Injective (absoluteUnramifiedKernelInclusion F p) :=
  Subtype.val_injective

/-- The kernel inclusion followed by absolute restriction is exact in the multiplicative
sense. -/
theorem absoluteUnramifiedGaloisSequence_mulExact :
    Function.MulExact (absoluteUnramifiedKernelInclusion F p)
      (absoluteToMaxEverywhereUnramifiedProP F p) := by
  change Function.MulExact
    (absoluteUnramifiedKernelInclusion F p).toMonoidHom
    (absoluteToMaxEverywhereUnramifiedProP F p).toMonoidHom
  apply MonoidHom.mulExact_iff.mpr
  rw [absoluteToMaxEverywhereUnramifiedProP_ker]
  exact (Subgroup.range_subtype (absoluteUnramifiedKernel F p).toSubgroup).symm

/-- Algebraic quotient equivalence induced by absolute restriction. -/
noncomputable def absoluteUnramifiedQuotientMulEquiv :
    Field.absoluteGaloisGroup F ⧸
        (absoluteUnramifiedKernel F p).toSubgroup ≃*
      MaxEverywhereUnramifiedProPGaloisGroup F p :=
  QuotientGroup.liftEquiv
    (absoluteUnramifiedKernel F p).toSubgroup
    (absoluteToMaxEverywhereUnramifiedProP_surjective F p)
    (absoluteToMaxEverywhereUnramifiedProP_ker F p).symm

/-- The quotient equivalence sends the class of an absolute automorphism to its restriction. -/
@[simp]
theorem absoluteUnramifiedQuotientMulEquiv_mk
    (σ : Field.absoluteGaloisGroup F) :
    absoluteUnramifiedQuotientMulEquiv F p (QuotientGroup.mk σ) =
      absoluteToMaxEverywhereUnramifiedProP F p σ :=
  rfl

/-- The algebraic quotient equivalence is continuous. -/
theorem absoluteUnramifiedQuotientMulEquiv_continuous :
    Continuous (absoluteUnramifiedQuotientMulEquiv F p) := by
  apply (QuotientGroup.isQuotientMap_mk
    (absoluteUnramifiedKernel F p).toSubgroup).continuous_iff.2
  refine (absoluteToMaxEverywhereUnramifiedProP F p).continuous.congr ?_
  intro σ
  exact (absoluteUnramifiedQuotientMulEquiv_mk F p σ).symm

/-- The quotient of the absolute Galois group by the closed fixing subgroup is continuously
equivalent to the maximal everywhere-unramified pro-`p` Galois group. -/
noncomputable def absoluteUnramifiedQuotientContinuousMulEquiv :
    Field.absoluteGaloisGroup F ⧸
        (absoluteUnramifiedKernel F p).toSubgroup ≃ₜ*
      MaxEverywhereUnramifiedProPGaloisGroup F p := by
  let h := Continuous.homeoOfEquivCompactToT2
    (absoluteUnramifiedQuotientMulEquiv_continuous F p)
  exact
    { toMulEquiv := absoluteUnramifiedQuotientMulEquiv F p
      continuous_toFun := h.continuous
      continuous_invFun := h.symm.continuous }

end ClassFieldTower.Martinet.Shafarevich
