import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity
import ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius
import ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields
import GaloisCohomology.ProfiniteIntegers.ProfiniteInteger
import GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

set_option autoImplicit false

/-!
# Base change of standard unramified degree kernels

If an extension has relative residue degree `f`, then intersecting its
absolute subgroup with the standard unramified degree-`f * m` subgroup
produces its own standard unramified degree-`m` subgroup.  Both sides use
the actual normalized degree maps.
-/

namespace ClassFormation

private theorem zHatReduction_mul_nsmul_eq_zero_iff
    (f m : ℕ) (hf : 0 < f) (hm : 0 < m) (z : ZHat) :
    zHatReduction (f * m) (Nat.mul_pos hf hm) (f • z) = 0 ↔
      zHatReduction m hm z = 0 := by
  constructor
  · intro hz
    have hr : f • z ∈ (zHatMulNat (f * m)).toAddMonoidHom.range := by
      rw [zHatMulNat_range_eq_ker_reduction (f * m) (Nat.mul_pos hf hm)]
      exact hz
    obtain ⟨w, hw⟩ := hr
    change (f * m) • w = f • z at hw
    have heq : zHatMulNat f (m • w) = zHatMulNat f z := by
      simpa only [zHatMulNat_apply, smul_smul] using hw
    have hwz : m • w = z := zHatMulNat_injective hf heq
    have hmemb : z ∈ (zHatMulNat m).toAddMonoidHom.range := ⟨w, hwz⟩
    rw [zHatMulNat_range_eq_ker_reduction m hm] at hmemb
    exact hmemb
  · intro hz
    have hr : z ∈ (zHatMulNat m).toAddMonoidHom.range := by
      rw [zHatMulNat_range_eq_ker_reduction m hm]
      exact hz
    obtain ⟨w, hw⟩ := hr
    change m • w = z at hw
    have hmemb : f • z ∈ (zHatMulNat (f * m)).toAddMonoidHom.range := by
      refine ⟨w, ?_⟩
      change (f * m) • w = f • z
      simpa only [smul_smul] using congrArg (fun x : ZHat => f • x) hw
    rw [zHatMulNat_range_eq_ker_reduction (f * m) (Nat.mul_pos hf hm)] at hmemb
    exact hmemb

namespace DegreeData

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual unramified degree kernels commute with base change after
multiplying the downstairs degree by the relative residue degree. -/
theorem unramifiedExtensionOfDegree_baseChange_mul
    (D : DegreeData G) (E : FiniteResidueAbstractExtension D)
    (m : ℕ) (hm : 0 < m) :
    D.unramifiedExtensionOfDegree E.field m hm =
      E.field.field ⊓ D.unramifiedExtensionOfDegree E.base
        ((E.residueDegree : ℕ) * m) (Nat.mul_pos E.residueDegree.property hm) := by
  ext g
  constructor
  · intro hg
    obtain ⟨l, hl, rfl⟩ :=
      (D.mem_unramifiedExtensionOfDegree_iff E.field m hm g).mp hg
    refine ⟨l.property, ?_⟩
    refine (D.mem_unramifiedExtensionOfDegree_iff E.base
      ((E.residueDegree : ℕ) * m) (Nat.mul_pos E.residueDegree.property hm) l.val).mpr ?_
    refine ⟨Subgroup.inclusion E.below l, ?_, rfl⟩
    change zHatReductionMul ((E.residueDegree : ℕ) * m)
      (Nat.mul_pos E.residueDegree.property hm)
      (D.normalizedDegree E.base (Subgroup.inclusion E.below l)) = 1
    apply Multiplicative.ext
    change zHatReduction ((E.residueDegree : ℕ) * m)
      (Nat.mul_pos E.residueDegree.property hm)
      (D.normalizedDegree E.base (Subgroup.inclusion E.below l)).toAdd = 0
    rw [D.frobeniusRestrictionNaturality_normalizedDegree E l]
    exact (zHatReduction_mul_nsmul_eq_zero_iff
      E.residueDegree m E.residueDegree.property hm
      (D.normalizedDegree E.field l).toAdd).mpr
      (congrArg Multiplicative.toAdd hl)
  · rintro ⟨hgL, hgU⟩
    let l : E.field.toSubgroup := ⟨g, hgL⟩
    obtain ⟨k, hk, hkg⟩ :=
      (D.mem_unramifiedExtensionOfDegree_iff E.base
        ((E.residueDegree : ℕ) * m) (Nat.mul_pos E.residueDegree.property hm) g).mp hgU
    have hkl : k = Subgroup.inclusion E.below l := Subtype.ext hkg
    subst k
    refine (D.mem_unramifiedExtensionOfDegree_iff E.field m hm g).mpr ⟨l, ?_, rfl⟩
    change zHatReductionMul m hm (D.normalizedDegree E.field l) = 1
    apply Multiplicative.ext
    change zHatReduction m hm (D.normalizedDegree E.field l).toAdd = 0
    apply (zHatReduction_mul_nsmul_eq_zero_iff
      E.residueDegree m E.residueDegree.property hm
      (D.normalizedDegree E.field l).toAdd).mp
    rw [← D.frobeniusRestrictionNaturality_normalizedDegree E l]
    exact congrArg Multiplicative.toAdd hk

end DegreeData
end ClassFormation
