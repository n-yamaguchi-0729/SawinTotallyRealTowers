import GaloisCohomology.Kummer.FiniteKummerCoefficientH2
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SupportedBridge

set_option autoImplicit false
/-!
# Root-of-unity coefficients are integral at every finite place

A torsion field unit has valuation one at every finite place. Its
principal relative idele therefore lies in the actual empty-support
subgroup. This gives the supported coefficient map needed to apply the
unramified local-to-global primitive construction.
-/

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

/-- A torsion field unit gives a principal idele integral at every finite place. -/
theorem principalIdele_mem_emptySupport_of_pow_eq_one
    (n : ℕ) (hn : n ≠ 0) (x : Lˣ) (hx : x ^ n = 1) :
    RelativeIdeleGroup.principalIdele K L x ∈
      relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) ∅ := by
  apply (relativeIdeleBaseChange_mem_supportedAt_iff (K := K) (L := L) ∅ _).2
  rw [relativeIdeleBaseChangeMulEquiv_principalIdele]
  apply (principalIdele_mem_supportedAt_iff_sUnit (L := L) _ x).2
  intro v _hv
  apply (pow_eq_one_iff_left hn).mp
  have hxL : (x : L) ^ n = 1 := congrArg Units.val hx
  rw [← map_pow, hxL, map_one]

variable (p : ℕ+)

/-- The actual principal idele of a Kummer coefficient has empty finite support. -/
theorem finiteKummerCoefficient_principalIdele_mem_emptySupport
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (z : ULift (ZMod (p : ℕ))) :
    RelativeIdeleGroup.principalIdele K L
        (finiteKummerCoefficientAddHom K L p hmu z).toMul ∈
      relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) ∅ :=
  principalIdele_mem_emptySupport_of_pow_eq_one K L p p.ne_zero _
    (finiteKummerCoefficientAddHom_pow_eq_one K L p hmu z)

/-- Finite Kummer coefficients mapped into the actual empty-support idele subgroup. -/
def finiteKummerSupportedIdeleAddHom
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) :
    ULift.{0} (ZMod (p : ℕ)) →+
      Additive (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) ∅) where
  toFun z := Additive.ofMul ⟨RelativeIdeleGroup.principalIdele K L
    (finiteKummerCoefficientAddHom K L p hmu z).toMul,
    finiteKummerCoefficient_principalIdele_mem_emptySupport K L p hmu z⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change RelativeIdeleGroup.principalIdele K L
      (finiteKummerCoefficientAddHom K L p hmu (0 : ULift.{0} (ZMod (p : ℕ)))).toMul = 1
    rw [map_zero]
    exact map_one _
  map_add' z w := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change RelativeIdeleGroup.principalIdele K L
      (finiteKummerCoefficientAddHom K L p hmu (z + w)).toMul = _
    rw [map_add]
    exact map_mul _ _ _

local instance finiteRootSupportedIdeleAction : MulDistribMulAction (Gal(L/K))
    (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) ∅) :=
  relativeIdeleLocalTensorDecompositionSupportedSubgroupAction (K := K) (L := L) ∅

/-- The supported coefficient map is equivariant for the actual Galois action. -/
def finiteKummerSupportedIdeleRepHom
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) :
    Rep.trivial ℤ (Gal(L/K)) (ULift (ZMod (p : ℕ))) ⟶
      Rep.ofMulDistribMulAction (Gal(L/K))
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) ∅) := by
  apply Rep.ofHom
  refine ⟨(finiteKummerSupportedIdeleAddHom K L p hmu).toIntLinearMap, ?_⟩
  intro g
  apply LinearMap.ext
  intro z
  apply Additive.toMul.injective
  apply Subtype.ext
  change RelativeIdeleGroup.principalIdele K L
      (finiteKummerCoefficientAddHom K L p hmu z).toMul =
    g • RelativeIdeleGroup.principalIdele K L
      (finiteKummerCoefficientAddHom K L p hmu z).toMul
  rw [RelativeIdeleGroup.smul_principalIdele]
  exact congrArg (fun x : Additive Lˣ => RelativeIdeleGroup.principalIdele K L x.toMul)
    (finiteKummerCoefficientAddHom_fixed K L p hmu g z).symm

end ClassFieldTower.Martinet.Shafarevich

end
