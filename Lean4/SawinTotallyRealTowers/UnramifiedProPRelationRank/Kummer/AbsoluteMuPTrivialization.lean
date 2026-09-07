import GaloisCohomology.ProP.TrivialZModP
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTopRep
import GaloisCohomology.Kummer.Concrete.FiniteDualSeparation

set_option autoImplicit false
/-!
# Trivializing natural `mu_p` coefficients over a cyclotomic base

When the base field contains a primitive `p`-th root of unity, the natural
absolute-Galois action on `mu_p` is trivial.  A chosen primitive root gives a
continuous `ZMod p`-linear equivalence with the standard trivial coefficient
line and hence an isomorphism of topological representations.
-/

open CategoryTheory
open scoped Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology
open ContRepresentation KummerTheory TopRep

variable (K : Type) [Field K]
variable (p : ℕ) [Fact p.Prime]

/-- The natural Galois action on `mu_p` is trivial when the base field already
contains a primitive `p`-th root. -/
theorem absoluteMuPAction_eq_self_of_primitiveRoots
    (hmu : (primitiveRoots p K).Nonempty)
    (sigma : Field.absoluteGaloisGroup K) (x : AbsoluteMuP K p) :
    absoluteMuPActionContinuousLinearMap K p sigma x = x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact nthRootsOfUnity_fixed
    (K := K) (L := AlgebraicClosure K)
    (p.toPNat (Fact.out : p.Prime).pos)
    (nthRootsOfUnityInBase_of_primitiveRoots
      (K := K) (L := AlgebraicClosure K)
      (p.toPNat (Fact.out : p.Prime).pos) hmu)
    (absoluteGaloisGroupContinuousMulEquiv K sigma)
    x.toMul.1 x.toMul.2

/-- The coefficient equivalence from roots of unity in the algebraic closure
to the multiplicative copy of `ZMod p`, using the supplied primitive root. -/
noncomputable def absoluteMuPMulEquivMultiplicativeZMod
    (hmu : (primitiveRoots p K).Nonempty) :
    DiscreteNthRootsSubgroup (AlgebraicClosure K) p ≃*
      Multiplicative (ZMod p) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let zeta : K := hmu.choose
  let hzeta : IsPrimitiveRoot zeta p :=
    (mem_primitiveRoots (Fact.out : p.Prime).pos).mp hmu.choose_spec
  let hzetaUnit := hzeta.isUnit_unit' (Fact.out : p.Prime).ne_zero
  exact
    (nthRootsSubgroupEquivOfPrimitiveRoots K (AlgebraicClosure K)
      (p.toPNat (Fact.out : p.Prime).pos) hmu).symm |>.trans
      ((nthRootsSubgroupEquivRootsOfUnity K p).trans
        ((MulEquiv.subgroupCongr hzetaUnit.zpowers_eq.symm).trans
          hzetaUnit.zmodEquivZPowers.symm.toMultiplicativeRight))

/-- Additive roots of unity are linearly equivalent to the standard
`ZMod p` coefficient line. -/
noncomputable def absoluteMuPLinearEquivZMod
    (hmu : (primitiveRoots p K).Nonempty) :
    AbsoluteMuP K p ≃ₗ[ZMod p] ZMod p := by
  let e := absoluteMuPMulEquivMultiplicativeZMod K p hmu
  let f : AbsoluteMuP K p ≃+ ZMod p :=
    { toFun := fun x ↦ (e x.toMul).toAdd
      invFun := fun a ↦ Additive.ofMul (e.symm (Multiplicative.ofAdd a))
      left_inv := fun x ↦ by
        apply Additive.toMul.injective
        exact e.symm_apply_apply x.toMul
      right_inv := fun a ↦ by
        apply Multiplicative.ofAdd.injective
        exact e.apply_symm_apply (Multiplicative.ofAdd a)
      map_add' := fun x y ↦ by
        apply Multiplicative.ofAdd.injective
        exact e.map_mul x.toMul y.toMul }
  exact { f with map_smul' := ZMod.map_smul f }

/-- The coefficient trivialization is a homeomorphism because both
coefficient spaces are discrete. -/
noncomputable def absoluteMuPContinuousLinearEquivZMod
    (hmu : (primitiveRoots p K).Nonempty) :
    AbsoluteMuP K p ≃L[ZMod p] ZMod p :=
  { toLinearEquiv := absoluteMuPLinearEquivZMod K p hmu
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

/-- Over a field containing `mu_p`, the natural coefficient representation is
isomorphic to the standard trivial `ZMod p` representation. -/
noncomputable def absoluteMuPTopRepTrivialIso
    (hmu : (primitiveRoots p K).Nonempty) :
    absoluteMuPTopRep K p ≅
      trivialZModP p (Field.absoluteGaloisGroup K) := by
  let e := absoluteMuPContinuousLinearEquivZMod K p hmu
  let hom : absoluteMuPTopRep K p ⟶
      trivialZModP p (Field.absoluteGaloisGroup K) := by
    apply TopRep.ofHom
    exact
      { toContinuousLinearMap := e.toContinuousLinearMap
        isIntertwining' := by
          intro sigma
          apply ContinuousLinearMap.ext
          intro x
          change e (absoluteMuPActionContinuousLinearMap K p sigma x) = e x
          rw [absoluteMuPAction_eq_self_of_primitiveRoots K p hmu] }
  let inv : trivialZModP p (Field.absoluteGaloisGroup K) ⟶
      absoluteMuPTopRep K p := by
    apply TopRep.ofHom
    exact
      { toContinuousLinearMap := e.symm.toContinuousLinearMap
        isIntertwining' := by
          intro sigma
          apply ContinuousLinearMap.ext
          intro x
          change e.symm x =
            absoluteMuPActionContinuousLinearMap K p sigma (e.symm x)
          rw [absoluteMuPAction_eq_self_of_primitiveRoots K p hmu] }
  exact
    { hom := hom
      inv := inv
      hom_inv_id := by
        apply TopRep.hom_ext
        apply ContIntertwiningMap.ext
        apply ContinuousLinearMap.ext
        intro x
        exact e.symm_apply_apply x
      inv_hom_id := by
        apply TopRep.hom_ext
        apply ContIntertwiningMap.ext
        apply ContinuousLinearMap.ext
        intro x
        exact e.apply_symm_apply x }

end ClassFieldTower.Martinet.Shafarevich
