/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.ProP.TrivialZModP
public import Nyll.GaloisCohomology.Kummer.AbsoluteMuPTopRep
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteDualSeparation

/-!
# Trivializing natural `mu_p` coefficients over a cyclotomic base

When the base field contains a primitive `p`-th root of unity, the natural
absolute-Galois action on `mu_p` is trivial.  A chosen primitive root gives a
continuous `ZMod p`-linear equivalence with the standard trivial coefficient
line and hence an isomorphism of topological representations.
-/

@[expose] public section

open CategoryTheory
open scoped Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology
open ContRepresentation KummerTheory TopRep

universe u

section General

variable (K : Type u) [Field K]
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
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
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
isomorphic to the same trivial coefficient line lifted to the universe of `K`. -/
noncomputable def absoluteMuPTopRepTrivialIsoLifted
    (hmu : (primitiveRoots p K).Nonempty) :
    absoluteMuPTopRep K p ≅
      trivialZModPLifted p (Field.absoluteGaloisGroup K) := by
  letI : ContinuousSMul (ZMod p) (ULift.{u} (ZMod p)) :=
    ContinuousSMul.induced ULift.moduleEquiv.toLinearMap
  let e : AbsoluteMuP K p ≃L[ZMod p] ULift.{u} (ZMod p) :=
    (absoluteMuPContinuousLinearEquivZMod K p hmu).trans
      (ContinuousLinearEquiv.ulift : ULift.{u} (ZMod p) ≃L[ZMod p] ZMod p).symm
  let hom : absoluteMuPTopRep K p ⟶
      trivialZModPLifted p (Field.absoluteGaloisGroup K) := by
    apply TopRep.ofHom
    exact
      { toContinuousLinearMap := e.toContinuousLinearMap
        isIntertwining' := by
          intro sigma
          apply ContinuousLinearMap.ext
          intro x
          change e (absoluteMuPActionContinuousLinearMap K p sigma x) = e x
          rw [absoluteMuPAction_eq_self_of_primitiveRoots K p hmu] }
  let inv : trivialZModPLifted p (Field.absoluteGaloisGroup K) ⟶
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


/-- The lifted trivialization uses the original chosen-root coefficient value. -/
theorem absoluteMuPTopRepTrivialIsoLifted_hom_apply
    (hmu : (primitiveRoots p K).Nonempty) (x : AbsoluteMuP K p) :
    (absoluteMuPTopRepTrivialIsoLifted K p hmu).hom x =
      ULift.up.{u} (absoluteMuPLinearEquivZMod K p hmu x) := rfl

/-- The inverse removes the explicit lift before applying the same coefficient inverse. -/
theorem absoluteMuPTopRepTrivialIsoLifted_inv_apply
    (hmu : (primitiveRoots p K).Nonempty) (z : ULift.{u} (ZMod p)) :
    (absoluteMuPTopRepTrivialIsoLifted K p hmu).inv z =
      (absoluteMuPLinearEquivZMod K p hmu).symm z.down := rfl

end General

section Small

variable (K : Type) [Field K]
variable (p : ℕ) [Fact p.Prime]

/-- The original small coefficient isomorphism, obtained by removing the explicit lift. -/
noncomputable def absoluteMuPTopRepTrivialIso
    (hmu : (primitiveRoots p K).Nonempty) :
    absoluteMuPTopRep K p ≅
      trivialZModP p (Field.absoluteGaloisGroup K) :=
  absoluteMuPTopRepTrivialIsoLifted K p hmu ≪≫
    trivialZModPLiftedSmallIso p (Field.absoluteGaloisGroup K)

/-- The old small forward map retains exactly its chosen-root value. -/
theorem absoluteMuPTopRepTrivialIso_hom_apply
    (hmu : (primitiveRoots p K).Nonempty) (x : AbsoluteMuP K p) :
    (absoluteMuPTopRepTrivialIso K p hmu).hom x =
      absoluteMuPLinearEquivZMod K p hmu x := rfl

/-- The old small inverse retains exactly its chosen-root value. -/
theorem absoluteMuPTopRepTrivialIso_inv_apply
    (hmu : (primitiveRoots p K).Nonempty) (z : ZMod p) :
    (absoluteMuPTopRepTrivialIso K p hmu).inv z =
      (absoluteMuPLinearEquivZMod K p hmu).symm z := rfl

end Small

end ClassFieldTower.Martinet.Shafarevich
