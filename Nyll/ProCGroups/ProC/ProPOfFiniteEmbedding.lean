/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.Subgroups.Products
import Nyll.ProCGroups.ProC.InverseLimits.Predicates
import Nyll.ProCGroups.FiniteGroups.PGroupFormation
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.LocallyConstant.Basic

/-!
# A compact group separated by continuous finite p-group coordinates

This is the existing product/closed-subgroup permanence argument applied to
an actual continuous injective homomorphism. It requires no surjectivity of
individual coordinates and no inverse-limit identification.
-/

namespace ProCGroups.ProC

universe u

/-- A compact group embedded in a product of actual finite p-groups has an
open-normal basis with finite p-group quotients. -/
theorem hasPGroupOpenNormalBasis_of_finiteCoordinates
    (p : ℕ) [Fact p.Prime]
    (G : GrpCat.{u}) [TopologicalSpace G.carrier] [IsTopologicalGroup G.carrier]
    [CompactSpace G.carrier]
    (ι : Type u) (H : ι → FiniteGrp.{u})
    (f : ∀ i : ι, G.carrier →* (H i).toGrp.carrier)
    (hf : ∀ i : ι, IsLocallyConstant (f i).toFun)
    (hsep : ∀ x y : G.carrier, (∀ i : ι, (f i).toFun x = (f i).toFun y) → x = y)
    (hp : ∀ i : ι, IsPGroup p (H i).toGrp.carrier) :
    HasPGroupOpenNormalBasis p G.carrier := by
  let φ : G.carrier →* ((i : ι) → (ProfiniteGrp.ofFiniteGrp (H i)).toProfinite) :=
    { toFun := fun x i => (f i).toFun x
      map_one' := funext (fun i => (f i).map_one)
      map_mul' := fun x y => funext (fun i => (f i).map_mul x y) }
  have hφ : Continuous φ.toFun := by
    apply continuous_pi
    intro i
    exact IsLocallyConstant.continuous
      (Y := (ProfiniteGrp.ofFiniteGrp (H i)).toProfinite) (hf i)
  have hinj : Function.Injective φ.toFun := by
    intro x y hxy
    exact hsep x y (fun i => congrFun hxy i)
  have hrange : IsClosed (φ.range : Set ((i : ι) →
      (ProfiniteGrp.ofFiniteGrp (H i)).toProfinite)) :=
    (isCompact_range hφ).isClosed
  have hpro : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) φ.range :=
    HasOpenNormalBasisInClass.of_closedSubgroup_pi hrange
      (FiniteGroupClass.pGroup_formation p) (FiniteGroupClass.pGroup_subgroupClosed p)
      (fun i => by
        have hfinite : Finite (ProfiniteGrp.ofFiniteGrp (H i)).toProfinite := (H i).isFinite
        exact HasOpenNormalBasisInClass.of_finite_discrete
          (FiniteGroupClass.pGroup_formation p).quotientClosed ⟨hfinite, hp i⟩)
  let e : G.carrier ≃ₜ* φ.range :=
    ContinuousMulEquiv.ofBijectiveCompactToT2 φ.rangeRestrict
      (hφ.subtype_mk (fun x => ⟨x, rfl⟩))
      ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), φ.rangeRestrict_surjective⟩
  exact HasOpenNormalBasisInClass.ofContinuousMulEquiv hpro e.symm

end ProCGroups.ProC
