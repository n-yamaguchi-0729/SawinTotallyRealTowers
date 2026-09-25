/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.Cohomology.ContinuousMapFiniteStage
import GaloisCohomology.ProP.PresentationH2Primitive
import GaloisCohomology.ProP.FiniteTransgression
import Mathlib.Tactic.FinCases

set_option autoImplicit false
/-!
# Finite-stage realization of continuous degree-two classes
-/

open scoped Topology

namespace ClassFieldTower.Cohomology

namespace H2FiniteStageAux

open CategoryTheory TopRep ContRepresentation
open ProCGroups ProCGroups.ProC

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- A universe-compatible three-element coordinate type. -/
abbrev Coordinate := ULift.{u} (Fin 3)

/-- The threefold product used to factor a homogeneous two-cocycle. -/
abbrev Triple (G : Type u) := Coordinate → G

/-- Include a small coordinate into the universe-lifted coordinate type. -/
def coordinateIndex (i : Fin 3) : Coordinate := ULift.up i

/-- Assemble three entries as an element of the threefold product. -/
def triple (a b c : G) : Triple G :=
  fun i => if i.down = 0 then a else if i.down = 1 then b else c

/-- The continuous homomorphism supported at one coordinate. -/
def coordinateHom (i : Coordinate) : G →ₜ* Triple G where
  toMonoidHom := MonoidHom.mulSingle (fun _ : Coordinate => G) i
  continuous_toFun := by
    change Continuous fun g : G => (Pi.mulSingle i g : Triple G)
    exact continuous_mulSingle (A := fun _ : Coordinate => G) i

/-- Pull an in-class open normal subgroup back along one coordinate inclusion. -/
noncomputable def coordinateSubgroup
    (W : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) (Triple G))
    (i : Coordinate) :
    OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G :=
  OpenNormalSubgroupInClass.comap
    (FiniteGroupClass.pGroup_hereditary p) (coordinateHom i) W

/-- A common in-class open normal subgroup for all three coordinates. -/
noncomputable def commonCoordinateSubgroup
    (W : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) (Triple G)) :
    OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G :=
  OpenNormalSubgroupInClass.inf (FiniteGroupClass.pGroup_formation p)
    (coordinateSubgroup W (coordinateIndex 0))
    (OpenNormalSubgroupInClass.inf (FiniteGroupClass.pGroup_formation p)
      (coordinateSubgroup W (coordinateIndex 1))
      (coordinateSubgroup W (coordinateIndex 2)))

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G] in
theorem commonCoordinateSubgroup_le
    (W : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) (Triple G))
    (i : Fin 3) :
    ((commonCoordinateSubgroup W).1 : Subgroup G) ≤
      ((coordinateSubgroup W (coordinateIndex i)).1 : Subgroup G) := by
  fin_cases i
  · exact inf_le_left
  · exact inf_le_right.trans inf_le_left
  · exact inf_le_right.trans inf_le_right

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G] in
theorem mulSingle_mem_of_mem_common
    (W : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) (Triple G))
    (i : Fin 3) {g : G}
    (hg : g ∈ ((commonCoordinateSubgroup W).1 : Subgroup G)) :
    Pi.mulSingle (coordinateIndex i) g ∈ (W.1 : Subgroup (Triple G)) := by
  have hi := commonCoordinateSubgroup_le W i hg
  change coordinateHom (coordinateIndex i) g ∈ (W.1 : Subgroup (Triple G))
  simpa [coordinateSubgroup, OpenNormalSubgroupInClass.comap] using hi

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G] in
theorem map_eq_of_coordinate_quotients
    (W : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) (Triple G))
    (rho : Triple G → ULift.{u} (ZMod p))
    (rhoW : (Triple G ⧸ (W.1 : Subgroup (Triple G))) → ULift.{u} (ZMod p))
    (hfac : rho = rhoW ∘ OpenNormalSubgroupInClass.quotientProj W)
    (a b : Triple G)
    (hab : ∀ i : Fin 3, OpenNormalSubgroupInClass.quotientProj
        (commonCoordinateSubgroup W) (a (coordinateIndex i)) =
      OpenNormalSubgroupInClass.quotientProj
        (commonCoordinateSubgroup W) (b (coordinateIndex i))) :
    rho a = rho b := by
  rw [congrFun hfac a, congrFun hfac b]
  apply congrArg rhoW
  apply OpenNormalSubgroupInClass.quotientProj_eq_quotientProj_iff.mpr
  have hi (i : Fin 3) :
      Pi.mulSingle (coordinateIndex i)
        (a (coordinateIndex i) / b (coordinateIndex i)) ∈
          (W.1 : Subgroup (Triple G)) := by
    apply mulSingle_mem_of_mem_common W i
    exact OpenNormalSubgroupInClass.quotientProj_eq_quotientProj_iff.mp (hab i)
  have hprod := (W.1 : Subgroup (Triple G)).mul_mem
    ((W.1 : Subgroup (Triple G)).mul_mem (hi 0) (hi 1)) (hi 2)
  convert hprod using 1
  ext i
  rcases i with ⟨i⟩
  fin_cases i <;> simp [coordinateIndex]

/-- Evaluate a homogeneous two-cocycle on three elements. -/
def cocycleValue
    (z : trivialZModPCocyclesLifted p G 2) (a b c : G) :
    ULift.{u} (ZMod p) :=
  (((trivialZModPCochainsLifted p G).iCycles 2).hom z).1 a b c

/-- Regard a homogeneous two-cocycle as a finite-valued map on a threefold product. -/
def cocycleTupleMap
    (z : trivialZModPCocyclesLifted p G 2) (a : Triple G) :
    ULift.{u} (ZMod p) :=
  cocycleValue z (a (coordinateIndex 0))
    (a (coordinateIndex 1)) (a (coordinateIndex 2))

omit [Fact p.Prime] [T2Space G] [TotallyDisconnectedSpace G] in
theorem cocycleTupleMap_continuous
    (z : trivialZModPCocyclesLifted p G 2) :
    Continuous (cocycleTupleMap z) := by
  let X := trivialZModPLifted p G
  let z₀ := ((trivialZModPCochainsLifted p G).iCycles 2).hom z
  change (TopRep.resolutionX X 3).ρ.invariants at z₀
  let zfun : C(G, C(G, C(G, ULift.{u} (ZMod p)))) := z₀.1
  change Continuous fun a : Triple G =>
    zfun (a (coordinateIndex 0)) (a (coordinateIndex 1)) (a (coordinateIndex 2))
  fun_prop

omit [Fact p.Prime] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem cocycleTupleMap_leftInvariant
    (z : trivialZModPCocyclesLifted p G 2) (g a b c : G) :
    cocycleTupleMap z (triple (g⁻¹ * a) (g⁻¹ * b) (g⁻¹ * c)) =
      cocycleTupleMap z (triple a b c) := by
  let X := trivialZModPLifted p G
  let z₀ := ((trivialZModPCochainsLifted p G).iCycles 2).hom z
  change (TopRep.resolutionX X 3).ρ.invariants at z₀
  have h := congrArg (fun τ => τ a b c) (z₀.2 g)
  change cocycleValue z (g⁻¹ * a) (g⁻¹ * b) (g⁻¹ * c) =
    cocycleValue z a b c at h
  simpa [cocycleTupleMap, cocycleValue, triple, coordinateIndex, X, z₀,
    coind₁_apply_apply, trivialZModPLifted_action] using h

/-- A chosen set-theoretic section of an open-normal quotient projection. -/
noncomputable def quotientSection
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    (G ⧸ (U.1 : Subgroup G)) → G :=
  Function.surjInv (OpenNormalSubgroupInClass.quotientProj_surjective U)

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G] in
@[simp]
theorem quotientProj_quotientSection
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (q : G ⧸ (U.1 : Subgroup G)) :
    OpenNormalSubgroupInClass.quotientProj U (quotientSection U q) = q :=
  Function.rightInverse_surjInv
    (OpenNormalSubgroupInClass.quotientProj_surjective U) q

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G] in
theorem quotientProj_quotientSection_inv_mul
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (q r : G ⧸ (U.1 : Subgroup G)) :
    OpenNormalSubgroupInClass.quotientProj U (quotientSection U (q⁻¹ * r)) =
      OpenNormalSubgroupInClass.quotientProj U
        ((quotientSection U q)⁻¹ * quotientSection U r) := by
  rw [quotientProj_quotientSection]
  simp only [map_mul, map_inv, quotientProj_quotientSection]

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G] in
theorem quotientProj_quotientSection_proj
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) (g : G) :
    OpenNormalSubgroupInClass.quotientProj U
        (quotientSection U (OpenNormalSubgroupInClass.quotientProj U g)) =
      OpenNormalSubgroupInClass.quotientProj U g :=
  quotientProj_quotientSection U _

/-- Descend a homogeneous cocycle cochain through a common coordinate quotient. -/
noncomputable def descendedHomogeneousCochain
    (W : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) (Triple G))
    (z : trivialZModPCocyclesLifted p G 2)
    (heq : ∀ a b : Triple G,
      (∀ i : Fin 3, OpenNormalSubgroupInClass.quotientProj
          (commonCoordinateSubgroup W) (a (coordinateIndex i)) =
        OpenNormalSubgroupInClass.quotientProj
          (commonCoordinateSubgroup W) (b (coordinateIndex i))) →
      cocycleTupleMap z a = cocycleTupleMap z b) :
    (trivialZModPCochainsLifted p
      (G ⧸ ((commonCoordinateSubgroup W).1 : Subgroup G))).X 2 := by
  let U := commonCoordinateSubgroup W
  let Q := G ⧸ (U.1 : Subgroup G)
  letI : DiscreteTopology Q :=
    QuotientGroup.discreteTopology (openNormalSubgroup_isOpen (G := G) U.1)
  let s := quotientSection U
  let σ : C(Q, C(Q, C(Q, ULift.{u} (ZMod p)))) :=
    ⟨fun a => ⟨fun b => ⟨fun c => cocycleTupleMap z (triple (s a) (s b) (s c)),
      continuous_of_discreteTopology⟩, continuous_of_discreteTopology⟩,
      continuous_of_discreteTopology⟩
  exact ⟨σ, by
    intro g
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro b
    apply ContinuousMap.ext
    intro c
    change cocycleTupleMap z
        (triple (s (g⁻¹ * a)) (s (g⁻¹ * b)) (s (g⁻¹ * c))) =
      cocycleTupleMap z (triple (s a) (s b) (s c))
    calc
      _ = cocycleTupleMap z
          (triple ((s g)⁻¹ * s a) ((s g)⁻¹ * s b) ((s g)⁻¹ * s c)) := by
        apply heq
        intro i
        fin_cases i
        · simpa [triple, coordinateIndex, s, U] using
            quotientProj_quotientSection_inv_mul
              (commonCoordinateSubgroup W) g a
        · simpa [triple, coordinateIndex, s, U] using
            quotientProj_quotientSection_inv_mul
              (commonCoordinateSubgroup W) g b
        · simpa [triple, coordinateIndex, s, U] using
            quotientProj_quotientSection_inv_mul
              (commonCoordinateSubgroup W) g c
      _ = _ := cocycleTupleMap_leftInvariant z (s g) (s a) (s b) (s c)⟩

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem descendedHomogeneousCochain_mem_cycles
    (W : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) (Triple G))
    (z : trivialZModPCocyclesLifted p G 2)
    (heq : ∀ a b : Triple G,
      (∀ i : Fin 3, OpenNormalSubgroupInClass.quotientProj
          (commonCoordinateSubgroup W) (a (coordinateIndex i)) =
        OpenNormalSubgroupInClass.quotientProj
          (commonCoordinateSubgroup W) (b (coordinateIndex i))) →
      cocycleTupleMap z a = cocycleTupleMap z b) :
    ((trivialZModPCochainsLifted p
      (G ⧸ ((commonCoordinateSubgroup W).1 : Subgroup G))).d 2 3).hom
        (descendedHomogeneousCochain W z heq) = 0 := by
  let : DiscreteTopology
      (G ⧸ ((commonCoordinateSubgroup W).1 : Subgroup G)) :=
    QuotientGroup.discreteTopology
      (openNormalSubgroup_isOpen (G := G) (commonCoordinateSubgroup W).1)
  change _ = (0 : (TopRep.resolutionX (trivialZModPLifted p
    (G ⧸ ((commonCoordinateSubgroup W).1 : Subgroup G))) 4).ρ.invariants)
  apply Subtype.ext
  ext a b c d
  have hd := TopRep.homogeneousCochains.d_apply
    (trivialZModPLifted p
      (G ⧸ ((commonCoordinateSubgroup W).1 : Subgroup G))) 2
      (descendedHomogeneousCochain W z heq)
  have hdabcd := congrArg (fun τ => τ a b c d) hd
  rw [hdabcd]
  simp [TopRep.d_succ, TopRep.d_zero, TopRep.hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun]
  change cocycleTupleMap z
      (triple (quotientSection (commonCoordinateSubgroup W) b)
        (quotientSection (commonCoordinateSubgroup W) c)
        (quotientSection (commonCoordinateSubgroup W) d)) -
    (cocycleTupleMap z
      (triple (quotientSection (commonCoordinateSubgroup W) a)
        (quotientSection (commonCoordinateSubgroup W) c)
        (quotientSection (commonCoordinateSubgroup W) d)) -
    (cocycleTupleMap z
      (triple (quotientSection (commonCoordinateSubgroup W) a)
        (quotientSection (commonCoordinateSubgroup W) b)
        (quotientSection (commonCoordinateSubgroup W) d)) -
    cocycleTupleMap z
      (triple (quotientSection (commonCoordinateSubgroup W) a)
        (quotientSection (commonCoordinateSubgroup W) b)
        (quotientSection (commonCoordinateSubgroup W) c)))) = 0
  have h := ProP.PresentationH2Aux.homogeneousTwoCocycleEquation z
    (quotientSection (commonCoordinateSubgroup W) a)
    (quotientSection (commonCoordinateSubgroup W) b)
    (quotientSection (commonCoordinateSubgroup W) c)
    (quotientSection (commonCoordinateSubgroup W) d)
  change cocycleTupleMap z
        (triple (quotientSection (commonCoordinateSubgroup W) b)
          (quotientSection (commonCoordinateSubgroup W) c)
          (quotientSection (commonCoordinateSubgroup W) d)) -
      cocycleTupleMap z
        (triple (quotientSection (commonCoordinateSubgroup W) a)
          (quotientSection (commonCoordinateSubgroup W) c)
          (quotientSection (commonCoordinateSubgroup W) d)) +
      cocycleTupleMap z
        (triple (quotientSection (commonCoordinateSubgroup W) a)
          (quotientSection (commonCoordinateSubgroup W) b)
          (quotientSection (commonCoordinateSubgroup W) d)) -
      cocycleTupleMap z
        (triple (quotientSection (commonCoordinateSubgroup W) a)
          (quotientSection (commonCoordinateSubgroup W) b)
          (quotientSection (commonCoordinateSubgroup W) c)) = 0 at h
  abel_nf at h ⊢
  exact h

end

end H2FiniteStageAux

end ClassFieldTower.Cohomology
