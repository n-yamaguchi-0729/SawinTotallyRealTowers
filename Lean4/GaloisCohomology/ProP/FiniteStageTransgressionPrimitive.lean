import GaloisCohomology.ProP.FiniteStageTransgression

set_option autoImplicit false
/-!
# Primitives for inflated finite-stage transgression

If an inflated finite-stage transgression class vanishes, its explicit homogeneous cocycle is a
boundary.  This file extracts a degree-one primitive and records its normalized coboundary
identity.  The residue correction and continuous kernel extension are built in the downstream
kernel module.
-/

open CategoryTheory TopRep ContRepresentation
open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.ProC
open ClassFieldTower.Cohomology

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

local instance finiteStagePrimitiveTargetTopology
    (R : ClosedSubgroup F)
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    TopologicalSpace
      ((F ⧸ (U.1 : Subgroup F)) ⧸ finiteStageImage R U) := ⊥

local instance finiteStagePrimitiveTargetDiscrete
    (R : ClosedSubgroup F)
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    DiscreteTopology
      ((F ⧸ (U.1 : Subgroup F)) ⧸ finiteStageImage R U) :=
  discreteTopology_bot _

theorem inflatedTransgressionCochain_apply
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (χbar : MonoidHom (finiteStageImage R U) (Multiplicative (ZMod p)))
    (a b c : F ⧸ (R : Subgroup F)) :
    (((trivialZModPCochainsMapLifted p (finiteStageQuotientMap R U)).f 2).hom
      (transgressionHomogeneousCochain (finiteStageImage R U) χbar)).1 a b c =
        ULift.up (transgressionFactor (finiteStageImage R U) χbar
          (finiteStageQuotientMap R U (a⁻¹ * b))
          (finiteStageQuotientMap R U (b⁻¹ * c))) := by
  change (transgressionHomogeneousCochain (finiteStageImage R U) χbar).1
    (finiteStageQuotientMap R U a) (finiteStageQuotientMap R U b)
      (finiteStageQuotientMap R U c) = _
  rw [transgressionHomogeneousCochain_apply]
  apply ULift.ext
  simp only [map_mul, map_inv]

/-- The normalized value of a degree-one cochain on the original quotient. -/
def inflatedPrimitiveValue
    (R : ClosedSubgroup F) [R.Normal]
    (c : (trivialZModPCochainsLifted p (F ⧸ (R : Subgroup F))).X 1)
    (q : F ⧸ (R : Subgroup F)) : ZMod p :=
  (c.1 1 q).down

omit [Fact p.Prime] in
theorem inflatedHomogeneousOneCochain_invariant
    (R : ClosedSubgroup F) [R.Normal]
    (c : (trivialZModPCochainsLifted p (F ⧸ (R : Subgroup F))).X 1)
    (a q r : F ⧸ (R : Subgroup F)) :
    c.1 (a⁻¹ * q) (a⁻¹ * r) = c.1 q r := by
  have hc := c.2 a
  have hcr := congrArg (fun τ ↦ τ q r) hc
  have hcr' :
      (trivialZModPLifted p (F ⧸ (R : Subgroup F))).ρ a
          (c.1 (a⁻¹ * q) (a⁻¹ * r)) = c.1 q r := by
    simpa only [ContRepresentation.coind₁_apply_apply] using hcr
  exact (trivialZModPLifted_action p (F ⧸ (R : Subgroup F)) a _).symm.trans hcr'

theorem homogeneousOneCochainNormalizedValue_inflated_primitive
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (χbar : MonoidHom (finiteStageImage R U) (Multiplicative (ZMod p)))
    (c : (trivialZModPCochainsLifted p (F ⧸ (R : Subgroup F))).X 1)
    (hc : ((trivialZModPCochainsLifted p
      (F ⧸ (R : Subgroup F))).d 1 2).hom c =
        (((trivialZModPCochainsMapLifted p (finiteStageQuotientMap R U)).f 2).hom
          (transgressionHomogeneousCochain (finiteStageImage R U) χbar)))
    (q r : F ⧸ (R : Subgroup F)) :
    inflatedPrimitiveValue R c r -
        inflatedPrimitiveValue R c (q * r) +
          inflatedPrimitiveValue R c q =
      transgressionFactor (finiteStageImage R U) χbar
        (finiteStageQuotientMap R U q) (finiteStageQuotientMap R U r) := by
  have hd := TopRep.homogeneousCochains.d_apply
    (trivialZModPLifted (p := p) (F ⧸ (R : Subgroup F))) 1 c
  have hdpoint := congrArg (fun τ ↦ τ 1 q (q * r)) hd
  have hcpoint := congrArg (fun τ ↦ τ.1 1 q (q * r)) hc
  rw [hdpoint] at hcpoint
  simp [TopRep.d_succ, TopRep.d_zero, TopRep.hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun] at hcpoint
  have hinv := inflatedHomogeneousOneCochain_invariant R c q q (q * r)
  have hinv' : c.1 q (q * r) = c.1 1 r := by
    convert hinv.symm using 1
    all_goals group
  rw [hinv'] at hcpoint
  have htrans :
      (((trivialZModPCochainsMapLifted p (finiteStageQuotientMap R U)).f 2).hom
          (transgressionHomogeneousCochain (finiteStageImage R U) χbar)).1
            1 q (q * r) =
        ULift.up (transgressionFactor (finiteStageImage R U) χbar
          (finiteStageQuotientMap R U q) (finiteStageQuotientMap R U r)) := by
    rw [inflatedTransgressionCochain_apply]
    congr 2
    · simp
    · exact congrArg (finiteStageQuotientMap R U) (by group)
  rw [htrans] at hcpoint
  let e : ULift.{u} (ZMod p) ≃ₗ[ZMod p] ZMod p := ULift.moduleEquiv
  change e (c.1 1 r) - e (c.1 1 (q * r)) + e (c.1 1 q) =
    transgressionFactor (finiteStageImage R U) χbar
      (finiteStageQuotientMap R U q) (finiteStageQuotientMap R U r)
  calc
    e (c.1 1 r) - e (c.1 1 (q * r)) + e (c.1 1 q) =
        e (c.1 1 r) - (e (c.1 1 (q * r)) - e (c.1 1 q)) := by abel
    _ = e (c.1 1 r) - e (c.1 1 (q * r) - c.1 1 q) :=
      congrArg (fun t ↦ e (c.1 1 r) - t)
        (e.map_sub (c.1 1 (q * r)) (c.1 1 q)).symm
    _ = e (c.1 1 r - (c.1 1 (q * r) - c.1 1 q)) :=
      (e.map_sub (c.1 1 r) (c.1 1 (q * r) - c.1 1 q)).symm
    _ = e (ULift.up (transgressionFactor (finiteStageImage R U) χbar
        (finiteStageQuotientMap R U q) (finiteStageQuotientMap R U r))) :=
      congrArg e hcpoint
    _ = transgressionFactor (finiteStageImage R U) χbar
        (finiteStageQuotientMap R U q) (finiteStageQuotientMap R U r) := rfl

theorem exists_primitive_of_inflatedFiniteTransgressionClass_eq_zero
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (χbar : MonoidHom (finiteStageImage R U) (Multiplicative (ZMod p)))
    (hχbar : ∀ (g : F ⧸ (U.1 : Subgroup F)) (n : finiteStageImage R U),
      χbar (MulAut.conjNormal g n) = χbar n)
    (hzero : inflatedFiniteTransgressionClass R U χbar hχbar = 0) :
    ∃ c : (trivialZModPCochainsLifted p (F ⧸ (R : Subgroup F))).X 1,
      ((trivialZModPCochainsLifted p (F ⧸ (R : Subgroup F))).d 1 2).hom c =
        (((trivialZModPCochainsMapLifted p (finiteStageQuotientMap R U)).f 2).hom
          (transgressionHomogeneousCochain (finiteStageImage R U) χbar)) := by
  let zstage := transgressionHomogeneousCocycle
    (finiteStageImage R U) χbar hχbar
  let zinfl := (trivialZModPCocyclesMapLifted p
    (finiteStageQuotientMap R U) 2).hom zstage
  have hzinflzero :
      (ContinuousCohomology.π
        (trivialZModPLifted p (F ⧸ (R : Subgroup F))) 2).hom zinfl = 0 := by
    have hnat := ConcreteCategory.congr_hom
      (trivialZModPLifted_π_naturality p (finiteStageQuotientMap R U) 2) zstage
    change (ConcreteCategory.hom
      (trivialZModPCocyclesMapLifted p (finiteStageQuotientMap R U) 2 ≫
        ContinuousCohomology.π
          (trivialZModPLifted p (F ⧸ (R : Subgroup F))) 2)) zstage = 0
    rw [← hnat]
    exact hzero
  obtain ⟨c, hc⟩ := exists_boundary_of_homologyπ_apply_eq_zero
    (trivialZModPLifted p (F ⧸ (R : Subgroup F))) 1 zinfl hzinflzero
  refine ⟨c, hc.trans ?_⟩
  have hmap := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (trivialZModPCochainsMapLifted p (finiteStageQuotientMap R U)) 2) zstage
  change ((trivialZModPCochainsLifted p (F ⧸ (R : Subgroup F))).iCycles 2).hom
      zinfl =
    (((trivialZModPCochainsMapLifted p (finiteStageQuotientMap R U)).f 2).hom
      (transgressionHomogeneousCochain (finiteStageImage R U) χbar))
  change ((trivialZModPCochainsLifted p (F ⧸ (R : Subgroup F))).iCycles 2).hom
      ((trivialZModPCocyclesMapLifted p (finiteStageQuotientMap R U) 2).hom zstage) = _
  rw [← ConcreteCategory.comp_apply]
  rw [HomologicalComplex.cyclesMap_i]
  rw [ConcreteCategory.comp_apply]
  exact congrArg
    (fun x ↦ (((trivialZModPCochainsMapLifted p
      (finiteStageQuotientMap R U)).f 2).hom x))
    (iCycles_transgressionHomogeneousCocycle
      (finiteStageImage R U) χbar hχbar)

end

end ClassFieldTower.ProP
