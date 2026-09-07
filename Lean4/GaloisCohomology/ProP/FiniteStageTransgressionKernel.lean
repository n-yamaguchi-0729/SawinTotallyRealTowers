import GaloisCohomology.ProP.FiniteStageTransgressionPrimitive

set_option autoImplicit false
/-!
# Kernel exactness for inflated finite-stage transgression

A primitive for a vanishing inflated class is corrected by finite-stage quotient-section residues.
The resulting coboundary datum gives a continuous ambient character extending the original
invariant kernel character.
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

local instance finiteStageKernelTargetTopology
    (R : ClosedSubgroup F)
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    TopologicalSpace
      ((F ⧸ (U.1 : Subgroup F)) ⧸ finiteStageImage R U) := ⊥

local instance finiteStageKernelTargetDiscrete
    (R : ClosedSubgroup F)
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    DiscreteTopology
      ((F ⧸ (U.1 : Subgroup F)) ⧸ finiteStageImage R U) :=
  discreteTopology_bot _

theorem finiteStageQuotientMap_out
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (q : F ⧸ (R : Subgroup F)) :
    QuotientGroup.mk' (finiteStageImage R U)
        (OpenNormalSubgroup.quotientProj U.1 (Quotient.out q)) =
      finiteStageQuotientMap R U q := by
  calc
    QuotientGroup.mk' (finiteStageImage R U)
        (OpenNormalSubgroup.quotientProj U.1 (Quotient.out q)) =
        finiteStageQuotientMap R U
          (QuotientGroup.mk' (R : Subgroup F) (Quotient.out q)) := rfl
    _ = finiteStageQuotientMap R U q :=
      congrArg (finiteStageQuotientMap R U) (QuotientGroup.out_eq' q)

/-- The additive character value of the finite-stage residue of a chosen quotient section. -/
noncomputable def finiteStageSectionResidueValue
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (χbar : MonoidHom (finiteStageImage R U) (Multiplicative (ZMod p)))
    (q : F ⧸ (R : Subgroup F)) : ZMod p :=
  (χbar (quotientSectionResidue (finiteStageImage R U)
    (OpenNormalSubgroup.quotientProj U.1 (Quotient.out q)))).toAdd

theorem quotientSectionResidue_finiteStage_out_mul
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (q r : F ⧸ (R : Subgroup F)) :
    quotientSectionResidue (finiteStageImage R U)
        (OpenNormalSubgroup.quotientProj U.1 (Quotient.out q) *
          OpenNormalSubgroup.quotientProj U.1 (Quotient.out r)) =
      finiteStageImageMap R U (quotientSectionFactor (R : Subgroup F) q r) *
        quotientSectionResidue (finiteStageImage R U)
          (OpenNormalSubgroup.quotientProj U.1 (Quotient.out (q * r))) := by
  apply Subtype.ext
  simp only [quotientSectionResidue_apply, map_mul, finiteStageImageMap,
    quotientSectionFactor_apply, Subgroup.coe_mul, MonoidHom.coe_mk,
    OneHom.coe_mk]
  rw [finiteStageQuotientMap_out, finiteStageQuotientMap_out,
    finiteStageQuotientMap_out]
  simp

theorem quotientSectionResidue_finiteStage_decomposition
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (g : F) :
    quotientSectionResidue (finiteStageImage R U)
        (OpenNormalSubgroup.quotientProj U.1 g) =
      finiteStageImageMap R U
          (quotientSectionResidue (R : Subgroup F) g) *
        quotientSectionResidue (finiteStageImage R U)
          (OpenNormalSubgroup.quotientProj U.1
            (Quotient.out (QuotientGroup.mk' (R : Subgroup F) g))) := by
  apply Subtype.ext
  simp only [quotientSectionResidue_apply, finiteStageImageMap,
    Subgroup.coe_mul, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_inv]
  rw [show QuotientGroup.mk' (finiteStageImage R U)
      (OpenNormalSubgroup.quotientProj U.1 g) =
        finiteStageQuotientMap R U
          (QuotientGroup.mk' (R : Subgroup F) g) by rfl]
  rw [finiteStageQuotientMap_out]
  simp

theorem transgressionFactor_eq_inflated_add_residue_boundary
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (χbar : MonoidHom (finiteStageImage R U) (Multiplicative (ZMod p)))
    (hχbar : ∀ (g : F ⧸ (U.1 : Subgroup F)) (n : finiteStageImage R U),
      χbar (MulAut.conjNormal g n) = χbar n)
    (χ : R →ₜ* Multiplicative (ZMod p))
    (hpull : χbar.comp (finiteStageImageMap R U) = χ.toMonoidHom)
    (q r : F ⧸ (R : Subgroup F)) :
    transgressionFactor (R : Subgroup F) χ.toMonoidHom q r =
      transgressionFactor (finiteStageImage R U) χbar
          (finiteStageQuotientMap R U q) (finiteStageQuotientMap R U r) +
        (finiteStageSectionResidueValue R U χbar r -
          finiteStageSectionResidueValue R U χbar (q * r) +
            finiteStageSectionResidueValue R U χbar q) := by
  let gq := OpenNormalSubgroup.quotientProj U.1 (Quotient.out q)
  let gr := OpenNormalSubgroup.quotientProj U.1 (Quotient.out r)
  have hstage := character_quotientSectionResidue_mul
    (finiteStageImage R U) χbar hχbar gq gr
  rw [quotientSectionResidue_finiteStage_out_mul R U q r] at hstage
  simp only [map_mul, toAdd_mul] at hstage
  have hpullFactor := DFunLike.congr_fun hpull
    (quotientSectionFactor (R : Subgroup F) q r)
  have hpullFactorAdd := congrArg Multiplicative.toAdd hpullFactor
  change (χbar (finiteStageImageMap R U
    (quotientSectionFactor (R : Subgroup F) q r))).toAdd =
      (χ (quotientSectionFactor (R : Subgroup F) q r)).toAdd at hpullFactorAdd
  rw [hpullFactorAdd] at hstage
  dsimp only [gq, gr] at hstage
  rw [finiteStageQuotientMap_out R U q,
    finiteStageQuotientMap_out R U r] at hstage
  change transgressionFactor (R : Subgroup F) χ.toMonoidHom q r +
      finiteStageSectionResidueValue R U χbar (q * r) =
    finiteStageSectionResidueValue R U χbar q +
      finiteStageSectionResidueValue R U χbar r +
        transgressionFactor (finiteStageImage R U) χbar
          (finiteStageQuotientMap R U q) (finiteStageQuotientMap R U r) at hstage
  calc
    transgressionFactor (R : Subgroup F) χ.toMonoidHom q r =
        (transgressionFactor (R : Subgroup F) χ.toMonoidHom q r +
          finiteStageSectionResidueValue R U χbar (q * r)) -
            finiteStageSectionResidueValue R U χbar (q * r) := by abel
    _ = (finiteStageSectionResidueValue R U χbar q +
          finiteStageSectionResidueValue R U χbar r +
            transgressionFactor (finiteStageImage R U) χbar
              (finiteStageQuotientMap R U q) (finiteStageQuotientMap R U r)) -
          finiteStageSectionResidueValue R U χbar (q * r) := by rw [hstage]
    _ = transgressionFactor (finiteStageImage R U) χbar
          (finiteStageQuotientMap R U q) (finiteStageQuotientMap R U r) +
        (finiteStageSectionResidueValue R U χbar r -
          finiteStageSectionResidueValue R U χbar (q * r) +
            finiteStageSectionResidueValue R U χbar q) := by abel

/-- Vanishing of the inflated finite-stage transgression class produces a continuous
ambient character extending the original pullback character. -/
theorem exists_continuous_extension_of_inflatedFiniteTransgressionClass_eq_zero
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (χbar : MonoidHom (finiteStageImage R U) (Multiplicative (ZMod p)))
    (hχbar : ∀ (g : F ⧸ (U.1 : Subgroup F)) (n : finiteStageImage R U),
      χbar (MulAut.conjNormal g n) = χbar n)
    (χ : R →ₜ* Multiplicative (ZMod p))
    (hχ : ∀ (f : F) (r : R), χ (MulAut.conjNormal f r) = χ r)
    (hpull : χbar.comp (finiteStageImageMap R U) = χ.toMonoidHom)
    (hzero : inflatedFiniteTransgressionClass R U χbar hχbar = 0) :
    ∃ ψ : F →ₜ* Multiplicative (ZMod p),
      ψ.comp (subgroupInclusion (R : Subgroup F)) = χ := by
  obtain ⟨c, hc⟩ :=
    exists_primitive_of_inflatedFiniteTransgressionClass_eq_zero
      R U χbar hχbar hzero
  let b₀ : F ⧸ (R : Subgroup F) → ZMod p := inflatedPrimitiveValue R c
  let d : F ⧸ (R : Subgroup F) → ZMod p :=
    finiteStageSectionResidueValue R U χbar
  let b : F ⧸ (R : Subgroup F) → ZMod p := fun q ↦ b₀ q + d q
  have hb : ∀ q r,
      b r - b (q * r) + b q =
        transgressionFactor (R : Subgroup F) χ.toMonoidHom q r := by
    intro q r
    have hb₀ := homogeneousOneCochainNormalizedValue_inflated_primitive
      R U χbar c hc q r
    have hfactor := transgressionFactor_eq_inflated_add_residue_boundary
      R U χbar hχbar χ hpull q r
    dsimp only [b, b₀, d]
    rw [hfactor, ← hb₀]
    abel
  let ψhom : MonoidHom F (Multiplicative (ZMod p)) :=
    transgressionKernelExtension (R : Subgroup F) χ.toMonoidHom hχ b hb
  have hrestrict : ψhom.comp (R : Subgroup F).subtype = χ.toMonoidHom :=
    transgressionKernelExtension_restrict
      (R : Subgroup F) χ.toMonoidHom hχ b hb
  have hstageResidueValue (g : F) :
      (χbar (quotientSectionResidue (finiteStageImage R U)
        (OpenNormalSubgroup.quotientProj U.1 g))).toAdd =
        (χ (quotientSectionResidue (R : Subgroup F) g)).toAdd +
          d (QuotientGroup.mk' (R : Subgroup F) g) := by
    have hdecomp := quotientSectionResidue_finiteStage_decomposition R U g
    have hmap := congrArg (fun n : finiteStageImage R U ↦ χbar n) hdecomp
    simp only [map_mul] at hmap
    have hadd := congrArg Multiplicative.toAdd hmap
    rw [toAdd_mul] at hadd
    have hpullResidue := DFunLike.congr_fun hpull
      (quotientSectionResidue (R : Subgroup F) g)
    have hpullResidueAdd := congrArg Multiplicative.toAdd hpullResidue
    change (χbar (finiteStageImageMap R U
      (quotientSectionResidue (R : Subgroup F) g))).toAdd =
        (χ (quotientSectionResidue (R : Subgroup F) g)).toAdd at hpullResidueAdd
    rw [hpullResidueAdd] at hadd
    exact hadd
  have hψvalue (g : F) :
      ψhom g = Multiplicative.ofAdd
        ((χbar (quotientSectionResidue (finiteStageImage R U)
          (OpenNormalSubgroup.quotientProj U.1 g))).toAdd +
            b₀ (QuotientGroup.mk' (R : Subgroup F) g)) := by
    change Multiplicative.ofAdd
      ((χ (quotientSectionResidue (R : Subgroup F) g)).toAdd +
        (b₀ (QuotientGroup.mk' (R : Subgroup F) g) +
          d (QuotientGroup.mk' (R : Subgroup F) g))) = _
    rw [hstageResidueValue]
    congr 1
    abel
  have hstageContinuous : Continuous (fun g : F ↦
      (χbar (quotientSectionResidue (finiteStageImage R U)
        (OpenNormalSubgroup.quotientProj U.1 g))).toAdd) := by
    exact (continuous_of_discreteTopology : Continuous
      (fun q : F ⧸ (U.1 : Subgroup F) ↦
        (χbar (quotientSectionResidue (finiteStageImage R U) q)).toAdd)).comp
          (OpenNormalSubgroup.quotientProj U.1).continuous
  have hb₀Continuous : Continuous b₀ := by
    change Continuous (fun q ↦ (c.1 1 q).down)
    exact (ContinuousLinearEquiv.ulift :
      ULift.{u} (ZMod p) ≃L[ZMod p] ZMod p).continuous.comp
        ((c.1 1).continuous)
  have hb₀QuotientContinuous : Continuous (fun g : F ↦
      b₀ (QuotientGroup.mk' (R : Subgroup F) g)) :=
    hb₀Continuous.comp QuotientGroup.continuous_mk
  have hψcontinuous : Continuous ψhom := by
    rw [show (ψhom : F → Multiplicative (ZMod p)) = fun g ↦
      Multiplicative.ofAdd
        ((χbar (quotientSectionResidue (finiteStageImage R U)
          (OpenNormalSubgroup.quotientProj U.1 g))).toAdd +
            b₀ (QuotientGroup.mk' (R : Subgroup F) g)) from funext hψvalue]
    change Continuous (fun g : F ↦
      (χbar (quotientSectionResidue (finiteStageImage R U)
        (OpenNormalSubgroup.quotientProj U.1 g))).toAdd +
          b₀ (QuotientGroup.mk' (R : Subgroup F) g))
    exact hstageContinuous.add hb₀QuotientContinuous
  let ψ : F →ₜ* Multiplicative (ZMod p) :=
    { toMonoidHom := ψhom
      continuous_toFun := hψcontinuous }
  refine ⟨ψ, ?_⟩
  apply ContinuousMonoidHom.ext
  intro r
  exact DFunLike.congr_fun hrestrict r

end

end ClassFieldTower.ProP
