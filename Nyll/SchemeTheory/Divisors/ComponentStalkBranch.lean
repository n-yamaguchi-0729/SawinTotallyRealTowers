/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.StalkLocalization
import Nyll.SchemeTheory.Divisors.LocalScheme
import Nyll.SchemeTheory.Divisors.ReducedIrreducibleComponentGeometry
import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale

/-!
# Component branches in a specialized stalk

The generic point of an irreducible boundary component specializes to each
point on that component.  Pulling the closed prime of the generic stalk back
along the corresponding generization map gives the canonical branch prime in
the stalk at the specialized point.
-/

noncomputable section


open CategoryTheory TopologicalSpace IsLocalRing

namespace AlgebraicGeometry.Scheme

universe u

variable {X : Scheme.{u}} {x y : X}

/-- The prime of `O_{X,y}` represented by a generalization `x` of `y`.
It is the inverse image of the maximal ideal of `O_{X,x}` under the
generization map. -/
noncomputable def specializationPrime (hxy : x ⤳ y) :
    Spec (X.presheaf.stalk y) :=
  Spec.map (X.presheaf.stalkSpecializes hxy)
    (closedPoint (X.presheaf.stalk x))

/-- The specialization prime maps back to its defining generalization. -/
@[simp]
theorem fromSpecStalk_specializationPrime (hxy : x ⤳ y) :
    X.fromSpecStalk y (specializationPrime hxy) = x := by
  change
    (Spec.map (X.presheaf.stalkSpecializes hxy) ≫ X.fromSpecStalk y)
        (closedPoint (X.presheaf.stalk x)) = x
  rw [SpecMap_stalkSpecializes_fromSpecStalk hxy,
    fromSpecStalk_closedPoint]

/-- The height of the specialization prime is the codimension of its
defining generalization. -/
theorem specializationPrime_height (hxy : x ⤳ y) :
    (specializationPrime hxy).asIdeal.height = Order.coheight x := by
  apply WithBot.coe_eq_coe.mp
  calc
    (((specializationPrime hxy).asIdeal.height : ℕ∞) : WithBot ℕ∞) =
        ringKrullDim
          (X.presheaf.stalk
            (X.fromSpecStalk y (specializationPrime hxy))) :=
      (X.ringKrullDim_stalk_fromSpecStalk_eq_height y
        (specializationPrime hxy)).symm
    _ = ringKrullDim (X.presheaf.stalk x) := by
      rw [fromSpecStalk_specializationPrime]
    _ = ((Order.coheight x : ℕ∞) : WithBot ℕ∞) :=
      ringKrullDim_stalk_eq_coheight x

/-- The specialization prime is the kernel of evaluation in the residue
field of its defining generalization. -/
theorem specializationPrime_asIdeal_eq_ker_residue (hxy : x ⤳ y) :
    (specializationPrime hxy).asIdeal =
      RingHom.ker
        ((X.residue x).hom.comp
          (X.presheaf.stalkSpecializes hxy).hom) := by
  ext a
  change
    X.presheaf.stalkSpecializes hxy a ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      X.presheaf.stalkSpecializes hxy a ∈
        RingHom.ker (IsLocalRing.residue (X.presheaf.stalk x))
  rw [IsLocalRing.ker_residue]

/-- Characteristic zero descends from the generic residue field to the
quotient by the corresponding specialization prime. -/
theorem specializationPrime_quotient_charZero
    (hxy : x ⤳ y) [CharZero (X.residueField x)] :
    CharZero
      (X.presheaf.stalk y ⧸ (specializationPrime hxy).asIdeal) := by
  rw [specializationPrime_asIdeal_eq_ker_residue]
  exact
    (RingHom.kerLift
      ((X.residue x).hom.comp
        (X.presheaf.stalkSpecializes hxy).hom)).charZero

/-- Every specialization prime is contained in the closed prime of the
specialized local ring. -/
theorem specializationPrime_le_maximalIdeal (hxy : x ⤳ y) :
    (specializationPrime hxy).asIdeal ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
  IsLocalRing.le_maximalIdeal
    (PrimeSpectrum.isPrime (specializationPrime hxy)).ne_top

/-- The residue field at the specialized point is a residue-characteristic
target for the component branch quotient. -/
noncomputable def specializationPrimeQuotientToResidueField
    (hxy : x ⤳ y) :
    (X.presheaf.stalk y ⧸ (specializationPrime hxy).asIdeal) →+*
      X.residueField y :=
  Ideal.Quotient.lift (specializationPrime hxy).asIdeal
    (X.residue y).hom fun a ha ↦ by
      apply RingHom.mem_ker.mp
      change a ∈ RingHom.ker
        (IsLocalRing.residue (X.presheaf.stalk y))
      rw [IsLocalRing.ker_residue]
      exact specializationPrime_le_maximalIdeal hxy ha

/-- If the generalization lies on an ideal-sheaf support, then the
corresponding specialization prime contains the stalk ideal. -/
theorem IdealSheafData.stalkIdeal_le_specializationPrime_of_mem_support
    (I : X.IdealSheafData) (hxy : x ⤳ y) (hxI : x ∈ I.support) :
    I.stalkIdeal y ≤ (specializationPrime hxy).asIdeal := by
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := y) (by simp)
  let V : X.affineOpens := ⟨U, hU⟩
  have hxU : x ∈ U := hxy.mem_open U.2 hyU
  rw [I.stalkIdeal_eq_map_ideal y V hyU,
    Ideal.map_le_iff_le_comap]
  intro a ha
  change
    X.presheaf.stalkSpecializes hxy
        (X.presheaf.germ U y hyU a) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)
  rw [← CommRingCat.comp_apply,
    TopCat.Presheaf.germ_stalkSpecializes]
  change
    X.presheaf.germ U x hxU a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro haUnit
  have hxZero : x ∈ X.zeroLocus (I.ideal V : Set Γ(X, U)) :=
    (I.mem_support_iff_of_mem hxU).mp hxI
  have hnotBasic : x ∉ X.basicOpen a :=
    (X.mem_zeroLocus_iff (I.ideal V : Set Γ(X, U)) x).mp
      hxZero a ha
  exact hnotBasic ((X.mem_basicOpen a x hxU).mpr haUnit)

namespace IdealSheafData

variable {I : X.IdealSheafData}

/-- The generic point of a component specializes to every point of that
component. -/
theorem componentGenericPoint_specializes_subschemeι
    (I : X.IdealSheafData)
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme)
    (z : I.subscheme) (hz : z ∈ Z) :
    I.componentGenericPoint Z hZ ⤳ I.subschemeι z := by
  rw [I.componentGenericPoint_eq Z hZ]
  exact ((genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩).specializes hz).map
    I.subschemeι.continuous

/-- The canonical branch prime in the ambient stalk at a point of a chosen
component. -/
noncomputable def componentBranchPrimeAt
    (I : X.IdealSheafData)
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme)
    (z : I.subscheme) (hz : z ∈ Z) :
    Spec (X.presheaf.stalk (I.subschemeι z)) :=
  specializationPrime (I.componentGenericPoint_specializes_subschemeι Z hZ z hz)

/-- The component branch represents the component generic point in the local
scheme at the chosen specialization. -/
@[simp]
theorem fromSpecStalk_componentBranchPrimeAt
    (I : X.IdealSheafData)
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme)
    (z : I.subscheme) (hz : z ∈ Z) :
    X.fromSpecStalk (I.subschemeι z)
        (I.componentBranchPrimeAt Z hZ z hz) =
      I.componentGenericPoint Z hZ := by
  exact fromSpecStalk_specializationPrime _

/-- On a locally Noetherian scheme, the canonical branch of an
effective Cartier component has height one. -/
theorem IsEffectiveCartier.componentBranchPrimeAt_height_eq_one
    [IsLocallyNoetherian X]
    (hI : I.IsEffectiveCartier)
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme)
    (z : I.subscheme) (hz : z ∈ Z) :
    (I.componentBranchPrimeAt Z hZ z hz).asIdeal.height = 1 := by
  rw [componentBranchPrimeAt, specializationPrime_height]
  exact hI.coheight_componentGenericPoint_eq_one Z hZ

/-- Every height-one prime of a stalk containing an effective Cartier ideal
represents the generic point of an irreducible component of the divisor.

This is the converse to constructing a height-one stalk prime from a chosen
component and specialization. -/
theorem IsEffectiveCartier.exists_componentGenericPoint_eq_fromSpecStalk
    [IsLocallyNoetherian X]
    (hI : I.IsEffectiveCartier) (x : X)
    (q : Spec (X.presheaf.stalk x))
    (hqheight : q.asIdeal.height = 1)
    (hIq : I.stalkIdeal x ≤ q.asIdeal) :
    ∃ (Z : Set I.subscheme)
      (hZ : Z ∈ irreducibleComponents I.subscheme),
      I.componentGenericPoint Z hZ = X.fromSpecStalk x q := by
  let y : X := X.fromSpecStalk x q
  have hySupport : y ∈ I.support :=
    I.mem_support_fromSpecStalk_of_stalkIdeal_le x q hIq
  have hyRange : y ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hySupport
  obtain ⟨z, hz⟩ := hyRange
  let Z : Set I.subscheme := irreducibleComponent z
  have hZ : Z ∈ irreducibleComponents I.subscheme :=
    irreducibleComponent_mem_irreducibleComponents z
  refine ⟨Z, hZ, ?_⟩
  let eta : X := I.componentGenericPoint Z hZ
  have hetaSpecializes : eta ⤳ y := by
    have h := I.componentGenericPoint_specializes_subschemeι
      Z hZ z (show z ∈ Z from mem_irreducibleComponent)
    simpa only [eta, y, hz] using h
  have hetaCoheight : Order.coheight eta = 1 := by
    exact hI.coheight_componentGenericPoint_eq_one Z hZ
  have hyCoheight : Order.coheight y = 1 := by
    apply WithBot.coe_eq_coe.mp
    calc
      ((Order.coheight y : ℕ∞) : WithBot ℕ∞) =
          ringKrullDim (X.presheaf.stalk y) :=
        (ringKrullDim_stalk_eq_coheight y).symm
      _ = (q.asIdeal.height : WithBot ℕ∞) :=
        X.ringKrullDim_stalk_fromSpecStalk_eq_height x q
      _ = ((1 : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hqheight
  have hyLeEta : y ≤ eta := Scheme.le_iff_specializes.mpr hetaSpecializes
  have hnotLt : ¬y < eta := by
    intro hyLt
    have hlt := Order.coheight_strictAnti hyLt (by simp [hetaCoheight])
    rw [hetaCoheight, hyCoheight] at hlt
    exact (lt_irrefl (1 : ℕ∞)) hlt
  have hetaLeY : eta ≤ y := by
    by_contra h
    exact hnotLt ⟨hyLeEta, h⟩
  have hySpecializesEta : y ⤳ eta :=
    Scheme.le_iff_specializes.mp hetaLeY
  exact (inseparable_iff_specializes_and.mpr
    ⟨hetaSpecializes, hySpecializesEta⟩).eq

/-- Every height-one prime in the stalk at a point of an effective Cartier
divisor is the canonical branch prime of a component through that point. -/
theorem IsEffectiveCartier.exists_componentBranchPrimeAt_eq
    [IsLocallyNoetherian X]
    (hI : I.IsEffectiveCartier) (z : I.subscheme)
    (q : Spec (X.presheaf.stalk (I.subschemeι z)))
    (hqheight : q.asIdeal.height = 1)
    (hIq : I.stalkIdeal (I.subschemeι z) ≤ q.asIdeal) :
    ∃ (Z : Set I.subscheme)
      (hZ : Z ∈ irreducibleComponents I.subscheme)
      (hz : z ∈ Z),
      I.componentBranchPrimeAt Z hZ z hz = q := by
  obtain ⟨Z, hZ, hgeneric⟩ :=
    hI.exists_componentGenericPoint_eq_fromSpecStalk
      (I.subschemeι z) q hqheight hIq
  have hfromSpec :
      X.fromSpecStalk (I.subschemeι z) q ⤳ I.subschemeι z := by
    have hmem : X.fromSpecStalk (I.subschemeι z) q ∈
        Set.range (X.fromSpecStalk (I.subschemeι z)) := ⟨q, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hmem
    exact hmem
  have hgenericSpecializes :
      I.componentGenericPoint Z hZ ⤳ I.subschemeι z := by
    rw [hgeneric]
    exact hfromSpec
  have hz : z ∈ Z := by
    apply (genericPoints.isGenericPoint_ofComponent
      (⟨Z, hZ⟩ : irreducibleComponents I.subscheme)).specializes_iff_mem.mp
    apply I.subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp
    rw [← I.componentGenericPoint_eq Z hZ]
    exact hgenericSpecializes
  refine ⟨Z, hZ, hz, ?_⟩
  apply (X.fromSpecStalk (I.subschemeι z)).isEmbedding.injective
  rw [I.fromSpecStalk_componentBranchPrimeAt, hgeneric]

/-- The canonical component branch contains the boundary stalk ideal. -/
theorem stalkIdeal_le_componentBranchPrimeAt
    (I : X.IdealSheafData)
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme)
    (z : I.subscheme) (hz : z ∈ Z) :
    I.stalkIdeal (I.subschemeι z) ≤
      (I.componentBranchPrimeAt Z hZ z hz).asIdeal := by
  apply I.stalkIdeal_le_specializationPrime_of_mem_support
  exact I.componentGenericPoint_mem_support Z hZ

end IdealSheafData

end AlgebraicGeometry.Scheme

end
