/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FiniteCyclicLocalUnitsH2

set_option autoImplicit false
/-!
# Evaluating the finite-cyclic periodic unit class

For a finite cyclic Galois extension, a unit fixed by the chosen generator is
fixed by the whole Galois group.  This file evaluates its class in the
periodic degree-two model through the existing comparison with degree-zero
Tate cohomology and the field norm quotient.
-/

open CategoryTheory Representation

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology
open CyclicCohomology LocalFieldTheory

noncomputable section

/-- A unit fixed by a generator, regarded canonically as a Galois-invariant
unit. -/
noncomputable def finiteCyclicGeneratorFixedUnitInvariant
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (g : Gal(L / K))
    (hg : ∀ σ : Gal(L / K), σ ∈ Subgroup.zpowers g)
    (a : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).ρ g - LinearMap.id)) :
    unitsInvariantSubmodule K L := by
  refine ⟨a.1, ?_⟩
  apply
    (Representation.mem_invariants_iff_of_forall_mem_zpowers
      (Rep.ofAlgebraAutOnUnits K L).ρ g hg a.1).2
  have ha := a.2
  change
    (Rep.ofAlgebraAutOnUnits K L).ρ g a.1 - a.1 = 0 at ha
  exact sub_eq_zero.mp ha

/-- The base-field unit canonically represented by a generator-fixed unit. -/
noncomputable def finiteCyclicGeneratorFixedBaseUnit
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (g : Gal(L / K))
    (hg : ∀ σ : Gal(L / K), σ ∈ Subgroup.zpowers g)
    (a : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).ρ g - LinearMap.id)) : Kˣ :=
  Additive.toMul
    (invariantsUnitsAddEquivBaseUnits K L
      (finiteCyclicGeneratorFixedUnitInvariant K L g hg a))

/-- The positive-even periodic class represented by a generator-fixed unit. -/
noncomputable def finiteCyclicUnitsH2PeriodicClass
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (g : Gal(L / K))
    (hg : ∀ σ : Gal(L / K), σ ∈ Subgroup.zpowers g)
    (a : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).ρ g - LinearMap.id)) :
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 := by
  let _ := AlgEquiv.fintype K L
  let _ : IsCyclic (Gal(L / K)) :=
    CyclicCohomology.isCyclic_of_generator g hg
  let _ : CommGroup (Gal(L / K)) := IsCyclic.commGroup
  let a' : LinearMap.ker
      (Rep.applyAsHom (Rep.ofAlgebraAutOnUnits K L) g -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap :=
    ⟨a.1, by
      change
        (Rep.ofAlgebraAutOnUnits K L).ρ g a.1 - a.1 = 0
      exact a.2⟩
  exact
    Rep.FiniteCyclicGroup.groupCohomologyπEven
      (Rep.ofAlgebraAutOnUnits K L) g hg 2 (by decide) a'

/-- The Tate degree-zero class represented by the same generator-fixed unit
in the finite-cyclic periodic short complex. -/
noncomputable def finiteCyclicUnitsTateHZeroPeriodicClass
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (g : Gal(L / K))
    (hg : ∀ σ : Gal(L / K), σ ∈ Subgroup.zpowers g)
    (a : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).ρ g - LinearMap.id)) :
    tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0 := by
  let _ := AlgEquiv.fintype K L
  let _ : IsCyclic (Gal(L / K)) :=
    CyclicCohomology.isCyclic_of_generator g hg
  let _ : CommGroup (Gal(L / K)) := IsCyclic.commGroup
  let A := Rep.ofAlgebraAutOnUnits K L
  let T := Rep.FiniteCyclicGroup.normHomCompSub A g
  let a' : LinearMap.ker
      (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap :=
    ⟨a.1, by
      change A.ρ g a.1 - a.1 = 0
      exact a.2⟩
  exact
    (TateCohomology.isoFiniteCyclicZero A g hg).inv
      (T.homologyπ (T.moduleCatCyclesIso.inv a'))

/-- The arithmetic part of the unit Tate comparison sends an invariant-unit
quotient representative to the norm class of the corresponding base unit. -/
theorem finiteCyclicUnitsH0Arithmetic_mk
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (x : unitsInvariantSubmodule K L) :
    (H0TateUnitsIsoNormQuotient K L).hom
        ((tateUnitsH0IsoInvariantsQuotient K L).inv
          (Submodule.Quotient.mk x)) =
      Additive.ofMul
        (normClass K L
          (Additive.toMul (invariantsUnitsAddEquivBaseUnits K L x))) := by
  let _ := AlgEquiv.fintype K L
  let eInv := Submodule.Quotient.equiv
      (unitsTateH0NormSubmodule K L)
      (additiveNormSubgroup K L).toIntSubmodule
      (invariantsUnitsEquivBaseUnits K L)
      (invariantsUnitsEquivBaseUnits_map_tateNormSubmodule K L)
  let eNormEq :=
    QuotientAddGroup.quotientAddEquivOfEq
      (additiveNormSubgroup_eq_ker_quotient_map K L)
  have hNormSurjective : Function.Surjective
      (MonoidHom.toAdditive (normClass K L)) := by
    change Function.Surjective
      (QuotientGroup.mk' (localNormSubgroup K L))
    exact QuotientGroup.mk'_surjective _
  let eNormKer :=
    QuotientAddGroup.quotientKerEquivOfSurjective
      (MonoidHom.toAdditive (normClass K L)) hNormSurjective
  dsimp only [H0TateUnitsIsoNormQuotient]
  simp only [Iso.trans_hom]
  rw [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  rw [ModuleCat.comp_apply]
  dsimp only [LinearEquiv.toModuleIso]
  change
    eNormKer (eNormEq (eInv (Submodule.Quotient.mk x))) = _
  dsimp only [eInv]
  rw [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  change
    eNormKer
      (eNormEq
        (QuotientAddGroup.mk
          ((invariantsUnitsEquivBaseUnits K L) x))) = _
  dsimp only [eNormEq, eNormKer]
  rw [QuotientAddGroup.quotientAddEquivOfEq_mk,
    QuotientAddGroup.quotientKerEquivOfSurjective,
    QuotientAddGroup.quotientKerEquivOfRightInverse_apply,
    QuotientAddGroup.kerLift_mk]
  rfl

/-- The finite-cyclic periodic Tate representative is the invariant-unit
quotient class of the same underlying fixed unit. -/
theorem finiteCyclicUnitsTateHZeroPeriodicClass_eq
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (g : Gal(L / K))
    (hg : ∀ σ : Gal(L / K), σ ∈ Subgroup.zpowers g)
    (a : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).ρ g - LinearMap.id)) :
    finiteCyclicUnitsTateHZeroPeriodicClass K L g hg a =
      (tateUnitsH0IsoInvariantsQuotient K L).inv
        (Submodule.Quotient.mk
          (finiteCyclicGeneratorFixedUnitInvariant K L g hg a)) := by
  let _ := AlgEquiv.fintype K L
  let _ : IsCyclic (Gal(L / K)) :=
    CyclicCohomology.isCyclic_of_generator g hg
  let _ : CommGroup (Gal(L / K)) := IsCyclic.commGroup
  let A := Rep.ofAlgebraAutOnUnits K L
  let T := Rep.FiniteCyclicGroup.normHomCompSub A g
  let a' : LinearMap.ker
      (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap :=
    ⟨a.1, by
      change A.ρ g a.1 - a.1 = 0
      exact a.2⟩
  let aT : T.moduleCatLeftHomologyData.K := a'
  let S : ShortComplex (ModuleCat ℤ) :=
    .mk A.norm.toModuleCatHom (groupCohomology.d₀₁ A)
      (Rep.norm_comp_d_eq_zero A)
  have hkerCyclic :
      LinearMap.ker S.g.hom = LinearMap.ker T.g.hom := by
    dsimp [S, T]
    rw [groupCohomology.d₀₁_ker_eq_invariants]
    ext x
    simpa [Rep.sub_hom, sub_eq_zero] using
      Representation.mem_invariants_iff_of_forall_mem_zpowers
        A.ρ g hg x
  let eKCyclic : LinearMap.ker S.g.hom ≃ₗ[ℤ]
      LinearMap.ker T.g.hom :=
    LinearEquiv.ofEq _ _ hkerCyclic
  have hboundaryCyclic :
      (LinearMap.range S.moduleCatToCycles).map eKCyclic.toLinearMap =
        LinearMap.range T.moduleCatToCycles := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      rfl
    · rintro ⟨z, rfl⟩
      refine ⟨S.moduleCatToCycles z, ⟨z, rfl⟩, ?_⟩
      apply Subtype.ext
      rfl
  let eCyclic := Submodule.Quotient.equiv
    (LinearMap.range S.moduleCatToCycles)
    (LinearMap.range T.moduleCatToCycles)
    eKCyclic hboundaryCyclic
  have eCyclic_symm_mk
      (z : LinearMap.ker T.g.hom) :
      eCyclic.symm (Submodule.Quotient.mk z) =
        Submodule.Quotient.mk (eKCyclic.symm z) := by
    rfl
  let eCyclicIso :
      S.moduleCatLeftHomologyData.H ≅ T.moduleCatLeftHomologyData.H :=
    eCyclic.toModuleIso
  have hkerInvariant :
      LinearMap.ker S.g.hom = unitsInvariantSubmodule K L := by
    dsimp only [S]
    rw [groupCohomology.d₀₁_ker_eq_invariants]
    rfl
  let eKInvariant : LinearMap.ker S.g.hom ≃ₗ[ℤ]
      unitsInvariantSubmodule K L :=
    LinearEquiv.ofEq _ _ hkerInvariant
  have hboundaryInvariant :
      (LinearMap.range S.moduleCatToCycles).map eKInvariant.toLinearMap =
        unitsTateH0NormSubmodule K L := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      rfl
    · rintro ⟨z, rfl⟩
      refine ⟨S.moduleCatToCycles z, ⟨z, rfl⟩, ?_⟩
      apply Subtype.ext
      rfl
  let eInvariant := Submodule.Quotient.equiv
    (LinearMap.range S.moduleCatToCycles)
    (unitsTateH0NormSubmodule K L)
    eKInvariant hboundaryInvariant
  have eInvariant_mk
      (z : LinearMap.ker S.g.hom) :
      eInvariant (Submodule.Quotient.mk z) =
        Submodule.Quotient.mk (eKInvariant z) := by
    rfl
  let eInvariantIso :
      S.moduleCatLeftHomologyData.H ≅
        ModuleCat.of ℤ
          (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) :=
    eInvariant.toModuleIso
  have hFiniteCyclicComparison :
      TateCohomology.isoFiniteCyclicZero A g hg =
        TateCohomology.isoZeroBoundary A ≪≫
          S.moduleCatHomologyIso ≪≫ eCyclicIso ≪≫
            T.moduleCatHomologyIso.symm := by
    rfl
  have hInvariantComparison :
      tateUnitsH0IsoInvariantsQuotient K L =
        TateCohomology.isoZeroBoundary A ≪≫
          S.moduleCatHomologyIso ≪≫ eInvariantIso := by
    rfl
  apply
    (ModuleCat.mono_iff_injective
      (tateUnitsH0IsoInvariantsQuotient K L).hom).1 inferInstance
  rw [Iso.inv_hom_id_apply]
  change
    (((TateCohomology.isoFiniteCyclicZero A g hg).inv ≫
        (tateUnitsH0IsoInvariantsQuotient K L).hom).hom
      (T.homologyπ (T.moduleCatCyclesIso.inv aT))) = _
  have hcomparison :
      (TateCohomology.isoFiniteCyclicZero A g hg).inv ≫
          (tateUnitsH0IsoInvariantsQuotient K L).hom =
        T.moduleCatHomologyIso.hom ≫ eCyclicIso.inv ≫ eInvariantIso.hom := by
    rw [hFiniteCyclicComparison, hInvariantComparison]
    simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
    rw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
    rfl
  rw [hcomparison, ModuleCat.comp_apply, ModuleCat.comp_apply]
  rw [ShortComplex.π_moduleCatCyclesIso_hom_apply]
  have hcycles :
      T.moduleCatCyclesIso.hom (T.moduleCatCyclesIso.inv aT) = aT :=
    Iso.inv_hom_id_apply T.moduleCatCyclesIso aT
  rw [hcycles]
  dsimp only [eCyclicIso, eInvariantIso, LinearEquiv.toModuleIso]
  change eInvariant (eCyclic.symm
    (Submodule.Quotient.mk a')) = _
  rw [eCyclic_symm_mk, eInvariant_mk]
  congr 1

/-- The arithmetic Tate comparison evaluates the finite-cyclic periodic
representative as the norm class of its canonical base-field unit. -/
theorem H0TateUnitsIsoNormQuotient_periodicClass
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (g : Gal(L / K))
    (hg : ∀ σ : Gal(L / K), σ ∈ Subgroup.zpowers g)
    (a : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).ρ g - LinearMap.id)) :
    (H0TateUnitsIsoNormQuotient K L).hom
        (finiteCyclicUnitsTateHZeroPeriodicClass K L g hg a) =
      Additive.ofMul
        (normClass K L
          (finiteCyclicGeneratorFixedBaseUnit K L g hg a)) := by
  rw [finiteCyclicUnitsTateHZeroPeriodicClass_eq K L g hg a]
  exact
    finiteCyclicUnitsH0Arithmetic_mk K L
      (finiteCyclicGeneratorFixedUnitInvariant K L g hg a)

/-- The finite-cyclic `H² ≅ Tate H⁰ ≅ Kˣ/N(Lˣ)` comparison sends the
periodic class of a generator-fixed unit to the norm class of its canonical
base-field value. -/
theorem finiteCyclicUnitsH2IsoNormQuotient_periodicClass
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (g : Gal(L / K))
    (hg : ∀ σ : Gal(L / K), σ ∈ Subgroup.zpowers g)
    (a : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).ρ g - LinearMap.id)) :
    (finiteCyclicUnitsH2IsoNormQuotient K L g hg).hom
        (finiteCyclicUnitsH2PeriodicClass K L g hg a) =
      Additive.ofMul
        (normClass K L
          (finiteCyclicGeneratorFixedBaseUnit K L g hg a)) := by
  let _ := AlgEquiv.fintype K L
  let _ : IsCyclic (Gal(L / K)) :=
    CyclicCohomology.isCyclic_of_generator g hg
  let _ : CommGroup (Gal(L / K)) := IsCyclic.commGroup
  let A := Rep.ofAlgebraAutOnUnits K L
  let a' : LinearMap.ker
      (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap :=
    ⟨a.1, by
      change A.ρ g a.1 - a.1 = 0
      exact a.2⟩
  change
    (H0TateUnitsIsoNormQuotient K L).hom
        ((finiteCyclicGroupH2IsoTateHZero A g hg).hom
          (Rep.FiniteCyclicGroup.groupCohomologyπEven
            A g hg 2 (by decide) a')) = _
  rw [finiteCyclicGroupH2IsoTateHZero_groupCohomologyπEven]
  change
    (H0TateUnitsIsoNormQuotient K L).hom
        (finiteCyclicUnitsTateHZeroPeriodicClass K L g hg a) = _
  exact H0TateUnitsIsoNormQuotient_periodicClass K L g hg a

end

end ClassFieldTower.Martinet.Shafarevich
