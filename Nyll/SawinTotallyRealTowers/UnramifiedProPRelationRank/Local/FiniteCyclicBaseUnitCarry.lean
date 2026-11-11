/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.FiniteCyclicBarPeriodicH2Comparison
import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FiniteCyclicUnitsH2PeriodicEvaluation
import Nyll.GaloisCohomology.Cyclic.NormKernelVanishing
import Nyll.GaloisCohomology.Cyclic.TateH0.Invariants

/-!
# Base-unit carry classes in finite cyclic unit cohomology

This file evaluates the normalized carry cocycle whose coefficient is a unit
from the base field.  Under the finite-cyclic `H²`--norm-quotient comparison,
its class is exactly the corresponding norm class.
-/

open CategoryTheory Representation

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology
open CyclicCohomology LocalFieldTheory

noncomputable section

/-- A base-field unit embedded in a finite Galois extension, bundled as a
fixed point for an arbitrary Galois automorphism. -/
noncomputable def finiteCyclicBaseUnitFixed
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (g : Gal(L/K)) (a : Kˣ) :
    LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).ρ g - LinearMap.id) := by
  refine ⟨Additive.ofMul
    (Units.map (algebraMap K L).toMonoidHom a), ?_⟩
  apply sub_eq_zero.mpr
  change Additive.ofMul
        (Units.mapEquiv g.toMulEquiv
          (Units.map (algebraMap K L).toMonoidHom a)) =
      Additive.ofMul (Units.map (algebraMap K L).toMonoidHom a)
  apply congrArg Additive.ofMul
  apply Units.ext
  exact g.commutes (a : K)

/-- Recovering the base-field unit from its embedded invariant representative
is the identity. -/
theorem finiteCyclicGeneratorFixedBaseUnit_baseUnitFixed
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (g : Gal(L/K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g)
    (a : Kˣ) :
    finiteCyclicGeneratorFixedBaseUnit K L g hg
        (finiteCyclicBaseUnitFixed K L g a) = a := by
  apply Units.ext
  apply (algebraMap K L).injective
  change algebraMap K L
      ((finiteCyclicGeneratorFixedBaseUnit K L g hg
        (finiteCyclicBaseUnitFixed K L g a) : Kˣ) : K) =
    algebraMap K L (a : K)
  exact (CyclicCohomology.invariantsUnitsAddEquivBaseUnits_spec K L
    (finiteCyclicGeneratorFixedUnitInvariant K L g hg
      (finiteCyclicBaseUnitFixed K L g a))).trans rfl

/-- The normalized carry class with a base-unit coefficient evaluates to the
norm class of that base unit. -/
theorem finiteCyclicUnitsH2IsoNormQuotient_carry_baseUnit
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (g : Gal(L/K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g)
    (a : Kˣ) :
    let := AlgEquiv.fintype K L
    let : IsCyclic (Gal(L / K)) :=
      CyclicCohomology.isCyclic_of_generator g hg
    let : CommGroup (Gal(L / K)) := IsCyclic.commGroup
    (finiteCyclicUnitsH2IsoNormQuotient K L g hg).hom
        (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)
          (finiteCyclicCarryTwoCocycle (Rep.ofAlgebraAutOnUnits K L)
            g hg (finiteCyclicBaseUnitFixed K L g a))) =
      Additive.ofMul (normClass K L a) := by
  intro reusedStructure1 reusedStructure2 reusedStructure3
  let A := Rep.ofAlgebraAutOnUnits K L
  let baseUnitFixed :
      LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap :=
    Eq.mp (by rfl) (finiteCyclicBaseUnitFixed K L g a)
  let periodic := Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 ⟨1, rfl⟩
  have hperiodic : periodic baseUnitFixed =
      finiteCyclicUnitsH2PeriodicClass K L g hg (finiteCyclicBaseUnitFixed K L g a) := by
    dsimp only [finiteCyclicUnitsH2PeriodicClass]
    exact congrArg periodic (Subtype.ext rfl)
  have hcarry := H2π_finiteCyclicCarryTwoCocycle A g hg baseUnitFixed
  have hnorm := finiteCyclicUnitsH2IsoNormQuotient_periodicClass K L g hg
    (finiteCyclicBaseUnitFixed K L g a)
  have hbase := finiteCyclicGeneratorFixedBaseUnit_baseUnitFixed K L g hg a
  exact (congrArg (fun c => (finiteCyclicUnitsH2IsoNormQuotient K L g hg).hom c)
    (hcarry.trans hperiodic)).trans
      (hnorm.trans (congrArg (fun u => Additive.ofMul (normClass K L u)) hbase))

end

end ClassFieldTower.Martinet.Shafarevich
