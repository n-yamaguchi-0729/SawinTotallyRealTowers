/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FiniteCyclicBaseUnitCarry
import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbol

set_option autoImplicit false
/-!
# Finite Kummer carry classes and the local Hilbert symbol

For the chosen simple Kummer extension, the finite-cyclic carry class with a
base-field unit coefficient evaluates through the norm quotient to the local
Hilbert symbol of that unit.
-/

open CategoryTheory Representation

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology
open CyclicCohomology LocalFieldTheory

noncomputable section

/-- The normalized carry class with coefficient `a : Kˣ`, evaluated in the
norm quotient of the chosen simple Kummer extension and then by the descended
local Hilbert symbol, is `(a, b)`. -/
theorem localHilbertSymbolFromNormQuotient_carry_baseUnit
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (p : ℕ+) (hpK : ((p : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) (a b : Kˣ)
    (g : Gal((KummerTheory.chosenSimpleKummerExtension K p hpK b) / K))
    (hg : ∀ sigma :
      Gal((KummerTheory.chosenSimpleKummerExtension K p hpK b) / K),
      sigma ∈ Subgroup.zpowers g) :
    let E := KummerTheory.chosenSimpleKummerExtension K p hpK b
    let : FiniteDimensional K E :=
      KummerTheory.chosenSimpleKummerExtension_finiteDimensional K p hpK b
    let : IsAbelianGalois K E :=
      KummerTheory.chosenSimpleKummerExtension_isAbelianGalois
        K p hpK hmu b
    letI := AlgEquiv.fintype K E
    let : IsCyclic (Gal(E / K)) :=
      CyclicCohomology.isCyclic_of_generator g hg
    letI : CommGroup (Gal(E / K)) := IsCyclic.commGroup
    LocalClassFieldTheory.Kummer.localHilbertSymbolFromNormQuotient
        K p hpK hmu b
        (Additive.toMul
          ((finiteCyclicUnitsH2IsoNormQuotient K E g hg).hom
            (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K E)
              (finiteCyclicCarryTwoCocycle
                (Rep.ofAlgebraAutOnUnits K E) g hg
                (finiteCyclicBaseUnitFixed K E g a))))) =
      LocalClassFieldTheory.Kummer.localHilbertSymbol K p hpK hmu a b := by
  dsimp only
  let E := KummerTheory.chosenSimpleKummerExtension K p hpK b
  let : FiniteDimensional K E :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional K p hpK b
  let : IsAbelianGalois K E :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois
      K p hpK hmu b
  let := AlgEquiv.fintype K E
  let : IsCyclic (Gal(E / K)) :=
    CyclicCohomology.isCyclic_of_generator g hg
  let : CommGroup (Gal(E / K)) := IsCyclic.commGroup
  rw [finiteCyclicUnitsH2IsoNormQuotient_carry_baseUnit]
  exact
    LocalClassFieldTheory.Kummer.localHilbertSymbolFromNormQuotient_normClass
      K p hpK hmu a b

end

end ClassFieldTower.Martinet.Shafarevich
