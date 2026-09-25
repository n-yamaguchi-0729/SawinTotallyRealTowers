/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.FiniteCyclicH2TateH0
import GaloisCohomology.Cyclic.TateH0.Invariants
import GaloisCohomology.Cyclic.TateH0.NormImage
import GaloisCohomology.Cyclic.TateH0.Main
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Main

set_option autoImplicit false
/-!
# Degree-two cohomology of cyclic local unit representations

For a finite cyclic Galois extension, degree-two cohomology of the actual
unit representation is identified first with the field norm quotient.  Over
a nonarchimedean local base this is then transported by finite local
reciprocity to the abelianized Galois group, and hence to the cyclic Galois
group itself.

The periodicity comparison is normalized by the supplied cyclic generator.
The norm-quotient and Artin comparisons are the existing canonical ones.
-/

open CategoryTheory

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology
open CyclicCohomology LocalClassFieldTheory LocalFieldTheory

noncomputable section

/-- For a finite cyclic Galois extension, degree-two cohomology of its unit
representation is the actual field norm quotient.

The generator is used only for the finite-cyclic periodic resolution.
-/
noncomputable def finiteCyclicUnitsH2IsoNormQuotient
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (g : Gal(L / K))
    (hg : ∀ x : Gal(L / K), x ∈ Subgroup.zpowers g) :
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ≅
      ModuleCat.of Int (Additive (NormQuotient K L)) := by
  letI := AlgEquiv.fintype K L
  exact
    finiteCyclicGroupH2IsoTateHZero
        (Rep.ofAlgebraAutOnUnits K L) g hg ≪≫
      H0TateUnitsIsoNormQuotient K L

/-- Over a nonarchimedean local field, finite local reciprocity sends the
cyclic unit `H²` object to the abelianized local Galois group.

This is the Artin interface before using cyclic commutativity to remove the
abelianization wrapper.
-/
noncomputable def finiteCyclicLocalUnitsH2IsoAbelianizedArtin
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (g : Gal(L / K))
    (hg : ∀ x : Gal(L / K), x ∈ Subgroup.zpowers g) :
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ≅
      ModuleCat.of Int (Additive (Abelianization (Gal(L / K)))) := by
  let eArtin :
      Additive (NormQuotient K L) ≃+
        Additive (Abelianization (Gal(L / K))) :=
    (abelianizationEquivNormQuotient K L).symm.toAdditive
  exact
    finiteCyclicUnitsH2IsoNormQuotient K L g hg ≪≫
      eArtin.toIntLinearEquiv.toModuleIso

/-- The cyclic form of the local Artin interface, with target the actual
Galois group.  It retains its natural additive-group structure; a `ZMod n`
coordinate would require a further normalized choice of cyclic coordinate.
-/
noncomputable def finiteCyclicLocalUnitsH2AddEquivGalois
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (g : Gal(L / K))
    (hg : ∀ x : Gal(L / K), x ∈ Subgroup.zpowers g) :
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ≃+
      Additive (Gal(L / K)) := by
  letI : IsCyclic (Gal(L / K)) :=
    CyclicCohomology.isCyclic_of_generator g hg
  letI : CommGroup (Gal(L / K)) := IsCyclic.commGroup
  let eCyclic :
      Additive (Abelianization (Gal(L / K))) ≃+
        Additive (Gal(L / K)) :=
    (Abelianization.equivOfComm (H := Gal(L / K))).symm.toAdditive
  exact
    (finiteCyclicLocalUnitsH2IsoAbelianizedArtin K L g hg).toLinearEquiv.toAddEquiv.trans
      eCyclic

end

end ClassFieldTower.Martinet.Shafarevich
