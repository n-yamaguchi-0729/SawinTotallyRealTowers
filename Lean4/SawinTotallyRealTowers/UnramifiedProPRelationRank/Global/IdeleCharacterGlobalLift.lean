/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.GlobalMaximalAbelianRestriction
import ProCGroups.ProP.ContinuousH1
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MaximalAbelianKernel
import ProCGroups.Topologies.QuotientMaps

set_option autoImplicit false
/-!
# Lifting an idele character to an absolute Galois character

A continuous finite-valued idele character trivial on principal ideles descends first to
the idele class group and then to its component quotient. Actual global reciprocity identifies
that quotient with the maximal abelian Galois group. Restriction from the absolute Galois
group therefore gives a genuine continuous degree-one class.
-/

open scoped NumberField Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP GlobalClassFieldTheory.Reciprocity

variable (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]

local instance ideleGlobalLiftTopology : TopologicalSpace (ZMod p) := ⊥
local instance ideleGlobalLiftDiscreteTopology : DiscreteTopology (ZMod p) :=
  discreteTopology_bot _

variable (chi : IdeleGroup F →ₜ* Multiplicative (ZMod p))
variable (hchi : ∀ a : Fˣ, chi (IdeleGroup.principalIdele F a) = 1)

/-- Descent of a principal-trivial continuous character to the actual idele class group. -/
def ideleCharacterClassLift : IdeleClassGroup F →ₜ* Multiplicative (ZMod p) :=
  ProCGroups.QuotientGroup.liftₜ (IdeleGroup.principalSubgroup F) chi (by
    rintro _ ⟨a, rfl⟩
    exact hchi a)

@[simp]
theorem ideleCharacterClassLift_mk (a : IdeleGroup F) :
    ideleCharacterClassLift F p chi hchi
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup F) a) = chi a := rfl

/-- The character kills the connected component because its target is discrete. -/
def ideleCharacterComponentLift :
    ideleClassComponentQuotient F →ₜ* Multiplicative (ZMod p) :=
  ProCGroups.QuotientGroup.liftₜ (ideleClassIdentityComponent F)
    (ideleCharacterClassLift F p chi hchi)
    (ideleClassIdentityComponent_le_ker F (ideleCharacterClassLift F p chi hchi))

@[simp]
theorem ideleCharacterComponentLift_mk (c : IdeleClassGroup F) :
    ideleCharacterComponentLift F p chi hchi
      (QuotientGroup.mk' (ideleClassIdentityComponent F) c) =
      ideleCharacterClassLift F p chi hchi c := rfl

/-- The character transported through the actual component-quotient reciprocity isomorphism. -/
def ideleCharacterMaximalAbelianLift :
    Gal(maximalAbelianExtension F / F) →ₜ* Multiplicative (ZMod p) :=
  (ideleCharacterComponentLift F p chi hchi).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (ideleClassComponentQuotientEquivMaximalAbelianGalois F).symm)

/-- Reciprocity sends an idele class back to the value of its descended character. -/
theorem ideleCharacterMaximalAbelianLift_artin (c : IdeleClassGroup F) :
    ideleCharacterMaximalAbelianLift F p chi hchi (maximalAbelianGlobalArtin F c) =
      ideleCharacterClassLift F p chi hchi c := by
  rw [← ideleClassComponentQuotientEquivMaximalAbelianGalois_mk F c]
  change ideleCharacterComponentLift F p chi hchi
      ((ideleClassComponentQuotientEquivMaximalAbelianGalois F).symm
        (ideleClassComponentQuotientEquivMaximalAbelianGalois F
          (QuotientGroup.mk' (ideleClassIdentityComponent F) c))) = _
  rw [ContinuousMulEquiv.symm_apply_apply, ideleCharacterComponentLift_mk]

/-- A principal-trivial idele character gives an actual absolute Galois character. -/
def ideleCharacterGlobalLift :
    Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod p) :=
  (ideleCharacterMaximalAbelianLift F p chi hchi).comp (globalMaximalAbelianRestriction F)

/-- The resulting continuous degree-one class of the absolute Galois group. -/
def ideleCharacterGlobalH1 : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup F) :=
  h1OfCharacter (ideleCharacterGlobalLift F p chi hchi)

@[simp]
theorem ideleCharacterGlobalH1_character :
    characterOfH1 (ideleCharacterGlobalH1 F p chi hchi) =
      ideleCharacterGlobalLift F p chi hchi := by
  ext sigma
  rfl

end ClassFieldTower.Martinet.Shafarevich
