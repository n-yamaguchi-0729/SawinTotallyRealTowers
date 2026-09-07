import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.GlobalMaximalAbelianRestriction
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MaximalAbelianGlobalArtin
import ProCGroups.Abelian.TopologicalAbelianization

set_option autoImplicit false
/-!
# Global reciprocity for an absolute finite character

An absolute character factors through the actual maximal abelian subextension.
Pulling that character back by global Artin gives a principal-trivial idele
character. This direction is used to compare choices of global central lifts.
-/

open scoped NumberField Topology
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich

open GlobalClassFieldTheory.Reciprocity

variable (F : Type) [Field F] (p : ℕ) [Fact p.Prime]

local instance globalReciprocityCharacterTopology : TopologicalSpace (ZMod p) := ⊥
local instance globalReciprocityCharacterDiscrete : DiscreteTopology (ZMod p) :=
  discreteTopology_bot _

variable (chi : Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod p))

/-- Descent of a continuous absolute character to the maximal abelian Galois group. -/
def globalReciprocityMaximalAbelianCharacter :
    Gal(maximalAbelianExtension F / F) →ₜ* Multiplicative (ZMod p) :=
  (ProCGroups.Abelian.TopologicalAbelianization.lift
    (chi.comp (ContinuousMonoidHom.toContinuousMonoidHom
      (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv F).symm))).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (absoluteTopologicalAbelianizationEquivMaximalAbelianGalois F).symm)

/-- Restriction recovers the original character, not merely its kernel. -/
@[simp]
theorem globalReciprocityMaximalAbelianCharacter_restriction
    (sigma : Field.absoluteGaloisGroup F) :
    globalReciprocityMaximalAbelianCharacter F p chi
      (globalMaximalAbelianRestriction F sigma) = chi sigma := by
  let e := RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv F
  let b := absoluteTopologicalAbelianizationEquivMaximalAbelianGalois F
  have hb : b (QuotientGroup.mk (e sigma)) = globalMaximalAbelianRestriction F sigma := rfl
  rw [← hb]
  change ProCGroups.Abelian.TopologicalAbelianization.lift
      (chi.comp (ContinuousMonoidHom.toContinuousMonoidHom e.symm))
      (b.symm (b (QuotientGroup.mk (e sigma)))) = chi sigma
  rw [ContinuousMulEquiv.symm_apply_apply]
  change chi (e.symm (e sigma)) = chi sigma
  exact congrArg chi (e.symm_apply_apply sigma)

theorem globalReciprocityMaximalAbelianCharacter_comp_restriction :
    (globalReciprocityMaximalAbelianCharacter F p chi).comp
      (globalMaximalAbelianRestriction F) = chi := by
  ext sigma
  exact globalReciprocityMaximalAbelianCharacter_restriction F p chi sigma

variable [NumberField F]

/-- The actual idele character associated with an absolute character. -/
def globalReciprocityIdeleCharacter : IdeleGroup F →ₜ* Multiplicative (ZMod p) :=
  ((globalReciprocityMaximalAbelianCharacter F p chi).comp
    (maximalAbelianGlobalArtin F)).comp
      { toMonoidHom := QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
        continuous_toFun := QuotientGroup.continuous_mk }

@[simp]
theorem globalReciprocityIdeleCharacter_apply (a : IdeleGroup F) :
    globalReciprocityIdeleCharacter F p chi a =
      globalReciprocityMaximalAbelianCharacter F p chi
        (maximalAbelianGlobalArtin F
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup F) a)) := rfl

/-- Global reciprocity is trivial on every principal idele. -/
theorem globalReciprocityIdeleCharacter_principal (a : Fˣ) :
    globalReciprocityIdeleCharacter F p chi (IdeleGroup.principalIdele F a) = 1 := by
  rw [globalReciprocityIdeleCharacter_apply]
  have h : QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
      (IdeleGroup.principalIdele F a) = 1 :=
    (QuotientGroup.eq_one_iff _).2 ⟨a, rfl⟩
  rw [h, map_one, map_one]

end ClassFieldTower.Martinet.Shafarevich
