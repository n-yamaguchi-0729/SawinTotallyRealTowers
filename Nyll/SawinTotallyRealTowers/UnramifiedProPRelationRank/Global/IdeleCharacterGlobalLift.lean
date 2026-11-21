/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Topology.Instances.ZMod
public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.GlobalMaximalAbelianRestriction
public import Nyll.ProCGroups.ProP.ContinuousH1
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.Characters
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibGlobalArtinNaturality
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MaximalAbelianBaseEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore

/-!
# Lifting an idele character to an absolute Galois character

A continuous finite-valued idele character trivial on principal ideles descends first to
the idele class group and then to its component quotient. Actual global reciprocity identifies
that quotient with the maximal abelian Galois group. Restriction from the absolute Galois
group therefore gives a genuine continuous degree-one class.
-/

@[expose] public section

open scoped NumberField Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP GlobalClassFieldTheory.Reciprocity

variable (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]


variable (chi : IdeleGroup F →ₜ* Multiplicative (ZMod p))
variable (hchi : ∀ a : Fˣ, chi (IdeleGroup.principalIdele F a) = 1)

/-- Descent of a principal-trivial continuous character to the actual idele class group. -/
def ideleCharacterClassLift : IdeleClassGroup F →ₜ* Multiplicative (ZMod p) :=
  IdeleGroup.liftContinuousToStandardClass F chi (by
    rintro _ ⟨a, rfl⟩
    exact hchi a)

@[simp]
theorem ideleCharacterClassLift_mk (a : IdeleGroup F) :
    ideleCharacterClassLift F p chi hchi
      (IdeleGroup.toStandardClass F a) = chi a := by
  exact IdeleGroup.liftContinuousToStandardClass_toStandardClass F chi _ a

/-- The general finite-character correspondence, specialized to the existing
prime target and the maximal-abelian presentation used by the tower argument. -/
noncomputable def ideleCharacterMaximalAbelianLift :
    Gal(maximalAbelianExtension F / F) →ₜ* Multiplicative (ZMod p) :=
  (mathlibIdeleClassCharacterLift F (ideleCharacterClassLift F p chi hchi)).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (ClassFieldTheory.mathlibAbelianizationToMaximal F).symm)

/-- Reciprocity sends an idele class back to the value of its descended character. -/
theorem ideleCharacterMaximalAbelianLift_artin (c : IdeleClassGroup F) :
    ideleCharacterMaximalAbelianLift F p chi hchi (maximalAbelianGlobalArtin F c) =
      ideleCharacterClassLift F p chi hchi c := by
  let targetEquiv := ClassFieldTheory.mathlibAbelianizationToMaximal F
  have hArtin : targetEquiv.symm (maximalAbelianGlobalArtin F c) =
      mathlibGlobalArtin F c := by
    apply targetEquiv.injective
    rw [targetEquiv.apply_symm_apply, mathlibGlobalArtin_toMaximal]
  change mathlibIdeleClassCharacterLift F (ideleCharacterClassLift F p chi hchi)
    (targetEquiv.symm (maximalAbelianGlobalArtin F c)) = _
  rw [hArtin, mathlibIdeleClassCharacterLift_artin]

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
