/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupAbsoluteAction
import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupTopology
import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteAbelianizationAction
import Nyll.GaloisCohomology.ProP.PrimeToIndexCharacterExtension
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Topology.Instances.ZMod

/-!
# Descent of invariant absolute Galois characters

Transport an absolute character of a finite normal intermediate field to its
actual fixing subgroup. The established comparison of conjugation actions
preserves invariance. Transfer divided by the extension degree then extends
the character whenever that degree is coprime to its coefficient modulus.
-/

namespace KummerTheory

open ProCGroups.Abelian

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L]

attribute [local instance] closureOverIntermediate

/-- Pull back an absolute character along the actual comparison from the
fixing subgroup to the absolute Galois group of the intermediate field. -/
noncomputable def fixingSubgroupAbsoluteCharacter
    {A : Type*} [CommGroup A] [TopologicalSpace A]
    (f : Gal(AlgebraicClosure L/L) →ₜ* A) : L.fixingSubgroup →ₜ* A := by
  let e : L.fixingSubgroup ≃ₜ* Gal(AlgebraicClosure L/L) :=
    (fixingSubgroupContinuousEquiv L).trans (absoluteGaloisClosureEquiv L Ω)
  exact ⟨f.toMonoidHom.comp e.toMulEquiv.toMonoidHom, f.continuous.comp e.continuous⟩

variable [Normal K L]

attribute [local instance] fixingSubgroup_normal

/-- Invariance under all relative field automorphisms gives invariance under
actual ambient conjugation on the fixing subgroup. -/
theorem fixingSubgroupAbsoluteCharacter_conjNormal
    {A : Type*} [CommGroup A] [TopologicalSpace A] [T1Space A]
    (f : Gal(AlgebraicClosure L/L) →ₜ* A)
    (hinv : ∀ (δ : Gal(L/K)) (σ : Gal(AlgebraicClosure L/L)),
      f (absoluteGaloisConjugate δ.toRingEquiv σ) = f σ)
    (g : Gal(Ω/K)) (σ : L.fixingSubgroup) :
    fixingSubgroupAbsoluteCharacter L f (MulAut.conjNormal g σ) =
      fixingSubgroupAbsoluteCharacter L f σ := by
  have hconj := fixingSubgroupAbsoluteAbelianizationEquiv_quotient_conjugation
    L g (TopologicalAbelianization.mk L.fixingSubgroup σ)
  rw [quotientConjugationTopologicalAbelianizationMap_mk_apply_mk
      L.fixingSubgroup g σ,
    fixingSubgroupAbsoluteAbelianizationEquiv_apply_mk L (MulAut.conjNormal g σ),
    fixingSubgroupAbsoluteAbelianizationEquiv_apply_mk L σ,
    absoluteGaloisAbelianizationAction_apply_mk] at hconj
  have hvalue := congrArg (TopologicalAbelianization.lift f) hconj
  rw [TopologicalAbelianization.lift_apply_mk,
    TopologicalAbelianization.lift_apply_mk] at hvalue
  change f (absoluteGaloisClosureEquiv L Ω
      (fixingSubgroupContinuousEquiv L (MulAut.conjNormal g σ))) =
    f (absoluteGaloisClosureEquiv L Ω (fixingSubgroupContinuousEquiv L σ))
  exact hvalue.trans (hinv (g.restrictNormal L)
    (absoluteGaloisClosureEquiv L Ω (fixingSubgroupContinuousEquiv L σ)))

/-- An invariant absolute character extends to the actual ambient Galois
group when its modulus is coprime to the finite separable extension degree. -/
theorem exists_character_extension_of_coprime_finrank [Algebra.IsSeparable K L]
    (n : ℕ) (hdegree : (Module.finrank K L).Coprime n)
    (f : Gal(AlgebraicClosure L/L) →ₜ* Multiplicative (ZMod n))
    (hinv : ∀ (δ : Gal(L/K)) (σ : Gal(AlgebraicClosure L/L)),
      f (absoluteGaloisConjugate δ.toRingEquiv σ) = f σ) :
    ∃ ψ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n),
      ∀ σ : L.fixingSubgroup, ψ (σ : Gal(Ω/K)) =
        f (absoluteGaloisClosureEquiv L Ω (fixingSubgroupContinuousEquiv L σ)) := by
  have : IsGalois K L := { to_isSeparable := inferInstance, to_normal := inferInstance }
  let H : OpenSubgroup Gal(Ω/K) := ⟨L.fixingSubgroup, L.fixingSubgroup_isOpen⟩
  have hindex_eq : H.toSubgroup.index = Module.finrank K L := by
    change L.fixingSubgroup.index = _
    have hsurj : Function.Surjective
        (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K)) :=
      AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := Ω)
    rw [← L.restrictNormalHom_ker, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr hsurj]
    exact (Nat.card_congr (Subgroup.topEquiv :
      (⊤ : Subgroup Gal(L/K)) ≃* Gal(L/K)).toEquiv).trans
        (IsGalois.card_aut_eq_finrank K L)
  let : H.toSubgroup.FiniteIndex :=
    ⟨by
      rw [hindex_eq]
      exact (Module.finrank_pos (R := K) (M := L)).ne'⟩
  have hindex : H.toSubgroup.index.Coprime n := by
    rw [hindex_eq]
    exact hdegree
  let φ : H →ₜ* Multiplicative (ZMod n) := fixingSubgroupAbsoluteCharacter L f
  refine ⟨ClassFieldTower.Cohomology.primeToIndexCharacterExtension H n φ, ?_⟩
  intro σ
  change ClassFieldTower.Cohomology.primeToIndexCharacterExtension H n φ
    (σ : Gal(Ω/K)) = φ σ
  exact ClassFieldTower.Cohomology.primeToIndexCharacterExtension_subtype H n hindex φ
    (fun g h => fixingSubgroupAbsoluteCharacter_conjNormal L f hinv g h) σ



end KummerTheory
