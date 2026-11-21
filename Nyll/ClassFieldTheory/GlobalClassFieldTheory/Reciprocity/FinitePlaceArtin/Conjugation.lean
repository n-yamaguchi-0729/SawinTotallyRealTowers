/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceModel

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Completion
public import Nyll.ValuedFieldTheory.Valuation.Completion.FiniteLocalization

/-!
# Conjugation of finite-place Artin homomorphisms

This module identifies localized completions associated with conjugate extensions and proves
conjugation invariance of the resulting finite-place Artin map.
-/



@[expose] public section

open scoped IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

universe uK uL

variable {K : Type uK} {L : Type uL}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The algebraic localizations belonging to conjugate extensions of a
finite place are identified by the induced equivalence of completions. -/
noncomputable def finitePlaceConjugateLocalizedCompletionAlgEquiv
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    Ewc ≃ₐ[vK.Completion] Ew := by
  intro vK wc
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  letI hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hwK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  letI hwcK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wc.1
  letI : SMul K wc.1.Completion := hwcK.toSMul
  letI : Algebra vK.Completion wc.1.Completion :=
    AbsoluteValue.completionAlgebra vK wc.1 wc.2
  let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
  let eCompletion : wc.1.Completion ≃ₐ[vK.Completion]
      w.1.Completion :=
    { LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv
        vK w g with
      commutes' :=
        LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv_algebraMap
          vK w g }
  let e : Ewc ≃ₐ[vK.Completion] Ew :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK hvK wc).trans
      (eCompletion.trans
        (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
          vK hvK w).symm)
  exact e

omit [IsAbelianGalois K L] in
/-- The conjugate-localization equivalence carries the canonical
embedding of `L` to the conjugate of that embedding. -/
theorem finitePlaceConjugateLocalizedCompletionAlgEquiv_toAlgebraicLocalization
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) (x : L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g
        (AbsoluteValue.toAlgebraicLocalization
          vK wc.1 wc.2 x) =
      AbsoluteValue.toAlgebraicLocalization
        vK w.1 w.2 (g x) := by
  intro vK wc
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hwK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let hwcK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wc.1
  let : SMul K wc.1.Completion := hwcK.toSMul
  let : Algebra vK.Completion wc.1.Completion :=
    AbsoluteValue.completionAlgebra vK wc.1 wc.2
  apply
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
      vK hvK w).injective
  change
    LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv
        vK w g
        (AbsoluteValue.toCompletion wc.1 x) =
      AbsoluteValue.toCompletion w.1 (g x)
  exact
    LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv_toCompletion
      vK w g x

omit [IsAbelianGalois K L] in
/-- The inverse conjugate-localization equivalence carries the
canonical embedding back along the inverse global automorphism. -/
theorem
    finitePlaceConjugateLocalizedCompletionAlgEquiv_symm_toAlgebraicLocalization
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) (x : L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    (finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g).symm
        (AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 x) =
      AbsoluteValue.toAlgebraicLocalization
        vK wc.1 wc.2 (g.symm x) := by
  intro vK wc
  let hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hwK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let hwcK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wc.1
  let : SMul K wc.1.Completion := hwcK.toSMul
  let : Algebra vK.Completion wc.1.Completion :=
    AbsoluteValue.completionAlgebra vK wc.1 wc.2
  let e :=
    finitePlaceConjugateLocalizedCompletionAlgEquiv
      (K := K) (L := L) v w g
  apply e.injective
  rw [e.apply_symm_apply,
    finitePlaceConjugateLocalizedCompletionAlgEquiv_toAlgebraicLocalization,
    g.apply_symm_apply]

private theorem eq_of_conjugate_actions
    {A B C : Type*} (i : A → B) (j : A → C) (e : C → B)
    (g ρ ρ' : A → A) (τ : B → B) (τ' : C → C)
    (hi : Function.Injective i) (hg : Function.Surjective g)
    (hcomm : Function.Commute g ρ')
    (he : ∀ x, e (j x) = i (g x))
    (ht : ∀ x, e (τ' x) = τ (e x))
    (hρ : ∀ x, τ (i x) = i (ρ x))
    (hρ' : ∀ x, τ' (j x) = j (ρ' x)) : ∀ x, ρ' x = ρ x := by
  intro x
  obtain ⟨y, rfl⟩ := hg x
  apply hi
  calc
    i (ρ' (g y)) = i (g (ρ' y)) := congrArg i (hcomm y).symm
    _ = e (j (ρ' y)) := (he _).symm
    _ = e (τ' (j y)) := congrArg e (hρ' y).symm
    _ = τ (e (j y)) := ht _
    _ = τ (i (g y)) := congrArg τ (he y)
    _ = i (ρ (g y)) := hρ _

private theorem autCongr_apply_image
    {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (t : A ≃ₐ[R] A) (x : A) :
    e (t x) = AlgEquiv.autCongr e t (e x) :=
  (congrArg (fun y : A => e (t y)) (e.symm_apply_apply x)).symm

/-- Conjugation of a place intertwines the two localization
decomposition-group identifications on each local automorphism. -/
theorem finitePlaceDecompositionTransport_conjugate_apply
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    let e :=
      finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g
    let eDw :
        absoluteValueDecompositionGroup K w.1 ≃*
          (Ew ≃ₐ[vK.Completion] Ew) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w
    let eDwc :
        absoluteValueDecompositionGroup K wc.1 ≃*
          (Ewc ≃ₐ[vK.Completion] Ewc) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK wc
    ∀ tauC : Ewc ≃ₐ[vK.Completion] Ewc,
      (absoluteValueDecompositionGroup K wc.1).subtype
          (eDwc.symm tauC) =
        (absoluteValueDecompositionGroup K w.1).subtype
          (eDw.symm (AlgEquiv.autCongr e tauC)) := by
  intro vK wc hvK Ew Ewc e eDw eDwc tauC
  let hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hwK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let hwcK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wc.1
  let : SMul K wc.1.Completion := hwcK.toSMul
  let : Algebra vK.Completion wc.1.Completion :=
    AbsoluteValue.completionAlgebra vK wc.1 wc.2
  let : Algebra vK.Completion Ew := finitePlaceLocalArtinLocalizedAlgebra v w
  let : Algebra vK.Completion Ewc := finitePlaceLocalArtinLocalizedAlgebra v wc
  let tau := AlgEquiv.autCongr e tauC
  let rhoC : absoluteValueDecompositionGroup K wc.1 :=
    eDwc.symm tauC
  let rho : absoluteValueDecompositionGroup K w.1 :=
    eDw.symm tau
  let i := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let j := AbsoluteValue.toAlgebraicLocalization vK wc.1 wc.2
  have hcomm : Function.Commute g (rhoC.1 : L ≃ₐ[K] L) := by
    intro z
    have h := (inferInstance : IsMulCommutative (L ≃ₐ[K] L)).is_comm.comm g rhoC.1
    exact DFunLike.congr_fun h z
  have he := finitePlaceConjugateLocalizedCompletionAlgEquiv_toAlgebraicLocalization v w g
  have ht (z : Ewc) : e (tauC z) = tau (e z) :=
    autCongr_apply_image e tauC z
  have hρ (z : L) : tau (i z) = i (rho.1 z) := by
    have hEval := DFunLike.congr_fun (eDw.apply_symm_apply tau) (i z)
    exact hEval.symm.trans
      (localizationRamificationGroups_decompositionGroupEquiv_toLocalization vK hvK w rho z)
  have hρC (z : L) : tauC (j z) = j (rhoC.1 z) := by
    have hEval := DFunLike.congr_fun (eDwc.apply_symm_apply tauC) (j z)
    exact hEval.symm.trans
      (localizationRamificationGroups_decompositionGroupEquiv_toLocalization
        vK hvK wc rhoC z)
  apply AlgEquiv.ext
  exact eq_of_conjugate_actions i j e g rho.1 rhoC.1 tau tauC
    i.injective g.surjective hcomm he ht hρ hρC

/-- Conjugation of a place intertwines the two localization
decomposition-group identifications after inclusion in the global
Galois group. -/
theorem finitePlaceDecompositionTransport_conjugate
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    let e :=
      finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g
    let eDw :
        absoluteValueDecompositionGroup K w.1 ≃*
          (Ew ≃ₐ[vK.Completion] Ew) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w
    let eDwc :
        absoluteValueDecompositionGroup K wc.1 ≃*
          (Ewc ≃ₐ[vK.Completion] Ewc) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK wc
    (absoluteValueDecompositionGroup K wc.1).subtype.comp
        eDwc.symm.toMonoidHom =
      ((absoluteValueDecompositionGroup K w.1).subtype.comp
          eDw.symm.toMonoidHom).comp
        (AlgEquiv.autCongr e).toMonoidHom := by
  apply MonoidHom.ext
  intro tauC
  exact
    finitePlaceDecompositionTransport_conjugate_apply
      (K := K) (L := L) v w g tauC

private theorem finitePlaceLocalArtinMonoidHom_comp_normalization
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L) :
    let vK := HeightOneSpectrum.adicAbv K v
    let E := LocalizedCompletion vK w
    let a := finitePlaceLocalArtinLocalizedAlgebra v w
    finitePlaceLocalArtinMonoidHom v w =
      (@abelianLocalArtinMonoidHom vK.Completion E _ _ a
        (finitePlaceLocalArtinCompletionValuativeRel v) _
        (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
        (finitePlaceLocalArtinFiniteDimensional v w)
        (finitePlaceLocalArtinIsAbelianGalois v w inferInstance)).comp
          (finitePlaceLocalArtinInputMonoidHom v) := by
  dsimp only [finitePlaceLocalArtinMonoidHom]

private theorem comp_eq_of_composed_maps
    {X A B C : Type*} [Monoid X] [Monoid A] [Monoid B] [Monoid C]
    {i : X →* A} {s : A →* B} {t : A →* C} {e : B →* C}
    {f : X →* B} {g : X →* C}
    (hf : f = s.comp i) (hg : g = t.comp i) (he : e.comp s = t) : e.comp f = g := by
  rw [hf, ← MonoidHom.comp_assoc, he, hg]

/-- Local Artin maps are natural under the localized-completion
equivalence induced by conjugating a finite-place extension. -/
theorem finitePlaceLocalArtinMonoidHom_conjugate
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    let : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    let : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    let e :=
      finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g
    (AlgEquiv.autCongr e).toMonoidHom.comp
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v wc) =
      finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w := by
  intro vK wc Ew Ewc sharedOwner5 sharedOwner6 e
  let := finitePlaceLocalArtinFiniteDimensional v w
  let := finitePlaceLocalArtinFiniteDimensional v wc
  let := finitePlaceLocalArtinIsAbelianGalois v w (inferInstance : FiniteDimensional K L)
  let := finitePlaceLocalArtinIsAbelianGalois v wc (inferInstance : FiniteDimensional K L)
  let := finitePlaceLocalArtinCompletionValuativeRel v
  let := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  have hsource := finitePlaceLocalArtinMonoidHom_comp_normalization v wc
  have htarget := finitePlaceLocalArtinMonoidHom_comp_normalization v w
  have h := LocalClassFieldTheory.abelianLocalArtinMonoidHom_autCongr vK.Completion Ewc Ew e
  have hFinal := comp_eq_of_composed_maps hsource htarget h
  exact hFinal

/-- Conjugating the chosen extension of a finite place does not change
its Artin homomorphism when the global extension is abelian. -/
theorem finitePlaceArtinMonoidHomOfExtension_conjugate
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v
        (absoluteValueExtensionConjugate
          (NumberField.HeightOneSpectrum.adicAbv K v) w g) =
      finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w := by
  let vK := HeightOneSpectrum.adicAbv K v
  let wc := absoluteValueExtensionConjugate vK w g
  let : Algebra vK.Completion (LocalizedCompletion vK w) :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  let : Algebra vK.Completion (LocalizedCompletion vK wc) :=
    finitePlaceLocalArtinLocalizedAlgebra v wc
  let e := finitePlaceConjugateLocalizedCompletionAlgEquiv v w g
  have hTransport : finitePlaceLocalToGlobalMonoidHom v wc =
      (finitePlaceLocalToGlobalMonoidHom v w).comp (AlgEquiv.autCongr e).toMonoidHom := by
    simpa only [finitePlaceLocalToGlobalMonoidHom] using
      (finitePlaceDecompositionTransport_conjugate v w g)
  rw [finitePlaceArtinMonoidHomOfExtension_factor, finitePlaceArtinMonoidHomOfExtension_factor]
  rw [hTransport, MonoidHom.comp_assoc, finitePlaceLocalArtinMonoidHom_conjugate v w g]

/-- The finite-place Artin homomorphism is independent of the chosen
extension of the base place in an abelian extension. -/
theorem finitePlaceArtinMonoidHomOfExtension_eq
    (v : HeightOneSpectrum (𝓞 K))
    (w w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w =
      finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w' := by
  let : NumberField L := NumberField.of_module_finite K L
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let W' :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w'
  let : Finite (L ≃ₐ[K] L) :=
    IsGaloisGroup.finite (L ≃ₐ[K] L) K L
  let :
      IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  let : W.asIdeal.LiesOver v.asIdeal :=
    ⟨(finitePlaceExtensionCentreIdeal_under
      (K := K) (L := L) v w).symm⟩
  let : W'.asIdeal.LiesOver v.asIdeal :=
    ⟨(finitePlaceExtensionCentreIdeal_under
      (K := K) (L := L) v w').symm⟩
  obtain ⟨g, hg⟩ :=
    HilbertRamification.Dedekind.exists_smul_eq_of_isGaloisGroup
      v.asIdeal W.asIdeal W'.asIdeal (L ≃ₐ[K] L)
  have hplace :
      finitePlaceEquiv K L g W = W' := by
    apply HeightOneSpectrum.ext
    rw [finitePlaceEquiv_asIdeal]
    exact hg
  have hconjugate :
      absoluteValueExtensionConjugate
          (NumberField.HeightOneSpectrum.adicAbv K v)
          w g⁻¹ =
        w' := by
    apply
      finitePlaceExtensionCentre_injective
        (K := K) (L := L) v
    rw [finitePlaceExtensionCentre_conjugate]
    simpa only [inv_inv, W, W'] using hplace
  rw [← hconjugate]
  exact
    (finitePlaceArtinMonoidHomOfExtension_conjugate
      (K := K) (L := L) v w g⁻¹).symm

end Reciprocity
end GlobalClassFieldTheory
