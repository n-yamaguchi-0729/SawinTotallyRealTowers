/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibTopologicalGlobalReciprocity
public import Nyll.ProCGroups.Topologies.QuotientMaps

/-!
# Characters and the specified global Artin map

Precomposition with the existing geometric `mathlibGlobalArtin` gives the
character correspondence. Both carriers are Mathlib's groups. A totally
disconnected target suffices, so every finite discrete target is included.
The inverse descends through the identity component and uses the same
reciprocity equivalence; it does not choose another Artin map.
-/

@[expose] public section

open scoped NumberField Topology

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

variable (K : Type*) [Field K] [NumberField K]
variable {A : Type*} [Group A] [TopologicalSpace A]
    [IsTopologicalGroup A] [TotallyDisconnectedSpace A]

/-- The Galois character associated to a continuous idele-class character. -/
noncomputable def mathlibIdeleClassCharacterLift
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) :
    Field.absoluteGaloisGroupAbelianization K →ₜ* A :=
  (ProCGroups.QuotientGroup.liftₜ
    (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K))
    χ χ.connectedComponentOfOne_le_ker).comp
      (ContinuousMonoidHom.toContinuousMonoidHom
        (mathlibIdeleClassConnectedQuotientEquivAbelianization K).symm)

/-- The lifted character recovers its original value under geometric Artin. -/
@[simp]
theorem mathlibIdeleClassCharacterLift_artin
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A)
    (c : NumberField.IdeleClassGroup (𝓞 K) K) :
    mathlibIdeleClassCharacterLift K χ (mathlibGlobalArtin K c) = χ c := by
  rw [mathlibGlobalArtin_apply]
  change (ProCGroups.QuotientGroup.liftₜ
    (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K))
    χ χ.connectedComponentOfOne_le_ker)
      ((mathlibIdeleClassConnectedQuotientEquivAbelianization K).symm
        (mathlibIdeleClassConnectedQuotientEquivAbelianization K
          (QuotientGroup.mk'
            (Subgroup.connectedComponentOfOne
              (NumberField.IdeleClassGroup (𝓞 K) K)) c))) = χ c
  rw [ContinuousMulEquiv.symm_apply_apply, ProCGroups.QuotientGroup.liftₜ_apply_mk]

/-- Global reciprocity for continuous characters, by precomposition with the
specified geometric Artin homomorphism. -/
noncomputable def mathlibGlobalCharacterEquiv :
    (Field.absoluteGaloisGroupAbelianization K →ₜ* A) ≃
      (NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) where
  toFun χ := χ.comp (mathlibGlobalArtin K)
  invFun := mathlibIdeleClassCharacterLift K
  left_inv χ := by
    apply ContinuousMonoidHom.ext
    intro σ
    obtain ⟨c, rfl⟩ := mathlibGlobalArtin_surjective K σ
    exact mathlibIdeleClassCharacterLift_artin K (χ.comp (mathlibGlobalArtin K)) c
  right_inv χ := by
    apply ContinuousMonoidHom.ext
    intro c
    exact mathlibIdeleClassCharacterLift_artin K χ c

/-- Postcomposition in the character target commutes with reciprocity. -/
theorem mathlibGlobalCharacterEquiv_postcompose
    {B : Type*} [Group B] [TopologicalSpace B]
    [IsTopologicalGroup B] [TotallyDisconnectedSpace B]
    (f : A →ₜ* B) (χ : Field.absoluteGaloisGroupAbelianization K →ₜ* A) :
    mathlibGlobalCharacterEquiv K (f.comp χ) =
      f.comp (mathlibGlobalCharacterEquiv K χ) := by
  apply ContinuousMonoidHom.ext
  intro c
  rfl

/-- The inverse correspondence is natural under the same postcomposition. -/
theorem mathlibIdeleClassCharacterLift_postcompose
    {B : Type*} [Group B] [TopologicalSpace B]
    [IsTopologicalGroup B] [TotallyDisconnectedSpace B]
    (f : A →ₜ* B) (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) :
    mathlibIdeleClassCharacterLift K (f.comp χ) =
      f.comp (mathlibIdeleClassCharacterLift K χ) := by
  apply ContinuousMonoidHom.ext
  intro σ
  obtain ⟨c, rfl⟩ := mathlibGlobalArtin_surjective K σ
  change mathlibIdeleClassCharacterLift K (f.comp χ) (mathlibGlobalArtin K c) =
    f (mathlibIdeleClassCharacterLift K χ (mathlibGlobalArtin K c))
  simp only [mathlibIdeleClassCharacterLift_artin]
  rfl

end GlobalClassFieldTheory.Reciprocity
