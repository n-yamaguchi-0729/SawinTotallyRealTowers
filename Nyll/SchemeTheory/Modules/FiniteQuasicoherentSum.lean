/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.QuasicoherentImage
import Nyll.SchemeTheory.Modules.QuasicoherentCoprod
import Nyll.SchemeTheory.Modules.FiniteTypeCoprod
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Actual finite joins of finite-type quasicoherent subsheaves

The native sheaf-lattice join is identified with the actual image of the
map from the coproduct. The proof uses the least-submodule property of the
image and both original inclusions. No pointwise-sum description of the
sheaf join is assumed.
-/

noncomputable section

universe u v w

open CategoryTheory Limits AlgebraicGeometry

namespace SheafOfModules

section General

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

/-- Inclusion of native submodules from their actual pointwise containment. -/
def Submodule.homOfLE {M : SheafOfModules.{u} R} {N P : M.Submodule} (h : N ≤ P) :
    N.toSheafOfModules ⟶ P.toSheafOfModules :=
  ⟨PresheafOfModules.Submodule.homOfLE h⟩

/-- The containment-induced map respects both embeddings into the ambient sheaf. -/
theorem Submodule.homOfLE_ι {M : SheafOfModules.{u} R} {N P : M.Submodule}
    (h : N ≤ P) : Submodule.homOfLE h ≫ P.ι = N.ι :=
  rfl

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The sheaf-lattice join is the actual image of the coproduct of the inclusions. -/
theorem imageSubmodule_coprod_eq_sup {M : SheafOfModules.{u} R} (N P : M.Submodule) :
    imageSubmodule (coprod.desc N.ι P.ι) = N ⊔ P := by
  apply le_antisymm
  · apply imageSubmodule_le (coprod.desc N.ι P.ι) (N ⊔ P)
      (coprod.desc (Submodule.homOfLE le_sup_left) (Submodule.homOfLE le_sup_right))
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, Submodule.homOfLE_ι, coprod.inl_desc]
    · rw [coprod.inr_desc_assoc, Submodule.homOfLE_ι, coprod.inr_desc]
  · apply sup_le
    · apply Submodule.le_of_hom_ι N (imageSubmodule (coprod.desc N.ι P.ι))
        (coprod.inl ≫ toImageSubmodule (coprod.desc N.ι P.ι))
      rw [Category.assoc, toImageSubmodule_ι, coprod.inl_desc]
    · apply Submodule.le_of_hom_ι P (imageSubmodule (coprod.desc N.ι P.ι))
        (coprod.inr ≫ toImageSubmodule (coprod.desc N.ι P.ι))
      rw [Category.assoc, toImageSubmodule_ι, coprod.inr_desc]

/-- The actual image of a zero morphism is the bottom native submodule. -/
theorem imageSubmodule_zero (M N : SheafOfModules.{u} R) :
    imageSubmodule (0 : M ⟶ N) = ⊥ := by
  apply le_antisymm
  · exact imageSubmodule_le 0 ⊥ 0 (zero_comp)
  · exact bot_le

section FiniteType

variable [HasBinaryProducts C]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

private theorem isFiniteType_free_finite (I : Type u) [Finite I] :
    (free (R := R) I).IsFiniteType := by
  let p : (free (R := R) I).GeneratingSections :=
    { I := I
      s := (free (R := R) I).freeHomEquiv (𝟙 (free I))
      epi := by rw [Equiv.symm_apply_apply]; infer_instance }
  let q : (free (R := R) I).LocalGeneratorsData := p.localGeneratorsData
  have hq : q.IsFiniteType := by
    constructor
    intro X
    constructor
    exact inferInstanceAs (Finite I)
  exact ⟨⟨q, hq⟩⟩

/-- The bottom native submodule is of finite type. -/
theorem Submodule.isFiniteType_bot (M : SheafOfModules.{u} R) :
    (⊥ : M.Submodule).toSheafOfModules.IsFiniteType := by
  have : (free (R := R) PEmpty.{u + 1}).IsFiniteType :=
    isFiniteType_free_finite PEmpty.{u + 1}
  have h := isFiniteType_imageSubmodule (0 : free (R := R) PEmpty.{u + 1} ⟶ M)
  rw [imageSubmodule_zero] at h
  exact h

variable [HasPullbacks C]

/-- The actual sheaf-lattice join of two finite-type submodules is finite type. -/
theorem Submodule.isFiniteType_sup {M : SheafOfModules.{u} R}
    (N P : M.Submodule) [N.toSheafOfModules.IsFiniteType] [P.toSheafOfModules.IsFiniteType] :
    (N ⊔ P).toSheafOfModules.IsFiniteType := by
  have : (N.toSheafOfModules ⨿ P.toSheafOfModules).IsFiniteType := isFiniteType_coprod
  have h := isFiniteType_imageSubmodule (coprod.desc N.ι P.ι)
  rw [imageSubmodule_coprod_eq_sup] at h
  exact h

/-- The actual finite join of finite-type native submodules is finite type. -/
theorem Submodule.isFiniteType_finset_sup {M : SheafOfModules.{u} R}
    {ι : Type w} (s : Finset ι) (N : ι → M.Submodule)
    (h : ∀ i ∈ s, (N i).toSheafOfModules.IsFiniteType) :
    (s.sup N).toSheafOfModules.IsFiniteType := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty]
      exact Submodule.isFiniteType_bot M
  | @insert i s _hi ih =>
      have : (N i).toSheafOfModules.IsFiniteType := h i (Finset.mem_insert_self i s)
      have : (s.sup N).toSheafOfModules.IsFiniteType :=
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      rw [Finset.sup_insert]
      exact Submodule.isFiniteType_sup (N i) (s.sup N)

end FiniteType

end General

section Quasicoherent

variable {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf} [M.IsQuasicoherent]

/-- The bottom native submodule of a quasicoherent sheaf is quasicoherent. -/
theorem Submodule.isQuasicoherent_bot :
    (⊥ : M.Submodule).toSheafOfModules.IsQuasicoherent := by
  have h := isQuasicoherent_imageSubmodule (0 : M ⟶ M)
  rw [imageSubmodule_zero] at h
  exact h

/-- The actual sheaf-lattice join of two quasicoherent submodules is quasicoherent. -/
theorem Submodule.isQuasicoherent_sup (N P : M.Submodule)
    [N.toSheafOfModules.IsQuasicoherent] [P.toSheafOfModules.IsQuasicoherent] :
    (N ⊔ P).toSheafOfModules.IsQuasicoherent := by
  have : (N.toSheafOfModules ⨿ P.toSheafOfModules).IsQuasicoherent :=
    isQuasicoherent_coprod_native N.toSheafOfModules P.toSheafOfModules
  have h := isQuasicoherent_imageSubmodule (coprod.desc N.ι P.ι)
  rw [imageSubmodule_coprod_eq_sup] at h
  exact h

/-- The actual finite join of quasicoherent native submodules is quasicoherent. -/
theorem Submodule.isQuasicoherent_finset_sup {ι : Type w}
    (s : Finset ι) (N : ι → M.Submodule)
    (h : ∀ i ∈ s, (N i).toSheafOfModules.IsQuasicoherent) :
    (s.sup N).toSheafOfModules.IsQuasicoherent := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty]
      exact Submodule.isQuasicoherent_bot
  | @insert i s _hi ih =>
      have : (N i).toSheafOfModules.IsQuasicoherent := h i (Finset.mem_insert_self i s)
      have : (s.sup N).toSheafOfModules.IsQuasicoherent :=
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      rw [Finset.sup_insert]
      exact Submodule.isQuasicoherent_sup (N i) (s.sup N)

end Quasicoherent

end SheafOfModules
