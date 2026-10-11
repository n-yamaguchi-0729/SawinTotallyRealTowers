/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.QuasicoherentImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Actual finite-type subsheaves containing finitely many global sections

A family of actual global sections defines a morphism from the free sheaf
through `freeHomEquiv`. Its native image contains the given sections.
For a finite family the source is finite type and quasicoherent, so the
image in a quasicoherent ambient module has both properties. This supplies
the local input to finite-type submodule extension without an additional
affine comparison assumption.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace SheafOfModules

variable {X : Scheme.{u}} (M : SheafOfModules.{u} X.ringCatSheaf)

/-- A section on the top open gives the actual compatible family on all opens. -/
def topSection (s : M.val.obj (op ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk (fun W => M.val.map W.unop.leTop.op s)
    (fun {V _} f =>
      (M.val.map_comp_apply V.unop.leTop.op f s).symm.trans
        (M.val.congr_map_apply (Subsingleton.elim _ _) s))

/-- The compatible family retains the original top section. -/
theorem topSection_top (s : M.val.obj (op ⊤)) : (M.topSection s).val (op ⊤) = s := by
  change M.val.presheaf.map (𝟙 (op ⊤)) s = s
  rw [M.val.presheaf.map_id]
  rfl

/-- The native image of the morphism specified by an actual section family. -/
def sectionFamilySubmodule {I : Type u} (s : I → M.sections) : M.Submodule :=
  imageSubmodule (M.freeHomEquiv.symm s)

/-- Each specified section belongs to the constructed image on every open. -/
theorem mem_sectionFamilySubmodule {I : Type u} (s : I → M.sections) (i : I)
    (U : X.Opens) : (s i).val (op U) ∈ (M.sectionFamilySubmodule s).toSubmodule.obj (op U) := by
  let f : free (R := X.ringCatSheaf) I ⟶ M := M.freeHomEquiv.symm s
  let x := (freeSection (R := X.ringCatSheaf) i).val (op U)
  let y := ((toImageSubmodule f).val.app (op U)).hom x
  have hImage := congrArg (fun g => (g.val.app (op U)).hom x) (toImageSubmodule_ι f)
  have hSection := congrArg (fun t : M.sections => t.val (op U))
    (sectionsMap_freeHomEquiv_symm_freeSection s i)
  have hy : y.val = (s i).val (op U) := hImage.trans hSection
  rw [← hy]
  exact y.property

/-- A finite family generates a finite-type actual image subsheaf. -/
theorem isFiniteType_sectionFamilySubmodule {I : Type u} [Finite I]
    (s : I → M.sections) : (M.sectionFamilySubmodule s).toSheafOfModules.IsFiniteType := by
  let p : (free (R := X.ringCatSheaf) I).GeneratingSections :=
    free.generatingSections (R := X.ringCatSheaf) I
  let q : (free (R := X.ringCatSheaf) I).LocalGeneratorsData := p.localGeneratorsData
  have hq : q.IsFiniteType := by
    constructor
    intro U
    constructor
    exact inferInstanceAs (Finite I)
  have : (free (R := X.ringCatSheaf) I).IsFiniteType := by
    refine { exists_localGeneratorsData := ?_ }
    exact ⟨q, hq⟩
  exact isFiniteType_imageSubmodule (M.freeHomEquiv.symm s)

/-- The generated image is quasicoherent in a quasicoherent ambient module. -/
theorem isQuasicoherent_sectionFamilySubmodule [M.IsQuasicoherent]
    {I : Type u} (s : I → M.sections) :
    (M.sectionFamilySubmodule s).toSheafOfModules.IsQuasicoherent := by
  have : (free (R := X.ringCatSheaf) I).IsQuasicoherent := inferInstance
  exact isQuasicoherent_imageSubmodule (M.freeHomEquiv.symm s)

/-- Any finitely generated submodule of actual global sections is contained
in a finite-type quasicoherent native subsheaf. -/
theorem exists_finiteType_submodule_containing_top [M.IsQuasicoherent]
    (K : _root_.Submodule (X.ringCatSheaf.obj.obj (op ⊤)) (M.val.obj (op ⊤))) (hK : K.FG) :
    ∃ N : M.Submodule, N.toSheafOfModules.IsQuasicoherent ∧
      N.toSheafOfModules.IsFiniteType ∧ K ≤ N.toSubmodule.obj (op ⊤) := by
  obtain ⟨s, hs⟩ := hK
  let a : s → M.sections := fun i => M.topSection i.val
  refine ⟨M.sectionFamilySubmodule a,
    M.isQuasicoherent_sectionFamilySubmodule a, M.isFiniteType_sectionFamilySubmodule a, ?_⟩
  rw [← hs]
  apply _root_.Submodule.span_le.mpr
  intro x hx
  have h := M.mem_sectionFamilySubmodule a ⟨x, hx⟩ ⊤
  exact (M.topSection_top x) ▸ h

end SheafOfModules
