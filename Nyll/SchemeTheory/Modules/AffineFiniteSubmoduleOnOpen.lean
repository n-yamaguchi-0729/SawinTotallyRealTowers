/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.AffineFiniteSubmoduleExtension
import Nyll.SchemeTheory.Modules.FiniteTypeLocalAffineSections
import Nyll.SchemeTheory.Modules.FiniteTypeSubopen
import Nyll.SchemeTheory.Modules.SubmoduleCoverEquality

/-!
# Finite-type affine submodules preserving a quasi-compact restriction

An actual quasicoherent submodule which is finite type on a quasi-compact
open contains a globally finite-type quasicoherent submodule with the same
restriction to that open. Compactness supplies finitely many principal
opens. Native finite type on each of them supplies finite generation of the
actual canonical localization; finite numerator extraction then gives the
submodule, and sheaf membership locality identifies its restriction.

This is the affine step of Stacks Tag 01PF, applied after the actual
quasicoherent extension of Tag 01PE.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- On an affine spectrum, a quasicoherent submodule which is finite type
on a quasi-compact open contains a finite-type quasicoherent submodule
whose actual restriction to that open is unchanged. -/
theorem exists_finiteType_submodule_eq_over_of_isCompact {R : CommRingCat.{u}}
    (F : SheafOfModules.{u} (Spec R).ringCatSheaf) [F.IsQuasicoherent] (H : F.Submodule)
    [H.toSheafOfModules.IsQuasicoherent] (U : (Spec R).Opens)
    (hU : IsCompact (U : Set (Spec R)))
    (hFT : (H.toSheafOfModules.over U).IsFiniteType) :
    ∃ N : F.Submodule, N ≤ H ∧ N.toSheafOfModules.IsQuasicoherent ∧
      N.toSheafOfModules.IsFiniteType ∧ N.over U = H.over U := by
  let G : (Spec R).Modules :=
    (sheafOfModulesEquivalence (Spec R)).inverse.obj H.toSheafOfModules
  have : G.IsQuasicoherent := inferInstanceAs H.toSheafOfModules.IsQuasicoherent
  have hGFT : (G.over U).IsFiniteType := hFT
  obtain ⟨ι, hι, r, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact U hU
  have : Finite ι := hι
  have hri (i : ι) : PrimeSpectrum.basicOpen (r i) ≤ U := by
    rw [hr]
    exact le_iSup (fun i : ι => PrimeSpectrum.basicOpen (r i)) i
  have hFinite (i : ι) :
      ((⊤ : Submodule R ((moduleSpecΓFunctor (R := R)).obj G)).localized
        (Submonoid.powers (r i))).FG :=
    fg_localized_top_of_isFiniteType_over_basicOpen G (r i)
      (SheafOfModules.IsFiniteType.over_of_le G (hri i) hGFT)
  obtain ⟨N, hNH, hNQC, hNFT, hEq⟩ :=
    exists_finiteType_submodule_eq_on_basicOpens F H r hFinite
  refine ⟨N, hNH, hNQC, hNFT, ?_⟩
  exact SheafOfModules.Submodule.over_eq_of_iSup_eq N H U
    (fun i : ι => PrimeSpectrum.basicOpen (r i)) hr.symm hEq

end AlgebraicGeometry.Scheme.Modules
