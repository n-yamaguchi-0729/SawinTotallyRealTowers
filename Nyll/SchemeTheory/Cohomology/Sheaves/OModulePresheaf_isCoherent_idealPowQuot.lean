/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafIdealFiltration

/-!
Coherence of quotients of a coherent module presheaf by ideal powers.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_isCoherent_idealPowQuot

open _root_.AlgebraicGeometry
open _root_.CategoryTheory
open _root_.TopologicalSpace
open _root_.Opposite

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
namespace G4T
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

universe u

section Closure

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem isCoherent_idealPowQuot [IsLocallyNoetherian V] (I : V.IdealSheafData)
    (F : OModulePresheaf π) (k : ℕ) (hFc : OModulePresheaf.IsCoherent F) :
    OModulePresheaf.IsCoherent (idealPowQuot π I F k) := fun U => by
  let : Module R Γ(V, U.1) :=
    (Scheme.TwoAffineOpenCover.algebraOfHom π U.1).toModule
  have : IsScalarTower R Γ(V, U.1) (F.obj U.1) := F.isScalarTower U.1
  have : IsNoetherianRing Γ(V, U.1) := IsLocallyNoetherian.component_noetherian U
  have : Module.Finite Γ(V, U.1) (F.obj U.1) := hFc U
  have hNoetherian : _root_.IsNoetherian Γ(V, U.1) (F.obj U.1) :=
    isNoetherian_of_isNoetherianRing_of_finite Γ(V, U.1) (F.obj U.1)
  have : Module.Finite Γ(V, U.1) ((idealPow π I F k).obj U.1) := by
    change Module.Finite Γ(V, U.1)
      ↥((idealSections I U.1 ^ k • (⊤ : Submodule Γ(V, U.1) (F.obj U.1))) :
        Submodule Γ(V, U.1) (F.obj U.1))
    have : _root_.IsNoetherian Γ(V, U.1)
        ↥((idealSections I U.1 ^ k • (⊤ : Submodule Γ(V, U.1) (F.obj U.1))) :
          Submodule Γ(V, U.1) (F.obj U.1)) :=
      isNoetherian_of_submodule_of_noetherian Γ(V, U.1) (F.obj U.1)
        (idealSections I U.1 ^ k • (⊤ : Submodule Γ(V, U.1) (F.obj U.1))) hNoetherian
    exact Module.IsNoetherian.finite _ _
  exact Module.Finite.of_surjective ((idealPowSES π I F k).proj.appSections U)
    ((idealPowSES π I F k).surjective U)

end Closure

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs in
open _root_.AlgebraicGeometry OModulePresheaf_isCoherent_idealPowQuot.AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.OModulePresheaf.isCoherent_idealPowQuot {R : Type u} [CommRing R]
    {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsLocallyNoetherian V] (I : V.IdealSheafData) (F :
    OModulePresheaf π) (k : ℕ) (hFc : F.IsCoherent) : (OModulePresheaf.idealPowQuot π I F
    k).IsCoherent :=
  AlgebraicGeometry.OModulePresheaf.G4T.isCoherent_idealPowQuot π I F k hFc
end AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_isCoherent_idealPowQuot
end ProofImplementation
