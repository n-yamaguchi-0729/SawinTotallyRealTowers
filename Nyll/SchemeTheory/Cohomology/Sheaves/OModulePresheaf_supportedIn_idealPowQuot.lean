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
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafIdealFiltration

/-!
Support of a module-presheaf quotient by an ideal power.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_supportedIn_idealPowQuot

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

theorem supportedIn_idealPowQuot (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ)
    {Y : Closeds V} (hFs : OModulePresheaf.SupportedIn F Y) :
    OModulePresheaf.SupportedIn (idealPowQuot π I F k) Y := fun U hU => by
  have := hFs U hU
  have : Subsingleton ((idealPow π I F k).obj U.1) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := (idealPowSuccSub π I F k U.1).mkQ_surjective a
    obtain ⟨b', rfl⟩ := (idealPowSuccSub π I F k U.1).mkQ_surjective b
    exact congrArg _ (Subsingleton.elim a' b')⟩

end Closure

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs in
open _root_.AlgebraicGeometry OModulePresheaf_supportedIn_idealPowQuot.AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.OModulePresheaf.supportedIn_idealPowQuot {R : Type u} [CommRing
    R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (I : V.IdealSheafData) (F : OModulePresheaf π) (k :
    ℕ) {Y : TopologicalSpace.Closeds V} (hFs : F.SupportedIn Y) : (OModulePresheaf.idealPowQuot π
    I F k).SupportedIn Y :=
  AlgebraicGeometry.OModulePresheaf.G4T.supportedIn_idealPowQuot π I F k hFs
end AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_supportedIn_idealPowQuot
end ProofImplementation
