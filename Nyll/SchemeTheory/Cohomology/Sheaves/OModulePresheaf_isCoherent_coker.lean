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
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions

/-!
Coherence of the cokernel of a morphism of module presheaves.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_isCoherent_coker

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

section PModAlg
variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G)

theorem isCoherent_coker (hG : OModulePresheaf.IsCoherent G) :
    OModulePresheaf.IsCoherent (OModulePresheaf.coker φ) := fun U => by
  have := hG U
  exact Module.Finite.of_surjective ((OModulePresheaf.imCokerSES φ).proj.appSections U.1)
    ((OModulePresheaf.imCokerSES φ).surjective U.1)

end PModAlg

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs in
open _root_.AlgebraicGeometry OModulePresheaf_isCoherent_coker.AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.OModulePresheaf.isCoherent_coker {R : Type u} [CommRing R] {V :
    Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G) (hG
    : G.IsCoherent) : (OModulePresheaf.coker φ).IsCoherent :=
  AlgebraicGeometry.OModulePresheaf.G4T.isCoherent_coker φ hG
end AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_isCoherent_coker
end ProofImplementation
