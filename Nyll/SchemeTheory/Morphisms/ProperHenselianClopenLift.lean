/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.ProperHenselianClosedRestriction
import Nyll.SchemeTheory.Topology.SpectralClosedRestriction
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Clopen lifting from the closed fibre over an arbitrary Henselian local ring

The scheme-theoretic closed fibre is identified with its actual closed subset
in the proper total space. The spectral closed-restriction theorem then lifts
each clopen subset. No Noetherian hypothesis is required.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- Every clopen subset of the scheme-theoretic closed fibre of a proper
scheme over a Henselian local ring extends to a clopen subset of that scheme. -/
theorem exists_isClopen_closedFiber_preimage_eq_of_isProper_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (V : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))))
    (hV : IsClopen V) :
    ∃ U : Set X, IsClopen U ∧
      pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ⁻¹' U = V := by
  let q : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
      Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hq : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  let p : pullback f q ⟶ X := pullback.fst f q
  have hqrange : Set.range q = {IsLocalRing.closedPoint R} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      have hz : z = IsLocalRing.closedPoint (IsLocalRing.ResidueField R) :=
        Subsingleton.elim _ _
      rw [hz]
      exact IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField R),
        IsLocalRing.comap_closedPoint (IsLocalRing.residue R)⟩
  have hrange : Set.range p = f ⁻¹' {IsLocalRing.closedPoint R} := by
    rw [Scheme.Pullback.range_fst, hqrange]
  let e : ↥(pullback f q) ≃ₜ (f ⁻¹' {IsLocalRing.closedPoint R}) :=
    p.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  let W : Clopens (f ⁻¹' {IsLocalRing.closedPoint R}) :=
    ⟨e.symm ⁻¹' V, hV.preimage e.symm.continuous⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : SpectralSpace X := {}
  obtain ⟨U, hU⟩ := (SchemeTheory.clopen_restriction_bijective
    ((IsLocalRing.isClosed_singleton_closedPoint (R := R)).preimage f.continuous)
    (isConnected_closedFiber_inter_closure f)).surjective W
  refine ⟨U, U.isClopen, ?_⟩
  ext x
  have hx := Iff.of_eq (congrArg (fun C : Clopens (f ⁻¹' {IsLocalRing.closedPoint R}) =>
    e x ∈ C) hU)
  change p x ∈ U ↔ e.symm (e x) ∈ V at hx
  rw [e.symm_apply_apply] at hx
  exact hx

end AlgebraicGeometry
