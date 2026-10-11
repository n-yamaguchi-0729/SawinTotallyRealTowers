/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# is Iso of is Iso pullback closed Fibre of is Finite of etale of is Proper
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace F1dE121

private theorem exists_specializes_over_closedPoint {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f] (x : X) :
    ∃ x' : X, x ⤳ x' ∧ f.base x' = IsLocalRing.closedPoint R := by
  have hclosed : IsClosed (f.base '' closure {x}) := f.isClosedMap _ isClosed_closure
  have hfx : f.base x ∈ f.base '' closure {x} := ⟨x, subset_closure rfl, rfl⟩
  have hspec : f.base x ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint _
  have hmem : IsLocalRing.closedPoint R ∈ f.base '' closure {x} := hspec.mem_closed hclosed hfx
  obtain ⟨x', hx', hfx'⟩ := hmem
  exact ⟨x', specializes_iff_mem_closure.mpr hx', hfx'⟩

private theorem closedPoint_mem_range_residue {R : Type u} [CommRing R] [IsLocalRing R] :
    IsLocalRing.closedPoint R ∈
      Set.range (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))).base := by
  refine ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField R), ?_⟩
  change PrimeSpectrum.comap (IsLocalRing.residue R) (IsLocalRing.closedPoint _) = _
  exact IsLocalRing.comap_closedPoint (IsLocalRing.residue R)

private theorem apply_eq_of_specializes {α β : Type*} [TopologicalSpace α] {g : α → β}
    (hg : IsLocallyConstant g) {x x' : α} (h : x ⤳ x') : g x' = g x := by
  have hclopen : IsClopen (g ⁻¹' {g x}) := hg.isClopen_fiber (g x)
  exact h.mem_closed hclopen.isClosed (Set.mem_singleton (g x))

end F1dE121

open F1dE121 in
theorem
  _root_.AlgebraicGeometry.isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X U : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (π : U ⟶ X) [IsFinite π] [AlgebraicGeometry.Etale π]
    (hk : IsIso (pullback.snd π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue
      R)))))) :
    IsIso π := by
  set ι := pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) with hι
  rw [Scheme.Hom.isIso_iff_finrank_eq]
  have hlc : IsLocallyConstant (Scheme.Hom.finrank π) := Scheme.Hom.isLocallyConstant_finrank π
  have hfib : ∀ y, Scheme.Hom.finrank π (ι.base y) = 1 := by
    intro y
    have h := Scheme.Hom.finrank_pullback_snd π ι y
    rw [Scheme.Hom.finrank_eq_one_of_isIso] at h
    exact h.symm
  funext x
  obtain ⟨x', hxx', hfx'⟩ := F1dE121.exists_specializes_over_closedPoint f x
  have hx'range : x' ∈ Set.range ι.base := by
    rw [hι, Scheme.Pullback.range_fst]
    change f.base x' ∈ Set.range _
    rw [hfx']
    exact F1dE121.closedPoint_mem_range_residue
  obtain ⟨y, rfl⟩ := hx'range
  rw [← F1dE121.apply_eq_of_specializes hlc hxx', hfib y]
  rfl
end isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
