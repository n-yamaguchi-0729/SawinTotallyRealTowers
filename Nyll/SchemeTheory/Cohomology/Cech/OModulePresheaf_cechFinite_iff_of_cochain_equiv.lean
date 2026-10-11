/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Mathlib.RingTheory.Finiteness.Basic

/-!
Finiteness of Cech cohomology is invariant under a cochain equivalence commuting with differentials.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.OModulePresheaf_cechFinite_iff_of_cochain_equiv

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open _root_.Opposite

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

section CochainEquiv

variable {R : Type u} [CommRing R] {V V' : Scheme.{u}} {π : V ⟶ Spec (.of R)} {π' : V' ⟶ Spec (.of
  R)}
variable (F : OModulePresheaf π) (G : OModulePresheaf π') (K : V.OrderedAffineCover) (K' :
  V'.OrderedAffineCover)
variable (e : ∀ q, F.cochain K q ≃ₗ[R] G.cochain K' q)
variable (he : ∀ q x, e (q + 1) (F.d K q x) = G.d K' q (e q x))

include he in
theorem d_comp_equiv (q : ℕ) :
    G.d K' q ∘ₗ (e q : F.cochain K q →ₗ[R] G.cochain K' q) = (e (q + 1) : _ →ₗ[R] _) ∘ₗ F.d K q :=
  LinearMap.ext fun x => (he q x).symm

include he in
theorem map_ker_d (q : ℕ) :
    Submodule.map (e q : F.cochain K q →ₗ[R] G.cochain K' q) (LinearMap.ker (F.d K q)) =
      LinearMap.ker (G.d K' q) := by
  rw [Submodule.map_equiv_eq_comap_symm, ← LinearMap.ker_comp, ← LinearEquiv.ker_comp (e (q + 1))]
  congr 1
  refine LinearMap.ext fun y => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [he, LinearEquiv.apply_symm_apply]

/--
The induced equivalence of cocycles from a cochain equivalence commuting with the differentials.
-/
def kerEquiv (q : ℕ) : LinearMap.ker (F.d K q) ≃ₗ[R] LinearMap.ker (G.d K' q) :=
  LinearEquiv.ofSubmodules (e q) _ _ (map_ker_d F G K K' e he q)

theorem kerEquiv_apply_coe (q : ℕ) (x : LinearMap.ker (F.d K q)) :
    (kerEquiv F G K K' e he q x).1 = e q x.1 := rfl

include he in
theorem map_comap_range (q : ℕ) :
    Submodule.map (kerEquiv F G K K' e he (q + 1) : _ →ₗ[R] _)
        ((LinearMap.range (F.d K q)).comap (LinearMap.ker (F.d K (q + 1))).subtype)
      = (LinearMap.range (G.d K' q)).comap (LinearMap.ker (G.d K' (q + 1))).subtype := by
  ext y
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range]
  constructor
  · rintro ⟨x, ⟨z, hz⟩, rfl⟩
    exact ⟨e q z, by change G.d K' q (e q z) = e (q + 1) x.1; rw [← he, hz]⟩
  · rintro ⟨z, hz⟩
    refine ⟨(kerEquiv F G K K' e he (q + 1)).symm y, ⟨(e q).symm z, ?_⟩,
      LinearEquiv.apply_symm_apply _ _⟩
    apply (e (q + 1)).injective
    rw [he, LinearEquiv.apply_symm_apply, hz]
    exact (congrArg Subtype.val ((kerEquiv F G K K' e he (q + 1)).apply_symm_apply y)).symm

/--
The induced equivalence on positive Cech cohomology, obtained by quotienting the cocycle
equivalence.
-/
def hSuccEquiv (q : ℕ) : F.HSucc K q ≃ₗ[R] G.HSucc K' q :=
  Submodule.Quotient.equiv _ _ (kerEquiv F G K K' e he (q + 1)) (map_comap_range F G K K' e he q)

include he in
theorem cechFinite_iff_of_cochainEquiv : F.CechFinite K ↔ G.CechFinite K' := by
  rw [OModulePresheaf.cechFinite_iff, OModulePresheaf.cechFinite_iff]
  refine ⟨fun ⟨h0, h⟩ => ⟨?_, fun q => ?_⟩, fun ⟨h0, h⟩ => ⟨?_, fun q => ?_⟩⟩
  · have := h0; exact Module.Finite.equiv (kerEquiv F G K K' e he 0)
  · have := h q; exact Module.Finite.equiv (hSuccEquiv F G K K' e he q)
  · have := h0; exact Module.Finite.equiv (kerEquiv F G K K' e he 0).symm
  · have := h q; exact Module.Finite.equiv (hSuccEquiv F G K K' e he q).symm

end CochainEquiv

end AlgebraicGeometry.OModulePresheaf

end

theorem _root_.AlgebraicGeometry.OModulePresheaf.cechFinite_iff_of_cochain_equiv
    {R : Type u} [CommRing R] {V V' : Scheme.{u}} {π : V ⟶ Spec (.of R)} {π' : V' ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (G : OModulePresheaf π') (K : V.OrderedAffineCover) (K' :
      V'.OrderedAffineCover)
    (e : ∀ q, F.cochain K q ≃ₗ[R] G.cochain K' q) (he : ∀ q x, e (q + 1) (F.d K q x) = G.d K' q (e
      q x)) :
    F.CechFinite K ↔ G.CechFinite K' :=
  AlgebraicGeometry.OModulePresheaf.cechFinite_iff_of_cochainEquiv F G K K' e he
end AlgebraicCurves.Cohomology.Cech.Proofs.OModulePresheaf_cechFinite_iff_of_cochain_equiv
end ProofImplementation
