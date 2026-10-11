/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverOf

/-!
# Injectivity of the affine-cover augmentation

The augmentation from sections on an open into the degree-zero Cech cochains of its
ordered affine cover is injective.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_OrderedAffineCoverOf_aug_injective

open _root_.AlgebraicGeometry
open _root_.CategoryTheory
open _root_.TopologicalSpace
open _root_.Opposite

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace OrderedAffineCoverOf
open _root_.AlgebraicGeometry.Scheme.OrderedAffineCoverOf
namespace Acyclic
open _root_.AlgebraicGeometry.Scheme.OrderedAffineCoverOf
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

universe u
section ResHelpers

variable {V : Scheme.{u}}

theorem res_refl {O : V.Opens} (h : O ≤ O) (x : Γ(V, O)) :
    (V.presheaf.map (homOfLE h).op).hom x = x := by
  have : (homOfLE h : O ⟶ O) = 𝟙 O := rfl
  rw [this, op_id, V.presheaf.map_id]; rfl

theorem res_res {O₁ O₂ O₃ : V.Opens} (h12 : O₁ ≤ O₂) (h23 : O₂ ≤ O₃)
    (x : Γ(V, O₃)) :
    (V.presheaf.map (homOfLE h12).op).hom ((V.presheaf.map (homOfLE h23).op).hom x)
      = (V.presheaf.map (homOfLE (h12.trans h23)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl

theorem altC_at_eq {W : V.Opens} {K : Scheme.OrderedAffineCoverOf W}
    {n : ℕ} (z : K.cochain n) {σ τ : K.Idx n} (h : σ = τ)
    {O : V.Opens} (hσ : O ≤ K.inter σ) (hτ : O ≤ K.inter τ) :
    (V.presheaf.map (homOfLE hσ).op).hom (z σ)
      = (V.presheaf.map (homOfLE hτ).op).hom (z τ) := by
  subst h; rfl

end ResHelpers

section Idx0
variable {V : Scheme.{u}} {W : V.Opens} (K : Scheme.OrderedAffineCoverOf W) (i₀ : K.ι)

/-- The degree-zero Cech index determined by a single cover member. -/
def idx0 : K.Idx 0 :=
  ⟨fun _ => i₀, fun a b h => absurd (Subsingleton.elim (α := Fin 1) a b) (ne_of_lt h)⟩
end Idx0

section CoverOf
variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))
include π

theorem aug_injective {W : V.Opens} (K : Scheme.OrderedAffineCoverOf W) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    Function.Injective (K.aug π) := by
  let := Scheme.OrderedAffineCoverOf.moduleSections π
  intro w₁ w₂ hw
  have hcov : W ≤ ⨆ σ : K.Idx 0, K.inter σ :=
    K.iSup_eq.ge.trans (iSup_le fun i => le_iSup_of_le (idx0 K i)
      (le_iInf fun _ => le_rfl))
  exact V.sheaf.eq_of_locally_eq' (K.inter (i := 0)) W
    (fun σ => homOfLE (K.inter_le_base σ)) hcov w₁ w₂ fun σ => congrFun hw σ
end CoverOf

end AlgebraicGeometry.Scheme.OrderedAffineCoverOf.Acyclic

end

universe u

with_weak_namespace _root_.AlgebraicCurves.Geometry.Schemes.Proofs
open _root_.AlgebraicGeometry Scheme_OrderedAffineCoverOf_aug_injective.AlgebraicGeometry in
with_weak_namespace Scheme_OrderedAffineCoverOf_aug_injective
theorem _root_.AlgebraicGeometry.Scheme.OrderedAffineCoverOf.aug_injective {R : Type u}
    [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) {W : V.Opens}
    (K : V.OrderedAffineCoverOf W) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    Function.Injective (K.aug π) :=
  Scheme.OrderedAffineCoverOf.Acyclic.aug_injective π K
end AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_OrderedAffineCoverOf_aug_injective
end ProofImplementation
