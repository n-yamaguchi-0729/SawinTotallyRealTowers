/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_existsUnique_hom_app_eq_of_iSup_eq_top.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Scheme Modules exists Unique hom app eq of i Sup eq top
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.HomGluing

open CategoryTheory Opposite AlgebraicGeometry

universe u v

theorem _root_.AlgebraicGeometry.Scheme.Modules.existsUnique_hom_app_eq_of_iSup_eq_top
    {X : Scheme.{u}} (M N : X.Modules) {ι : Type v} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (f : ∀ (W : X.Opens), (∃ i, W ≤ U i) → (Γ(M, W) →ₗ[Γ(X, W)] Γ(N, W)))
    (hf : ∀ (W W' : X.Opens) (hW : ∃ i, W ≤ U i) (h : W' ≤ W) (x : Γ(M, W)),
      N.presheaf.map (homOfLE h).op (f W hW x) = f W' (hW.imp fun _ hi => h.trans hi)
        (M.presheaf.map (homOfLE h).op x)) :
    ∃! F : M ⟶ N, ∀ (W : X.Opens) (hW : ∃ i, W ≤ U i) (x : Γ(M, W)), F.app W x = f W hW x := by
  classical
  let β : Type u := {W : X.Opens // ∃ i, W ≤ U i}
  let B : β → X.Opens := fun b => b.1
  have hB : TopologicalSpace.Opens.IsBasis (Set.range B) :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {W} {x} hx => by
      have hx' : x ∈ (⨆ i, U i) := by rw [hU]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
      exact ⟨W ⊓ U i, ⟨⟨W ⊓ U i, i, inf_le_right⟩, rfl⟩, ⟨hx, hi⟩, inf_le_left⟩
  let N' : TopCat.Sheaf Ab X := ⟨N.val.presheaf, N.isSheaf⟩
  have hext : ∀ (V : X.Opens) (a c : Γ(N, V)),
      (∀ (b : β) (hbV : B b ≤ V),
        N.presheaf.map (homOfLE hbV).op a = N.presheaf.map (homOfLE hbV).op c) → a = c := by
    intro V a c h
    have hcov : V ≤ iSup (fun k : {b : β // B b ≤ V} => B k.1) := by
      intro x hx
      obtain ⟨W', ⟨b, rfl⟩, hxW', hW'V⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp hB hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨b, hW'V⟩, hxW'⟩
    exact N'.eq_of_locally_eq' (fun k : {b : β // B b ≤ V} => B k.1) V (fun k => homOfLE k.2) hcov
      a c
      (fun k => h k.1 k.2)
  let α : (inducedFunctor B).op ⋙ M.val.presheaf ⟶ (inducedFunctor B).op ⋙ N.val.presheaf :=
    { app := fun b => AddCommGrpCat.ofHom (f (B b.unop) b.unop.2).toAddMonoidHom
      naturality := fun {b b'} g => by
        ext x
        exact (hf (B b.unop) (B b'.unop) b.unop.2 g.unop.hom.le x).symm }
  obtain ⟨φ, hφ⟩ : ∃ φ : M.val.presheaf ⟶ N.val.presheaf, ∀ b : β, φ.app (op (B b)) = α.app (op b)
    :=
    ⟨TopCat.Sheaf.restrictHomEquivHom M.val.presheaf N' hB α, TopCat.Sheaf.extend_hom_app
      M.val.presheaf N' hB α⟩
  let φ' : ∀ V : X.Opens, Γ(M, V) → Γ(N, V) := fun V x => φ.app (op V) x
  have hφ' : ∀ (b : β) (x : Γ(M, B b)), φ' (B b) x = f (B b) b.2 x := fun b x => by
    change φ.app (op (B b)) x = _
    rw [hφ b]; rfl
  have hnat : ∀ (V V' : X.Opens) (h : V' ≤ V) (x : Γ(M, V)),
      N.presheaf.map (homOfLE h).op (φ' V x) = φ' V' (M.presheaf.map (homOfLE h).op x) :=
    fun V V' h x => (NatTrans.naturality_apply φ (homOfLE h).op x).symm
  have hlin : ∀ (V : X.Opens) (r : Γ(X, V)) (m : Γ(M, V)), φ' V (r • m) = r • φ' V m := by
    intro V r m
    apply hext V
    intro b hbV
    rw [hnat, Scheme.Modules.map_smul, hφ', map_smul, Scheme.Modules.map_smul, hnat, hφ']
  let F : M ⟶ N := ⟨PresheafOfModules.homMk φ fun W r m => hlin W.unop r m⟩
  have hF : ∀ (W : X.Opens) (hW : ∃ i, W ≤ U i) (x : Γ(M, W)), F.app W x = f W hW x :=
    fun W hW x => hφ' ⟨W, hW⟩ x
  refine ⟨F, hF, fun G hG => ?_⟩
  apply (Scheme.Modules.toPresheaf X).map_injective
  refine TopCat.Sheaf.hom_ext M.val.presheaf N' hB fun b => ?_
  ext x
  change G.app (B b) x = F.app (B b) x
  rw [hG (B b) b.2 x, hF (B b) b.2 x]
end AlgebraicCurves.Geometry.Sheaves.Proofs.HomGluing
end ProofImplementation
