/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_isPullback_toProj_of_faithfullyFlat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.Modules.ProjectivePresentation
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Nyll.SchemeTheory.Modules.FlatSectionsBaseChange
import Nyll.SchemeTheory.Modules.SpanningFrameDescent
import Nyll.SchemeTheory.Modules.ProjectivePresentationFromFrames
import Nyll.SchemeTheory.Modules.ProjectivePresentationBaseChange
import Nyll.SchemeTheory.Modules.ProjectivePresentationIso
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! Faithfully flat descent of projective presentations. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Scheme.Modules

/-- A projective presentation descends through a faithfully flat base change. -/
theorem exists_projPresentation_isPullback_toProj_of_faithfullyFlat
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S
      S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [IsSeparated f]
    (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (L' : X'.Modules)
    (e : (Scheme.Modules.pullback c).obj L ≅ L')
    {M : ℕ} (𝔔 : Scheme.Modules.ProjPresentation L' f' M) :
    ∃ (N : ℕ) (𝔓 : Scheme.Modules.ProjPresentation L f N) (𝔓' : Scheme.Modules.ProjPresentation L'
      f' N),
      IsPullback c 𝔓'.toProj 𝔓.toProj (ProjSpace.map S S' N) ∧
      ∀ j : Fin (M + 1), ∃ a : Fin (N + 1) → S',
        𝔔.σ j = ∑ l, ((f'.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S')).inv.hom (a
          l))) • 𝔓'.σ l := by
  classical
  let iS : Algebra S Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom.toAlgebra
  let iSL : Module S Γ(L, ⊤) := Module.compHom _ (algebraMap S Γ(X, ⊤))
  let iS' : Algebra S' Γ(X', ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫
    f'.appTop).hom.toAlgebra
  let iS'L : Module S' Γ((Scheme.Modules.pullback c).obj L, ⊤) := Module.compHom _ (algebraMap S'
    Γ(X', ⊤))
  obtain ⟨𝔔₀, hQ₀t, hQ₀σ⟩ := ProjPresentation.exists_of_iso 𝔔
    e.symm
  obtain ⟨β, hβ⟩ :=
    IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_of_flat S' f f' c hc L hL
  have hdec : ∀ j : Fin (M + 1), ∃ T : Finset (S' × Γ(L, ⊤)), β.symm (𝔔₀.σ j) = ∑ i ∈ T, i.1 ⊗ₜ[S]
    i.2 :=
    fun j => TensorProduct.exists_finset _
  choose T hT using hdec
  let N : ℕ := Fintype.card (Σ j : Fin (M + 1), ↥(T j))
  have hcard : Fintype.card (Option (Σ j : Fin (M + 1), ↥(T j))) = N + 1 :=
    by rw [Fintype.card_option]
  let eI : Option (Σ j : Fin (M + 1), ↥(T j)) ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hcard
  let σfun : Option (Σ j : Fin (M + 1), ↥(T j)) → Γ(L, ⊤) := fun o => match o with
    | none => 0
    | some x => x.2.1.2
  let coef : Fin (M + 1) → Option (Σ j : Fin (M + 1), ↥(T j)) → S' := fun j o => match o with
    | none => 0
    | some x => if x.1 = j then x.2.1.1 else 0
  let σ : Fin (N + 1) → Γ(L, ⊤) := fun l => σfun (eI.symm l)
  let a : Fin (M + 1) → Fin (N + 1) → S' := fun j l => coef j (eI.symm l)
  have key : ∀ (Rs V : Type u) [Semiring Rs] [AddCommMonoid V] [Module Rs V] (φ : S' → Rs) (hφ : φ
    0 = 0)
      (ψ : Γ(L, ⊤) → V) (j : Fin (M + 1)),
      ∑ l : Fin (N + 1), φ (a j l) • ψ (σ l) = ∑ i ∈ T j, φ i.1 • ψ i.2 := by
    intro Rs V _ _ _ φ hφ ψ j
    have h1 : ∑ l : Fin (N + 1), φ (a j l) • ψ (σ l) = ∑ o : Option (Σ j : Fin (M + 1), ↥(T j)), φ
      (coef j o) • ψ (σfun o) := by
      rw [← Equiv.sum_comp eI.symm]
    rw [h1, Fintype.sum_option]
    have h0 : φ (coef j none) • ψ (σfun none) = 0 := by
      change φ 0 • ψ 0 = 0
      rw [hφ, zero_smul]
    rw [h0, zero_add]
    have h2 : ∀ x : (Σ j : Fin (M + 1), ↥(T j)), φ (coef j (some x)) • ψ (σfun (some x)) = if x.1 =
      j then φ x.2.1.1 • ψ x.2.1.2 else 0 := by
      intro x
      change φ (if x.1 = j then x.2.1.1 else 0) • ψ x.2.1.2 = _
      split_ifs
      · rfl
      · rw [hφ, zero_smul]
    simp_rw [h2]
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    exact Finset.sum_coe_sort (T j) (fun i => φ i.1 • ψ i.2)
  let σ' : Fin (N + 1) → Γ((Scheme.Modules.pullback c).obj L, ⊤) := fun l => β ((1 : S') ⊗ₜ[S] σ l)
  have hσ' : ∀ l, σ' l = (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app L).app ⊤) (σ
    l) := fun l => hβ (σ l)
  have hρ : ∀ j : Fin (M + 1), 𝔔₀.σ j = ∑ l, (algebraMap S' (X'.presheaf.obj (Opposite.op ⊤)) (a j
    l)) • σ' l := by
    intro j
    rw [key _ _ (algebraMap S' (X'.presheaf.obj (Opposite.op ⊤))) (map_zero _) (fun m => β ((1 :
      S') ⊗ₜ[S] m)) j]
    have h1 : 𝔔₀.σ j = β (β.symm (𝔔₀.σ j)) := (β.apply_symm_apply _).symm
    rw [h1, hT j, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 : i.1 ⊗ₜ[S] i.2 = i.1 • ((1 : S') ⊗ₜ[S] i.2) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h2, LinearEquiv.map_smul]
    rfl
  let U' : Fin (M + 1) → X'.Opens := fun j =>
    𝔔₀.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (M + 1)) S')
      (MvPolynomial.X j)
  have hU' : iSup U' = ⊤ := by
    have h : ⨆ i : Fin (M + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (M + 1)) S')
        (MvPolynomial.X i) = ⊤ :=
      Proj.iSup_basicOpen_eq_top _ (fun i => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X S' M)
    refine le_antisymm le_top fun y _ => ?_
    have hy : 𝔔₀.toProj.base y ∈ (⊤ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (M + 1))
      S')).Opens) := trivial
    rw [← h] at hy
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  have : Surjective c := by
    have hs : Surjective (Spec.map (CommRingCat.ofHom (algebraMap S S'))) :=
      ⟨by rw [Spec.map_base]; exact PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
    exact MorphismProperty.of_isPullback (P := @Surjective) hc.flip hs
  obtain ⟨U, hU, hframe⟩ :=
    IsInvertible.exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective
      c L hL σ σ' hσ' 𝔔₀.σ U' hU' (fun j V' hV' => 𝔔₀.frame j V' hV') (fun j => ⟨fun l =>
        algebraMap S' (X'.presheaf.obj (Opposite.op ⊤)) (a j l), hρ j⟩)
  obtain ⟨𝔓, h𝔓σ, -⟩ := exists_projPresentation_of_iSup_eq_top f L
    N σ U hU hframe
  obtain ⟨𝔓'₀, hσ'₀, -, hsq₀⟩ :=
    ProjPresentation.exists_baseChange_of_isPullback hc 𝔓
  obtain ⟨𝔓', htp, hσ'e⟩ := ProjPresentation.exists_of_iso 𝔓'₀ e
  refine ⟨N, 𝔓, 𝔓', by rw [htp]; exact hsq₀, fun j => ⟨a j, ?_⟩⟩
  have hQσ : 𝔔.σ j = (e.hom.app ⊤) (𝔔₀.σ j) := by
    rw [hQ₀σ j]
    change 𝔔.σ j = ((e.symm.hom ≫ e.hom).app ⊤) (𝔔.σ j)
    rw [Iso.symm_hom, Iso.inv_hom_id]
    rfl
  have hPσ : ∀ l, 𝔓'.σ l = (e.hom.app ⊤) (σ' l) := by
    intro l; rw [hσ'e l, hσ'₀ l, h𝔓σ, hσ' l]
  rw [hQσ, hρ j, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Scheme.Modules.Hom.app_smul, hPσ l]
  congr 1
  change ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appTop).hom (a j l) = (f'.appLE ⊤ ⊤
    le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S')).inv.hom (a j l))
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

end AlgebraicGeometry.Scheme.Modules
