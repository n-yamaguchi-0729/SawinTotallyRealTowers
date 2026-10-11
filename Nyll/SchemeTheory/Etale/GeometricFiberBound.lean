/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.AffineGeometricFiberBound
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Compactness.Compact


/-!
# Uniform geometric-fiber bounds from a compact étale source

An étale morphism with quasi-compact source has a uniform finite bound on
all actual geometric fibers. The target is arbitrary. The proof uses the
native affine refinement of the pullback of an affine target cover, then
compactness selects finitely many of those source charts.

Each selected chart maps to an affine target chart, where the existing
affine bound applies. A field-valued point either misses that target chart
or lifts through its open immersion; the existing pullback universal
property compares the actual fibers. Finally the pulled-back source charts
cover each geometric fiber, so the sum of their bounds is a uniform bound.

This supplies the initial bound required by the degree induction in Stacks
Project, Tag 09Z0, after its existing affine-source reduction.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

private theorem exists_uniform_geometricFiber_bound_affine
    {U X : Scheme.{u}} [IsAffine U] [IsAffine X] (f : U ⟶ X) [Etale f] :
    ∃ N : ℕ, ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (CommRingCat.of Ω) ⟶ X),
      Finite (pullback f s : Scheme.{u}) ∧ Nat.card (pullback f s : Scheme.{u}) ≤ N := by
  let φ : Spec Γ(U, ⊤) ⟶ Spec Γ(X, ⊤) := Spec.map f.appTop
  have : Etale φ := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (HasRingHomProperty.appTop (P := @Etale) f (inferInstance : Etale f))
  obtain ⟨N, hN⟩ := exists_uniform_geometricFiber_bound_spec φ
  refine ⟨N, ?_⟩
  intro Ω _ _ s
  let m : pullback f s ⟶ pullback φ (s ≫ X.isoSpec.hom) :=
    pullback.map f s φ (s ≫ X.isoSpec.hom) U.isoSpec.hom (𝟙 _) X.isoSpec.hom
      (Scheme.isoSpec_hom_naturality f).symm (Category.id_comp _).symm
  have : IsIso m := by
    dsimp only [m]
    infer_instance
  let E : pullback f s ≅ pullback φ (s ≫ X.isoSpec.hom) := asIso m
  have : Finite (pullback φ (s ≫ X.isoSpec.hom) : Scheme.{u}) :=
    (hN Ω (s ≫ X.isoSpec.hom)).1
  exact ⟨Finite.of_injective m m.injective,
    (Nat.card_congr E.schemeIsoToHomeo.toEquiv).trans_le
      (hN Ω (s ≫ X.isoSpec.hom)).2⟩

private theorem geometricFiber_bound_postcomp_open
    {A V X : Scheme.{u}} (h : A ⟶ V) (j : V ⟶ X) [IsOpenImmersion j]
    (N : ℕ)
    (hN : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (CommRingCat.of Ω) ⟶ V),
      Finite (pullback h s : Scheme.{u}) ∧ Nat.card (pullback h s : Scheme.{u}) ≤ N)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ X) :
    Finite (pullback (h ≫ j) s : Scheme.{u}) ∧
      Nat.card (pullback (h ≫ j) s : Scheme.{u}) ≤ N := by
  classical
  by_cases hs : s default ∈ Set.range j
  · have hsj : Set.range s ⊆ Set.range j := by
      rintro _ ⟨x, rfl⟩
      rw [Subsingleton.elim x default]
      exact hs
    let t : Spec (CommRingCat.of Ω) ⟶ V := IsOpenImmersion.lift j s hsj
    have ht : t ≫ j = s := IsOpenImmersion.lift_fac j s hsj
    let E : pullback h t ≅ pullback (h ≫ j) (t ≫ j) :=
      (pullbackIsPullbackOfCompMono h t j).conePointUniqueUpToIso
        (pullback.isLimit (h ≫ j) (t ≫ j))
    have : Finite (pullback h t : Scheme.{u}) := (hN Ω t).1
    have hfinite : Finite (pullback (h ≫ j) (t ≫ j) : Scheme.{u}) :=
      Finite.of_injective E.inv E.inv.injective
    have hcard : Nat.card (pullback (h ≫ j) (t ≫ j) : Scheme.{u}) ≤ N :=
      (Nat.card_congr E.symm.schemeIsoToHomeo.toEquiv).trans_le (hN Ω t).2
    simpa only [ht] using And.intro hfinite hcard
  · have : IsEmpty (pullback (h ≫ j) s : Scheme.{u}) := by
      constructor
      intro w
      apply hs
      refine ⟨h (pullback.fst (h ≫ j) s w), ?_⟩
      have hw := congrArg
        (fun k : pullback (h ≫ j) s ⟶ X => k w)
        (pullback.condition (f := h ≫ j) (g := s))
      simpa only [Scheme.Hom.comp_apply,
        Subsingleton.elim (pullback.snd (h ≫ j) s w) default] using hw
    exact ⟨inferInstance, (Nat.card_of_isEmpty).trans_le (Nat.zero_le N)⟩

/-- A quasi-compact source supplies one finite bound on every geometric
fiber of an étale morphism, independently of the separably closed field and
its actual map to the arbitrary target. -/
theorem exists_uniform_geometricFiber_bound
    {U X : Scheme.{u}} [CompactSpace U] (f : U ⟶ X) [Etale f] :
    ∃ N : ℕ, ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (CommRingCat.of Ω) ⟶ X),
      Finite (pullback f s : Scheme.{u}) ∧ Nat.card (pullback f s : Scheme.{u}) ≤ N := by
  classical
  let B : X.OpenCover := X.affineOpenCover.openCover
  let P : U.OpenCover := B.pullback₁ f
  let A : U.OpenCover := (Scheme.OpenCover.affineRefinement P).openCover
  let e : A ⟶ P := Scheme.OpenCover.fromAffineRefinement P
  let j (i : A.I₀) : B.I₀ := e.s₀ i
  let h (i : A.I₀) : A.X i ⟶ B.X (j i) :=
    e.h₀ i ≫ B.pullbackHom f (j i)
  have hcomp (i : A.I₀) : h i ≫ B.f (j i) = A.f i ≫ f := by
    have he : e.h₀ i ≫ P.f (j i) = A.f i := e.w₀ i
    have hpull : B.pullbackHom f (j i) ≫ B.f (j i) = P.f (j i) ≫ f :=
      Scheme.Cover.pullbackHom_map B f (j i)
    calc
      h i ≫ B.f (j i) = e.h₀ i ≫ (B.pullbackHom f (j i) ≫ B.f (j i)) :=
        Category.assoc (e.h₀ i) (B.pullbackHom f (j i)) (B.f (j i))
      _ = e.h₀ i ≫ (P.f (j i) ≫ f) := congrArg (fun k => e.h₀ i ≫ k) hpull
      _ = (e.h₀ i ≫ P.f (j i)) ≫ f := (Category.assoc _ _ _).symm
      _ = A.f i ≫ f := congrArg (fun k => k ≫ f) he
  have hEtale (i : A.I₀) : Etale (h i) := by
    have : Etale (h i ≫ B.f (j i)) := by
      rw [hcomp i]
      infer_instance
    exact Etale.of_comp (h i) (B.f (j i))
  have chartBounds (i : A.I₀) :
      ∃ N : ℕ, ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (s : Spec (CommRingCat.of Ω) ⟶ B.X (j i)),
        Finite (pullback (h i) s : Scheme.{u}) ∧
          Nat.card (pullback (h i) s : Scheme.{u}) ≤ N := by
    have : IsAffine (A.X i) := by
      change IsAffine (Spec _)
      infer_instance
    have : IsAffine (B.X (j i)) := by
      change IsAffine (Spec _)
      infer_instance
    have : Etale (h i) := hEtale i
    exact exists_uniform_geometricFiber_bound_affine (h i)
  choose N hN using chartBounds
  have hcover : (Set.univ : Set U) ⊆ ⋃ i : A.I₀, Set.range (A.f i) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨A.idx x, A.covers x⟩
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set U)).elim_finite_subcover
    (fun i : A.I₀ => Set.range (A.f i))
    (fun i => IsOpenImmersion.isOpen_range (A.f i)) hcover
  refine ⟨∑ i : t, N i, ?_⟩
  intro Ω _ _ s
  have hchart (i : A.I₀) :
      Finite (pullback (A.f i ≫ f) s : Scheme.{u}) ∧
        Nat.card (pullback (A.f i ≫ f) s : Scheme.{u}) ≤ N i := by
    rw [← hcomp i]
    exact geometricFiber_bound_postcomp_open (h i) (B.f (j i)) (N i) (hN i) Ω s
  let E (i : t) : pullback (A.f i) (pullback.fst f s) ≅ pullback (A.f i ≫ f) s :=
    pullbackRightPullbackFstIso f s (A.f i)
  have hfinite (i : t) : Finite (pullback (A.f i) (pullback.fst f s) : Scheme.{u}) := by
    have : Finite (pullback (A.f i ≫ f) s : Scheme.{u}) := (hchart i).1
    exact Finite.of_injective (E i).hom (E i).hom.injective
  have : ∀ i : t, Finite (pullback (A.f i) (pullback.fst f s) : Scheme.{u}) := hfinite
  let ρ : (Σ i : t, (pullback (A.f i) (pullback.fst f s) : Scheme.{u})) →
      (pullback f s : Scheme.{u}) := fun z =>
    pullback.snd (A.f z.1) (pullback.fst f s) z.2
  have hρ : Function.Surjective ρ := by
    intro z
    obtain ⟨i, hit, v, hv⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (pullback.fst f s z)))
    obtain ⟨w, _, hw⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := A.f i) (g := pullback.fst f s) v z hv
    exact ⟨⟨⟨i, hit⟩, w⟩, hw⟩
  refine ⟨Finite.of_surjective ρ hρ, ?_⟩
  calc
    Nat.card (pullback f s : Scheme.{u}) ≤
        Nat.card (Σ i : t, (pullback (A.f i) (pullback.fst f s) : Scheme.{u})) :=
      Nat.card_le_card_of_surjective ρ hρ
    _ = ∑ i : t, Nat.card (pullback (A.f i) (pullback.fst f s) : Scheme.{u}) :=
      Nat.card_sigma
    _ ≤ ∑ i : t, N i := by
      apply Finset.sum_le_sum
      intro i _
      exact (Nat.card_congr (E i).schemeIsoToHomeo.toEquiv).trans_le (hchart i).2

end AlgebraicGeometry.Etale
