/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.FiniteAffineCover
import Nyll.SchemeTheory.Etale.GeometricFiberBound
import Nyll.SchemeTheory.Etale.NormalizationRemainderDegree
import Nyll.SchemeTheory.Morphisms.ClosedImmersion
import Nyll.SchemeTheory.Morphisms.QuasiFinite
import Nyll.SchemeTheory.Normalization.IntegralOpen
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Compactness.Compact


/-!
# Integral refinements of étale covers

This file proves the integral-refinement assertion of Stacks Project,
Tag 09Z0, by induction on the actual uniform geometric-fiber bound.
The recursive refinement is produced by the strict degree decrease of the
normalization remainder. Its integral normalization extension is joined
to the actual reduced closed complement, using native scheme coproducts.

The result is an integral surjective morphism which Zariski locally
factors through the original étale cover. The later strengthening to a
finite morphism of finite presentation is not asserted here.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A map to `X` factors through `f` on a Zariski neighborhood of each source point. -/
def Scheme.Hom.ZariskiLocallyFactorsThrough {T U X : Scheme.{u}}
    (g : T ⟶ X) (f : U ⟶ X) : Prop :=
  ∀ x : T, ∃ V : T.Opens, x ∈ V ∧
    ∃ a : V.toScheme ⟶ U, a ≫ f = V.ι ≫ g

private theorem local_factor_on_open_image
    {A T U X : Scheme.{u}} (g : T ⟶ X) (f : U ⟶ X)
    (i : A ⟶ T) [IsOpenImmersion i] (a : A ⟶ U)
    (ha : a ≫ f = i ≫ g) (x : A) :
    ∃ V : T.Opens, i x ∈ V ∧ ∃ b : V.toScheme ⟶ U, b ≫ f = V.ι ≫ g := by
  let V := i.opensRange
  have hV : Set.range V.ι ⊆ Set.range i := by
    rw [Scheme.Opens.range_ι]
    exact Set.Subset.rfl
  let l : V.toScheme ⟶ A := IsOpenImmersion.lift i V.ι hV
  refine ⟨V, ⟨x, rfl⟩, l ≫ a, ?_⟩
  calc
    (l ≫ a) ≫ f = l ≫ (a ≫ f) := Category.assoc _ _ _
    _ = l ≫ (i ≫ g) := congrArg (fun k => l ≫ k) ha
    _ = (l ≫ i) ≫ g := (Category.assoc _ _ _).symm
    _ = V.ι ≫ g := congrArg (fun k => k ≫ g) (IsOpenImmersion.lift_fac i V.ι hV)

private theorem integral_refinement_glue
    {U X Y Z : Scheme.{u}} (f : U ⟶ X) (π : Y ⟶ X)
    [IsIntegralHom π] [Surjective π] (j : U ⟶ Y) [IsOpenImmersion j]
    (hj : j ≫ π = f) (V : Y.Opens) [QuasiCompact V.ι]
    (hcover : (Set.range j)ᶜ ⊆ (V : Set Y))
    (p : Z ⟶ V.toScheme) [IsIntegralHom p] [Surjective p]
    (hlocal : (p ≫ V.ι ≫ π).ZariskiLocallyFactorsThrough f) :
    ∃ (T : Scheme.{u}) (g : T ⟶ X),
      IsIntegralHom g ∧ Surjective g ∧ g.ZariskiLocallyFactorsThrough f := by
  classical
  let F : Z ⟶ Y := p ≫ V.ι
  let A := F.normalization
  let b : A ⟶ Y := F.fromNormalization
  let e : Z ⟶ A := F.toNormalization
  have he : e ≫ b = p ≫ V.ι := F.toNormalization_fromNormalization
  have : IsOpenImmersion e := Scheme.Hom.isOpenImmersion_toNormalization_integral_open p V.ι
  have herange : Set.range e = b ⁻¹' (V : Set Y) := by
    simpa only [Scheme.Opens.range_ι] using
      Scheme.Hom.range_toNormalization_integral_open p V.ι
  let I : Y.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    ⟨(V : Set Y)ᶜ, V.isOpen.isClosed_compl⟩
  have hI : Set.range I.subschemeι = (V : Set Y)ᶜ := by
    rw [I.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  let H : A ⨿ I.subscheme ⟶ Y := coprod.desc b I.subschemeι
  have : IsIntegralHom H := by
    dsimp only [H]
    infer_instance
  have : Surjective H := by
    constructor
    intro y
    by_cases hy : y ∈ V
    · obtain ⟨z, hz⟩ := p.surjective ⟨y, hy⟩
      refine ⟨(coprod.inl : A ⟶ A ⨿ I.subscheme) (e z), ?_⟩
      calc
        H ((coprod.inl : A ⟶ A ⨿ I.subscheme) (e z)) = b (e z) :=
          (Scheme.Hom.comp_apply coprod.inl H (e z)).symm.trans
            (congrArg (fun k : A ⟶ Y => k (e z)) (coprod.inl_desc b I.subschemeι))
        _ = V.ι (p z) := (Scheme.Hom.comp_apply e b z).symm.trans
          ((congrArg (fun k : Z ⟶ Y => k z) he).trans (Scheme.Hom.comp_apply p V.ι z))
        _ = y := congrArg (fun v : V.toScheme => v.val) hz
    · have hyI : y ∈ Set.range I.subschemeι := by rw [hI]; exact hy
      obtain ⟨z, hz⟩ := hyI
      refine ⟨(coprod.inr : I.subscheme ⟶ A ⨿ I.subscheme) z, ?_⟩
      exact (Scheme.Hom.comp_apply coprod.inr H z).symm.trans
        ((congrArg (fun k : I.subscheme ⟶ Y => k z) (coprod.inr_desc b I.subschemeι)).trans hz)
  refine ⟨A ⨿ I.subscheme, H ≫ π, inferInstance, inferInstance, ?_⟩
  intro x
  obtain ⟨(x | x), rfl⟩ := (coprodMk A I.subscheme).surjective x
  · rw [coprodMk_inl]
    by_cases hx : x ∈ Set.range e
    · obtain ⟨z, rfl⟩ := hx
      obtain ⟨O, hz, a, ha⟩ := hlocal z
      let i : O.toScheme ⟶ A ⨿ I.subscheme := O.ι ≫ e ≫ coprod.inl
      have hi : a ≫ f = i ≫ (H ≫ π) := by
        have heπ : e ≫ b ≫ π = p ≫ V.ι ≫ π := by
          rw [← Category.assoc, he, Category.assoc]
        calc
          a ≫ f = O.ι ≫ p ≫ V.ι ≫ π := ha
          _ = O.ι ≫ e ≫ b ≫ π := congrArg (fun k => O.ι ≫ k) heπ.symm
          _ = i ≫ (H ≫ π) := by
            simp only [i, H, Category.assoc, coprod.inl_desc_assoc]
      have hpoint : i (⟨z, hz⟩ : O.toScheme) =
          (coprod.inl : A ⟶ A ⨿ I.subscheme) (e z) := by
        calc
          i (⟨z, hz⟩ : O.toScheme) = (e ≫ coprod.inl) z :=
            Scheme.Hom.comp_apply O.ι (e ≫ coprod.inl) ⟨z, hz⟩
          _ = (coprod.inl : A ⟶ A ⨿ I.subscheme) (e z) :=
            Scheme.Hom.comp_apply e coprod.inl z
      obtain ⟨N, hN, a', ha'⟩ :=
        local_factor_on_open_image (H ≫ π) f i a hi ⟨z, hz⟩
      rw [hpoint] at hN
      exact ⟨N, hN, a', ha'⟩
    · have hxV : b x ∉ V := by
        intro hb
        apply hx
        rw [herange]
        exact hb
      have hxj : b x ∈ Set.range j := by
        by_contra hj'
        exact hxV (hcover hj')
      let O : A.Opens := b ⁻¹ᵁ j.opensRange
      have hO : Set.range (O.ι ≫ b) ⊆ Set.range j := by
        rintro _ ⟨z, rfl⟩
        change b z.val ∈ Set.range j
        exact z.property
      let a : O.toScheme ⟶ U := IsOpenImmersion.lift j (O.ι ≫ b) hO
      let i : O.toScheme ⟶ A ⨿ I.subscheme := O.ι ≫ coprod.inl
      have hi : a ≫ f = i ≫ (H ≫ π) := by
        calc
          a ≫ f = a ≫ (j ≫ π) := congrArg (fun k => a ≫ k) hj.symm
          _ = (a ≫ j) ≫ π := (Category.assoc _ _ _).symm
          _ = (O.ι ≫ b) ≫ π :=
            congrArg (fun k => k ≫ π) (IsOpenImmersion.lift_fac j (O.ι ≫ b) hO)
          _ = i ≫ (H ≫ π) := by
            simp only [i, H, Category.assoc, coprod.inl_desc_assoc]
      have hpoint : i (⟨x, hxj⟩ : O.toScheme) =
          (coprod.inl : A ⟶ A ⨿ I.subscheme) x :=
        Scheme.Hom.comp_apply O.ι coprod.inl ⟨x, hxj⟩
      obtain ⟨N, hN, a', ha'⟩ :=
        local_factor_on_open_image (H ≫ π) f i a hi ⟨x, hxj⟩
      rw [hpoint] at hN
      exact ⟨N, hN, a', ha'⟩
  · rw [coprodMk_inr]
    have hIj : Set.range I.subschemeι ⊆ Set.range j := by
      intro y hy
      have hyV : y ∉ V := by
        change y ∈ (V : Set Y)ᶜ
        rw [← hI]
        exact hy
      by_contra hj'
      exact hyV (hcover hj')
    let a : I.subscheme ⟶ U := IsOpenImmersion.lift j I.subschemeι hIj
    have ha : a ≫ f = (coprod.inr : I.subscheme ⟶ A ⨿ I.subscheme) ≫ (H ≫ π) := by
      calc
        a ≫ f = a ≫ (j ≫ π) := congrArg (fun k => a ≫ k) hj.symm
        _ = (a ≫ j) ≫ π := (Category.assoc _ _ _).symm
        _ = I.subschemeι ≫ π :=
          congrArg (fun k => k ≫ π) (IsOpenImmersion.lift_fac j I.subschemeι hIj)
        _ = coprod.inr ≫ (H ≫ π) := by
          simp only [H, coprod.inr_desc_assoc]
    exact local_factor_on_open_image (H ≫ π) f coprod.inr a ha x

private theorem integral_refinement_of_bound (n : ℕ) :
    ∀ {U X : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace X]
      (f : U ⟶ X) [Etale f] [IsSeparated f] [Surjective f],
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (s : Spec (CommRingCat.of Ω) ⟶ X),
        Finite (pullback f s : Scheme.{u}) ∧ Nat.card (pullback f s : Scheme.{u}) ≤ n) →
      ∃ (T : Scheme.{u}) (g : T ⟶ X),
        IsIntegralHom g ∧ Surjective g ∧ g.ZariskiLocallyFactorsThrough f := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro U X _ _ f _ _ _ hbound
    cases n with
    | zero =>
      have : IsEmpty U := by
        constructor
        intro x
        let Ω := SeparableClosure (U.residueField x)
        let t : Spec (CommRingCat.of Ω) ⟶ U :=
          Spec.map (CommRingCat.ofHom (algebraMap (U.residueField x) Ω)) ≫
            U.fromSpecResidueField x
        let s : Spec (CommRingCat.of Ω) ⟶ X := t ≫ f
        let a : Spec (CommRingCat.of Ω) ⟶ pullback f s :=
          pullback.lift t (𝟙 _) (Category.id_comp s).symm
        have : Nonempty (pullback f s : Scheme.{u}) := ⟨a default⟩
        have : Finite (pullback f s : Scheme.{u}) := (hbound Ω s).1
        have hpos : 0 < Nat.card (pullback f s : Scheme.{u}) := Nat.card_pos
        exact (Nat.lt_irrefl 0) (hpos.trans_le (hbound Ω s).2)
      have : IsEmpty X := by
        constructor
        intro x
        obtain ⟨y, _⟩ := f.surjective x
        exact isEmptyElim y
      refine ⟨X, 𝟙 X, inferInstance, inferInstance, ?_⟩
      intro x
      exact isEmptyElim x
    | succ m =>
      have : QuasiCompact f := inferInstance
      have : LocallyQuasiFinite f :=
        LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType f
      let Y := f.normalization
      let π : Y ⟶ X := f.fromNormalization
      let j : U ⟶ Y := f.toNormalization
      have : IsOpenImmersion j := inferInstance
      have : IsIntegralHom π := inferInstance
      have : Surjective π := by
        have : Surjective (j ≫ π) := by
          change Surjective (f.toNormalization ≫ f.fromNormalization)
          rw [f.toNormalization_fromNormalization]
          infer_instance
        exact Surjective.of_comp j π
      have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated π
      let W := f.etaleNormalizationRemainder
      have hWclosed : IsClosed (Set.range W.ι) := by
        rw [Scheme.Opens.range_ι]
        exact f.etaleNormalizationRemainder_isClosed
      have : IsClosedImmersion W.ι :=
        isClosedImmersion_of_isPreimmersion_of_isClosed W.ι hWclosed
      have : CompactSpace (pullback f π : Scheme.{u}) := inferInstance
      have : CompactSpace W.toScheme := QuasiCompact.compactSpace_of_compactSpace W.ι
      let q : W.toScheme ⟶ Y := W.ι ≫ pullback.snd f π
      have : Etale q := inferInstance
      have : IsSeparated q := inferInstance
      let V : Y.Opens := ⟨Set.range q, q.isOpenMap.isOpen_range⟩
      have : CompactSpace V.toScheme := by
        change CompactSpace (Set.range q)
        exact isCompact_iff_compactSpace.mp (isCompact_range q.continuous)
      have : QuasiSeparatedSpace V.toScheme := quasiSeparatedSpace_of_quasiSeparated V.ι
      have : QuasiCompact V.ι := inferInstance
      have hqV : Set.range q ⊆ Set.range V.ι := by
        rw [Scheme.Opens.range_ι]
        exact Set.Subset.rfl
      let w : W.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι q hqV
      have hw : w ≫ V.ι = q := IsOpenImmersion.lift_fac V.ι q hqV
      have : Etale w := by
        have : Etale (w ≫ V.ι) := by rw [hw]; infer_instance
        exact Etale.of_comp w V.ι
      have : IsSeparated w := by
        have : IsSeparated (w ≫ V.ι) := by rw [hw]; infer_instance
        exact IsSeparated.of_comp w V.ι
      have : Surjective w := by
        constructor
        intro v
        obtain ⟨x, hx⟩ := v.property
        refine ⟨x, ?_⟩
        apply V.ι.injective
        exact (Scheme.Hom.comp_apply w V.ι x).symm.trans
          ((congrArg (fun k : W.toScheme ⟶ Y => k x) hw).trans hx)
      have hsmall : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
          (s : Spec (CommRingCat.of Ω) ⟶ V.toScheme),
          Finite (pullback w s : Scheme.{u}) ∧ Nat.card (pullback w s : Scheme.{u}) ≤ m := by
        intro Ω _ _ s
        obtain ⟨hfinite, hlt⟩ :=
          f.normalizationRemainder_degree_lt_of_bound (Nat.succ m) hbound Ω (s ≫ V.ι)
        have : Finite (pullback q (s ≫ V.ι) : Scheme.{u}) := hfinite
        let E₀ : pullback w s ≅ pullback (w ≫ V.ι) (s ≫ V.ι) :=
          (pullbackIsPullbackOfCompMono w s V.ι).conePointUniqueUpToIso
            (pullback.isLimit (w ≫ V.ι) (s ≫ V.ι))
        let E : pullback w s ≅ pullback q (s ≫ V.ι) :=
          E₀ ≪≫ pullback.congrHom hw rfl
        exact ⟨Finite.of_injective E.hom E.hom.injective,
          (Nat.card_congr E.schemeIsoToHomeo.toEquiv).trans_le (Nat.le_of_lt_succ hlt)⟩
      obtain ⟨Z, p, hpI, hpS, hpLocal⟩ := ih m (Nat.lt_succ_self m) w hsmall
      have : IsIntegralHom p := hpI
      have : Surjective p := hpS
      let r : W.toScheme ⟶ U := W.ι ≫ pullback.fst f π
      have hr : r ≫ f = q ≫ π :=
        (Category.assoc W.ι (pullback.fst f π) f).trans
          ((congrArg (fun k => W.ι ≫ k) (pullback.condition (f := f) (g := π))).trans
            (Category.assoc W.ι (pullback.snd f π) π).symm)
      have hlocal : (p ≫ V.ι ≫ π).ZariskiLocallyFactorsThrough f := by
        intro z
        obtain ⟨O, hz, a, ha⟩ := hpLocal z
        have haV : a ≫ q = O.ι ≫ p ≫ V.ι := by
          calc
            a ≫ q = a ≫ (w ≫ V.ι) := congrArg (fun k => a ≫ k) hw.symm
            _ = (a ≫ w) ≫ V.ι := (Category.assoc _ _ _).symm
            _ = (O.ι ≫ p) ≫ V.ι := congrArg (fun k => k ≫ V.ι) ha
            _ = O.ι ≫ p ≫ V.ι := Category.assoc _ _ _
        refine ⟨O, hz, a ≫ r, ?_⟩
        calc
          (a ≫ r) ≫ f = a ≫ (r ≫ f) := Category.assoc _ _ _
          _ = a ≫ (q ≫ π) := congrArg (fun k => a ≫ k) hr
          _ = (a ≫ q) ≫ π := (Category.assoc _ _ _).symm
          _ = (O.ι ≫ p ≫ V.ι) ≫ π := congrArg (fun k => k ≫ π) haV
          _ = O.ι ≫ (p ≫ V.ι ≫ π) := Category.assoc _ _ _
      have hcover : (Set.range j)ᶜ ⊆ (V : Set Y) :=
        f.normalization_boundary_subset_remainder_image
      exact integral_refinement_glue f π j f.toNormalization_fromNormalization V hcover p hlocal

/-- A compact separated étale cover has an integral surjective refinement
which locally factors through the original cover. The recursive local
factorizations are constructed by induction on the actual fiber bound. -/
theorem Etale.exists_integral_refinement_of_compactSource
    {U X : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace X]
    (f : U ⟶ X) [Etale f] [IsSeparated f] [Surjective f] :
    ∃ (T : Scheme.{u}) (g : T ⟶ X),
      IsIntegralHom g ∧ Surjective g ∧ g.ZariskiLocallyFactorsThrough f := by
  obtain ⟨n, hn⟩ := Etale.exists_uniform_geometricFiber_bound f
  exact integral_refinement_of_bound n f hn

/-- The integral-refinement assertion of Stacks, Tag 09Z0. A surjective
étale cover of a quasi-compact quasi-separated scheme is Zariski locally
dominated by an actual integral surjective morphism. Finite presentation
of the refinement is a separate, later assertion. -/
theorem Etale.exists_integral_refinement
    {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : U ⟶ X) [Etale f] [Surjective f] :
    ∃ (T : Scheme.{u}) (g : T ⟶ X),
      IsIntegralHom g ∧ Surjective g ∧ g.ZariskiLocallyFactorsThrough f := by
  let C : X.Cover.{u} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)) :=
    Scheme.Cover.mkOfCovers PUnit.{u + 1} (fun _ => U) (fun _ => f)
      (fun x => by obtain ⟨y, hy⟩ := f.surjective x; exact ⟨PUnit.unit, y, hy⟩)
      (fun _ => inferInstance)
  obtain ⟨A, e, hfinite, _, hAffine, hEtale, hSurj⟩ :=
    Scheme.Cover.exists_finite_affine_etale_refinement C
  have : Finite A.I₀ := hfinite
  let S : Scheme.{u} := ∐ fun i : A.I₀ => Spec (A.X i)
  have : IsAffine S := hAffine
  have : CompactSpace S := inferInstance
  let F : S ⟶ X := Sigma.desc A.f
  have : Etale F := hEtale
  have : Surjective F := hSurj
  have : IsSeparated F := inferInstance
  let a (i : A.I₀) : Spec (A.X i) ⟶ U := e.h₀ i
  have ha (i : A.I₀) : a i ≫ f = A.f i := e.w₀ i
  let l : S ⟶ U := Sigma.desc a
  have hl : l ≫ f = F := by
    apply Sigma.hom_ext
    intro i
    calc
      Sigma.ι (fun i : A.I₀ => Spec (A.X i)) i ≫ (l ≫ f) = a i ≫ f := by
        rw [← Category.assoc, Sigma.ι_comp_desc]
      _ = A.f i := ha i
      _ = Sigma.ι (fun i : A.I₀ => Spec (A.X i)) i ≫ F := (Sigma.ι_comp_desc A.f i).symm
  obtain ⟨T, g, hgI, hgS, hgLocal⟩ := Etale.exists_integral_refinement_of_compactSource F
  refine ⟨T, g, hgI, hgS, ?_⟩
  intro x
  obtain ⟨V, hx, b, hb⟩ := hgLocal x
  refine ⟨V, hx, b ≫ l, ?_⟩
  calc
    (b ≫ l) ≫ f = b ≫ (l ≫ f) := Category.assoc _ _ _
    _ = b ≫ F := congrArg (fun k => b ≫ k) hl
    _ = V.ι ≫ g := hb

end AlgebraicGeometry
