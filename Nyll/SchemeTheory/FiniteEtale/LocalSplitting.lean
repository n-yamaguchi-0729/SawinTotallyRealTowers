/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.Basic
import Nyll.SchemeTheory.FiniteEtale.Algebra.Splitting
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.TotallySplit

/-!
# Étale local splitting of finite étale morphisms

Every finite étale morphism becomes a finite disjoint union of copies of the
base on an étale cover. The cover is constructed from the local algebraic
splitting theorem, first on affine schemes and then on an affine open cover.
The trivializing isomorphisms commute with the projections to the cover.

The rank may vary between members of the cover. No connectedness or
noetherian hypothesis, and no choice of a ground field, is imposed.
-/

noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

private lemma sigmaSpec_comp_algebraMap (S : Type u) [CommRing S]
    (ι : Type u) [Finite ι] :
    sigmaSpec (fun _ : ι => CommRingCat.of S) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (ι → S))) =
      Sigma.desc (fun _ : ι => 𝟙 (Spec (.of S))) := by
  apply Sigma.hom_ext
  intro i
  rw [ι_sigmaSpec_assoc, Sigma.ι_comp_desc, ← Spec.map_comp]
  exact Spec.map_id _

private lemma exists_coprod_pullback_iso_of_split
    (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] (ι : Type u) [Finite ι]
    (e : (S ⊗[R] A) ≃ₐ[S] (ι → S)) :
    ∃ E : (∐ fun _ : ι => Spec (.of S)) ≅
        pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S))),
      E.hom ≫ pullback.snd _ _ = Sigma.desc (fun _ : ι => 𝟙 (Spec (.of S))) := by
  let eSpec : Spec (.of (ι → S)) ≅ Spec (.of (S ⊗[R] A)) :=
    Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  have he : eSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) =
      Spec.map (CommRingCat.ofHom (algebraMap S (ι → S))) := by
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext e.commutes)
  refine ⟨asIso (sigmaSpec (fun _ : ι => CommRingCat.of S)) ≪≫ eSpec ≪≫
    (pullbackSpecIso R S A).symm ≪≫ pullbackSymmetry _ _, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst']
  rw [he]
  exact sigmaSpec_comp_algebraMap S ι

private lemma exists_etale_splitting_spec
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A] (p : PrimeSpectrum R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Etale (Spec.map (CommRingCat.ofHom (algebraMap R S))) ∧
      p ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R S))) ∧
      ∃ (n : ℕ) (E : (∐ fun _ : ULift.{u} (Fin n) => Spec (.of S)) ≅
          pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
            (Spec.map (CommRingCat.ofHom (algebraMap R S)))),
        E.hom ≫ pullback.snd _ _ =
          Sigma.desc (fun _ : ULift.{u} (Fin n) => 𝟙 (Spec (.of S))) := by
  obtain ⟨S, _, _, _, hp, hS⟩ := Algebra.exists_etale_isFiniteSplit (A := A) p
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun S (S ⊗[R] A)
  let e' : (S ⊗[R] A) ≃ₐ[S] (ULift.{u} (Fin n) → S) :=
    e.trans (AlgEquiv.piCongrLeft' S (fun _ : Fin n => S) Equiv.ulift.symm)
  obtain ⟨E, hE⟩ := exists_coprod_pullback_iso_of_split R S A (ULift.{u} (Fin n)) e'
  exact ⟨S, inferInstance, inferInstance,
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance), hp, n, E, hE⟩

private lemma exists_etale_splitting_of_isAffine {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsFiniteEtale f] [IsAffine X] (x : X) :
    ∃ (U : Scheme.{u}) (g : U ⟶ X), IsAffine U ∧ Etale g ∧ x ∈ Set.range g ∧
      ∃ (n : ℕ) (E : (∐ fun _ : ULift.{u} (Fin n) => U) ≅ pullback f g),
        E.hom ≫ pullback.snd f g = Sigma.desc (fun _ : ULift.{u} (Fin n) => 𝟙 U) := by
  have : IsAffine Y := isAffine_of_isAffineHom f
  let R := Γ(X, ⊤)
  let A := Γ(Y, ⊤)
  let : Algebra R A := f.appTop.hom.toAlgebra
  have : Module.Finite R A := f.finite_appTop
  have : Algebra.Etale R A :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := f)).mp inferInstance
  obtain ⟨S, _, _, hg, hp, n, E, hE⟩ :=
    exists_etale_splitting_spec R A (X.isoSpec.hom x)
  let g' : Spec (.of S) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let g : Spec (.of S) ⟶ X := g' ≫ X.isoSpec.inv
  let φ : Spec A ⟶ Spec R := Spec.map f.appTop
  let E' : (∐ fun _ : ULift.{u} (Fin n) => Spec (.of S)) ≅ pullback φ g' := E
  have hE' : E'.hom ≫ pullback.snd φ g' =
      Sigma.desc (fun _ : ULift.{u} (Fin n) => 𝟙 (Spec (.of S))) := hE
  let b : pullback φ g' ≅ pullback f g := asIso
    (pullback.map φ g' f g Y.isoSpec.inv (𝟙 _) X.isoSpec.inv
      (Scheme.isoSpec_inv_naturality f)
      (Category.id_comp g).symm)
  refine ⟨Spec (.of S), g, inferInstance, inferInstance, ?_, n, E' ≪≫ b, ?_⟩
  · obtain ⟨q, hq⟩ := hp
    refine ⟨q, ?_⟩
    change X.isoSpec.inv (g' q) = x
    rw [hq, ← Scheme.Hom.comp_apply, X.isoSpec.hom_inv_id]
    rfl
  · change (E'.hom ≫ pullback.map φ g' f g Y.isoSpec.inv (𝟙 _) X.isoSpec.inv
        (Scheme.isoSpec_inv_naturality f) (Category.id_comp g).symm) ≫
      pullback.snd f g = _
    rw [Category.assoc, pullback.lift_snd, Category.comp_id]
    exact hE'

/-- At every point of the base, a finite étale morphism splits on an affine
étale neighbourhood as a finite disjoint union of copies of that neighbourhood. -/
theorem IsFiniteEtale.exists_etale_splitting {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsFiniteEtale f] (x : X) :
    ∃ (U : Scheme.{u}) (g : U ⟶ X), IsAffine U ∧ Etale g ∧ x ∈ Set.range g ∧
      ∃ (n : ℕ) (E : (∐ fun _ : ULift.{u} (Fin n) => U) ≅ pullback f g),
        E.hom ≫ pullback.snd f g = Sigma.desc (fun _ : ULift.{u} (Fin n) => 𝟙 U) := by
  let i := X.affineCover.idx x
  let a := X.affineCover.f i
  obtain ⟨x', hx'⟩ := X.affineCover.covers x
  have : IsFiniteEtale (pullback.snd f a) := ⟨⟩
  obtain ⟨U, g, hU, hg, ⟨u, hu⟩, n, E, hE⟩ :=
    exists_etale_splitting_of_isAffine (pullback.snd f a) x'
  refine ⟨U, g ≫ a, hU, inferInstance, ?_, n,
    E ≪≫ pullbackLeftPullbackSndIso f a g, ?_⟩
  · refine ⟨u, ?_⟩
    change a (g u) = x
    rw [hu]
    exact hx'
  · rw [Iso.trans_hom, Category.assoc, pullbackLeftPullbackSndIso_hom_snd]
    exact hE

/-- A finite étale morphism has an étale cover by affine schemes on which it
is a finite disjoint union of copies of the base. The finite rank can depend
on the member of the cover. -/
theorem IsFiniteEtale.exists_etale_splitting_cover {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsFiniteEtale f] :
    ∃ 𝒰 : X.Cover.{u} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)),
      (∀ i : 𝒰.I₀, IsAffine (𝒰.X i)) ∧
      ∀ i : 𝒰.I₀, ∃ (n : ℕ)
        (E : (∐ fun _ : ULift.{u} (Fin n) => 𝒰.X i) ≅ pullback f (𝒰.f i)),
        E.hom ≫ pullback.snd f (𝒰.f i) =
          Sigma.desc (fun _ : ULift.{u} (Fin n) => 𝟙 (𝒰.X i)) := by
  classical
  choose U g hU hg hp n E hE using fun x : X => IsFiniteEtale.exists_etale_splitting f x
  let 𝒰 : X.Cover.{u} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)) :=
    Scheme.Cover.mkOfCovers X U g (fun x => ⟨x, hp x⟩) hg
  exact ⟨𝒰, hU, fun i => ⟨n i, E i, hE i⟩⟩

end AlgebraicGeometry
