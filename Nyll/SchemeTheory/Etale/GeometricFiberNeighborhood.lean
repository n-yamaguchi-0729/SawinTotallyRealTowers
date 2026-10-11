/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Topology.Basic


/-!
# Finite sets of geometric points persist on an open neighborhood

For a separated étale morphism, a finite set of distinct points in one
geometric fiber gives equally many distinct points in every nearby
geometric fiber. The conclusion is an actual injection; no finiteness or
cardinality convention is needed for the surrounding fibers.

The construction uses the native finite product in the small étale category.
It removes the inverse images of the actual relative diagonals, not the
loci where projected underlying points coincide. Open-immersion lifting
retains the actual maps from the chosen field, including their residue
embeddings. This is the local geometric input for the degree-decrease step
in Stacks Project, Tag 09Z0.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

private theorem field_sections_eq_of_apply_eq
    {Ω : Type u} [Field Ω] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (CommRingCat.of Ω)) [Etale p]
    (a b : Spec (CommRingCat.of Ω) ⟶ Z)
    (ha : a ≫ p = 𝟙 _) (hb : b ≫ p = 𝟙 _)
    (hab : a default = b default) : a = b := by
  have : Etale (a ≫ p) := by
    rw [ha]
    infer_instance
  have : Etale a := Etale.of_comp a p
  have : IsSplitMono a := IsSplitMono.mk' ⟨p, ha⟩
  have : IsOpenImmersion a := IsOpenImmersion.of_flat_of_mono a
  have hba : Set.range b ⊆ Set.range a := by
    rintro _ ⟨x, rfl⟩
    refine ⟨default, ?_⟩
    rw [Subsingleton.elim x default]
    exact hab
  let l := IsOpenImmersion.lift a b hba
  have hl : l = 𝟙 (Spec (CommRingCat.of Ω)) := by
    calc
      l = l ≫ (a ≫ p) := by rw [ha, Category.comp_id]
      _ = (l ≫ a) ≫ p := (Category.assoc _ _ _).symm
      _ = b ≫ p := congrArg (fun k => k ≫ p) (IsOpenImmersion.lift_fac a b hba)
      _ = 𝟙 _ := hb
  calc
    a = (𝟙 _) ≫ a := (Category.id_comp a).symm
    _ = l ≫ a := congrArg (fun k => k ≫ a) hl.symm
    _ = b := IsOpenImmersion.lift_fac a b hba

private theorem exists_etale_factor_finite_family
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ X)
    {n : ℕ} (a : Fin n → (Spec (CommRingCat.of Ω) ⟶ U))
    (ha : ∀ i, a i ≫ f = s) :
    ∃ (T : Scheme.{u}) (g : T ⟶ X), Etale g ∧
      ∃ (r : Spec (CommRingCat.of Ω) ⟶ T) (p : Fin n → (T ⟶ U)),
        r ≫ g = s ∧ (∀ i, p i ≫ f = g) ∧ (∀ i, r ≫ p i = a i) := by
  let E : Fin n → X.Etale := fun _ => Scheme.Etale.mk f
  let T : X.Etale := ∏ᶜ E
  let F : X.Etale ⥤ Over X := Scheme.Etale.forget X
  let c : Over.mk s ⟶ ∏ᶜ (fun i => F.obj (E i)) :=
    Pi.lift (fun i => Over.homMk (a i) (ha i))
  let r : Over.mk s ⟶ F.obj T := c ≫ inv (piComparison F E)
  refine ⟨T.left, T.hom, inferInstance, r.left, fun i => (Pi.π E i).left,
    Over.w r, ?_, ?_⟩
  · intro i
    exact Over.w (Pi.π E i).hom
  · intro i
    have h : r ≫ F.map (Pi.π E i) = Over.homMk (a i) (ha i) := by
      dsimp only [r, c]
      rw [Category.assoc, inv_piComparison_comp_map_π, Pi.lift_comp_π]
    exact congrArg (fun k : Over.mk s ⟶ Over.mk f => k.left) h

/-- Finitely many distinct points in one geometric fiber of a separated
étale morphism persist as distinct points in every geometric fiber over an
open neighborhood of the given base point. The target fields and their
actual maps to the base remain arbitrary. -/
theorem exists_geometricFiber_injections_neighborhood
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X) {n : ℕ}
    (e : Fin n ↪ (pullback f s : Scheme.{u})) :
    ∃ V : X.Opens, s default ∈ V ∧
      ∀ (Ω' : Type u) [Field Ω'] [IsSepClosed Ω']
        (s' : Spec (CommRingCat.of Ω') ⟶ X), s' default ∈ V →
        Nonempty (Fin n ↪ (pullback f s' : Scheme.{u})) := by
  classical
  choose b hb hbe using fun i : Fin n =>
    Scheme.exists_fac_of_etale_of_isSepClosed (pullback.snd f s)
      (𝟙 (Spec (CommRingCat.of Ω))) (e i) (Subsingleton.elim _ _)
  let a (i : Fin n) : Spec (CommRingCat.of Ω) ⟶ U := b i ≫ pullback.fst f s
  have ha (i : Fin n) : a i ≫ f = s := by
    dsimp only [a]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hb i, Category.id_comp]
  obtain ⟨T, g, hg, r, p, hr, hp, hrp⟩ := exists_etale_factor_finite_family f s a ha
  have : Etale g := hg
  let q (i j : Fin n) : T ⟶ pullback f f :=
    pullback.lift (p i) (p j) ((hp i).trans (hp j).symm)
  let D : Set (pullback f f : Scheme.{u}) := Set.range (pullback.diagonal f)
  have hD : IsClosed D := (pullback.diagonal f).isClosedEmbedding.isClosed_range
  let J := {ij : Fin n × Fin n // ij.1 ≠ ij.2}
  let A : T.Opens :=
    ⟨⋂ ij : J, (q ij.val.1 ij.val.2) ⁻¹' Dᶜ,
      isOpen_iInter_of_finite (fun ij => hD.isOpen_compl.preimage
        (q ij.val.1 ij.val.2).continuous)⟩
  have hrA : r default ∈ A := by
    apply Set.mem_iInter.mpr
    intro ij
    change q ij.val.1 ij.val.2 (r default) ∉ D
    intro hdiag
    have hrange : Set.range (r ≫ q ij.val.1 ij.val.2) ⊆
        Set.range (pullback.diagonal f) := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Hom.comp_apply, Subsingleton.elim x default]
      exact hdiag
    let l := IsOpenImmersion.lift (pullback.diagonal f) (r ≫ q ij.val.1 ij.val.2) hrange
    have hl : l ≫ pullback.diagonal f = r ≫ q ij.val.1 ij.val.2 :=
      IsOpenImmersion.lift_fac _ _ hrange
    have hleft : r ≫ p ij.val.1 = l := by
      calc
        r ≫ p ij.val.1 = (r ≫ q ij.val.1 ij.val.2) ≫ pullback.fst f f := by
          simp only [q, Category.assoc, pullback.lift_fst]
        _ = (l ≫ pullback.diagonal f) ≫ pullback.fst f f :=
          congrArg (fun k => k ≫ pullback.fst f f) hl.symm
        _ = l := by rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    have hright : r ≫ p ij.val.2 = l := by
      calc
        r ≫ p ij.val.2 = (r ≫ q ij.val.1 ij.val.2) ≫ pullback.snd f f := by
          simp only [q, Category.assoc, pullback.lift_snd]
        _ = (l ≫ pullback.diagonal f) ≫ pullback.snd f f :=
          congrArg (fun k => k ≫ pullback.snd f f) hl.symm
        _ = l := by rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
    have hab : b ij.val.1 = b ij.val.2 := by
      apply pullback.hom_ext
      · exact (hrp ij.val.1).symm.trans ((hleft.trans hright.symm).trans (hrp ij.val.2))
      · exact (hb ij.val.1).trans (hb ij.val.2).symm
    apply ij.property
    apply e.injective
    exact (hbe ij.val.1).symm.trans
      ((congrArg (fun k : Spec (CommRingCat.of Ω) ⟶ pullback f s => k default) hab).trans
        (hbe ij.val.2))
  let k : A.toScheme ⟶ X := A.ι ≫ g
  refine ⟨⟨Set.range k, k.isOpenMap.isOpen_range⟩, ?_, ?_⟩
  · change s default ∈ Set.range k
    refine ⟨⟨r default, hrA⟩, ?_⟩
    change g (r default) = s default
    exact (Scheme.Hom.comp_apply r g default).symm.trans
      (congrArg (fun h : Spec (CommRingCat.of Ω) ⟶ X => h default) hr)
  · intro Ω' _ _ s' hs'
    change s' default ∈ Set.range k at hs'
    obtain ⟨t, ht⟩ := hs'
    obtain ⟨r', hr', _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed k s' t ht
    let r₀ : Spec (CommRingCat.of Ω') ⟶ T := r' ≫ A.ι
    have hr₀ : r₀ ≫ g = s' := (Category.assoc r' A.ι g).trans hr'
    let a' (i : Fin n) : Spec (CommRingCat.of Ω') ⟶ U := r₀ ≫ p i
    have ha' (i : Fin n) : a' i ≫ f = s' := by
      dsimp only [a']
      rw [Category.assoc, hp i, hr₀]
    let b' (i : Fin n) : Spec (CommRingCat.of Ω') ⟶ pullback f s' :=
      pullback.lift (a' i) (𝟙 _) ((ha' i).trans (Category.id_comp s').symm)
    have hb' (i : Fin n) : b' i ≫ pullback.snd f s' = 𝟙 _ :=
      pullback.lift_snd _ _ _
    refine ⟨⟨fun i => b' i default, ?_⟩⟩
    intro i j hij
    have hbij : b' i = b' j :=
      field_sections_eq_of_apply_eq (pullback.snd f s') (b' i) (b' j) (hb' i) (hb' j) hij
    have haij : a' i = a' j := by
      simpa only [b', pullback.lift_fst] using
        congrArg (fun h : Spec (CommRingCat.of Ω') ⟶ pullback f s' => h ≫ pullback.fst f s') hbij
    by_contra hne
    have hgood := Set.mem_iInter.mp (r' default).property (⟨(i, j), hne⟩ : J)
    change q i j (A.ι (r' default)) ∉ D at hgood
    apply hgood
    have hq : r₀ ≫ q i j = a' i ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp only [q, a', Category.assoc, pullback.lift_fst,
          pullback.diagonal_fst, Category.comp_id]
      · simp only [q, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
        exact haij.symm
    refine ⟨a' i default, ?_⟩
    have hpoint := congrArg
      (fun h : Spec (CommRingCat.of Ω') ⟶ pullback f f => h default) hq
    simpa only [r₀, Scheme.Hom.comp_apply] using hpoint.symm

end AlgebraicGeometry.Etale
