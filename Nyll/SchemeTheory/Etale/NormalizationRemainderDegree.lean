/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.AffineGeometricFiberBound
import Nyll.SchemeTheory.Etale.GeometricFiberNeighborhood
import Nyll.SchemeTheory.Etale.NormalizationRemainder
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Topology.Closure


/-!
# Strict degree decrease for the normalization remainder

A supplied uniform finite bound on the geometric fibers of a separated
quasi-compact étale morphism strictly decreases on its actual normalization
remainder. Over the dense normalization image the residual fiber omits the
normalization-graph point. The neighborhood theorem for finite sets of
geometric points extends this strict bound to the entire normalization.

The final theorem supplies the original bound from the existing affine
geometric-fiber theorem for maps between spectra. The very same bound is
used in the strict inequality; it is not increased. This proves the
degree-decrease step in the affine case of Stacks Project, Tag 09Z0.
The uniform bound for a general qcqs target, the integral refinement and
finite-presentation descent remain separate tasks.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {U X : Scheme.{u}} (f : U ⟶ X) [QuasiCompact f] [IsSeparated f] [Etale f]

/-- The actual residual-fiber inclusion, followed by the standard pasting
isomorphism to the original geometric fiber. -/
private def remainderFiberMap {Ω : Type u} [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ f.normalization) :
    pullback ((f.etaleNormalizationRemainder).ι ≫ pullback.snd f f.fromNormalization) s ⟶
      pullback f (s ≫ f.fromNormalization) :=
  pullback.map _ _ _ _ (f.etaleNormalizationRemainder).ι (𝟙 _) (𝟙 _)
      (Category.comp_id _)
      ((Category.comp_id s).trans (Category.id_comp s).symm) ≫
    (pullbackLeftPullbackSndIso f f.fromNormalization s).hom

private instance remainderFiberMap_isOpenImmersion {Ω : Type u} [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ f.normalization) :
    IsOpenImmersion (remainderFiberMap f s) := by
  dsimp only [remainderFiberMap]
  infer_instance

private theorem remainder_degree_lt_over_source
    (d : ℕ)
    (hbound : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (CommRingCat.of Ω) ⟶ X),
      Finite (pullback f s : Scheme.{u}) ∧ Nat.card (pullback f s : Scheme.{u}) ≤ d)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (CommRingCat.of Ω) ⟶ U) :
    Finite (pullback ((f.etaleNormalizationRemainder).ι ≫
        pullback.snd f f.fromNormalization) (t ≫ f.toNormalization) : Scheme.{u}) ∧
      Nat.card (pullback ((f.etaleNormalizationRemainder).ι ≫
        pullback.snd f f.fromNormalization) (t ≫ f.toNormalization) : Scheme.{u}) < d := by
  let W := f.etaleNormalizationRemainder
  let p : pullback f f.fromNormalization ⟶ f.normalization :=
    pullback.snd f f.fromNormalization
  let q : W.toScheme ⟶ f.normalization := W.ι ≫ p
  let s : Spec (CommRingCat.of Ω) ⟶ f.normalization := t ≫ f.toNormalization
  have : Finite (pullback f (s ≫ f.fromNormalization) : Scheme.{u}) :=
    (hbound Ω (s ≫ f.fromNormalization)).1
  have hfinite : Finite (pullback q s : Scheme.{u}) :=
    Finite.of_injective (remainderFiberMap f s) (remainderFiberMap f s).injective
  have hns : ¬ Function.Surjective (remainderFiberMap f s) := by
    let m : pullback q s ⟶ pullback p s :=
      pullback.map q s p s W.ι (𝟙 _) (𝟙 _) (Category.comp_id q)
        ((Category.comp_id s).trans (Category.id_comp s).symm)
    let E : pullback p s ≅ pullback f (s ≫ f.fromNormalization) :=
      pullbackLeftPullbackSndIso f f.fromNormalization s
    have hzfac : (t ≫ f.normalizationEtaleGraph) ≫ p = (𝟙 _) ≫ s := by
      rw [Category.assoc, normalizationEtaleGraph_snd, Category.id_comp]
    let zmap : Spec (CommRingCat.of Ω) ⟶ pullback p s :=
      pullback.lift (t ≫ f.normalizationEtaleGraph) (𝟙 _) hzfac
    let z : (pullback p s : Scheme.{u}) := zmap default
    intro hsurj
    change Function.Surjective (m ≫ E.hom) at hsurj
    obtain ⟨w, hw⟩ := hsurj (E.hom z)
    have hw' : m w = z := E.hom.injective
      ((Scheme.Hom.comp_apply m E.hom w).symm.trans hw)
    have hm : m ≫ pullback.fst p s = pullback.fst q s ≫ W.ι :=
      pullback.lift_fst _ _ _
    have hz : zmap ≫ pullback.fst p s = t ≫ f.normalizationEtaleGraph :=
      pullback.lift_fst _ _ _
    have hmpt : pullback.fst p s (m w) = W.ι (pullback.fst q s w) :=
      (Scheme.Hom.comp_apply m (pullback.fst p s) w).symm.trans
        ((congrArg (fun k : pullback q s ⟶ pullback f f.fromNormalization => k w) hm).trans
          (Scheme.Hom.comp_apply (pullback.fst q s) W.ι w))
    have hzpt : pullback.fst p s z = f.normalizationEtaleGraph (t default) :=
      (Scheme.Hom.comp_apply zmap (pullback.fst p s) default).symm.trans
        ((congrArg (fun k : Spec (CommRingCat.of Ω) ⟶ pullback f f.fromNormalization =>
          k default) hz).trans
          (Scheme.Hom.comp_apply t f.normalizationEtaleGraph default))
    have houtside : W.ι (pullback.fst q s w) ∉ Set.range f.normalizationEtaleGraph :=
      (pullback.fst q s w).property
    apply houtside
    exact ⟨t default,
      (hmpt.symm.trans ((congrArg (pullback.fst p s) hw').trans hzpt)).symm⟩
  have hlt : Nat.card (pullback q s : Scheme.{u}) <
      Nat.card (pullback f (s ≫ f.fromNormalization) : Scheme.{u}) := by
    apply lt_of_not_ge
    intro hge
    exact hns ((remainderFiberMap f s).injective.bijective_of_nat_card_le hge).surjective
  exact ⟨hfinite, hlt.trans_le (hbound Ω (s ≫ f.fromNormalization)).2⟩

/-- The normalization remainder has geometric fibers strictly smaller than
any actual uniform finite bound for the original étale morphism. The bound
premise is the induction parameter; the affine theorem below supplies it
without an additional hypothesis. -/
theorem normalizationRemainder_degree_lt_of_bound
    (d : ℕ)
    (hbound : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (CommRingCat.of Ω) ⟶ X),
      Finite (pullback f s : Scheme.{u}) ∧ Nat.card (pullback f s : Scheme.{u}) ≤ d) :
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (CommRingCat.of Ω) ⟶ f.normalization),
      Finite (pullback ((f.etaleNormalizationRemainder).ι ≫
          pullback.snd f f.fromNormalization) s : Scheme.{u}) ∧
        Nat.card (pullback ((f.etaleNormalizationRemainder).ι ≫
          pullback.snd f f.fromNormalization) s : Scheme.{u}) < d := by
  intro Ω _ _ s
  let q : (f.etaleNormalizationRemainder).toScheme ⟶ f.normalization :=
    (f.etaleNormalizationRemainder).ι ≫ pullback.snd f f.fromNormalization
  have : Finite (pullback f (s ≫ f.fromNormalization) : Scheme.{u}) :=
    (hbound Ω (s ≫ f.fromNormalization)).1
  have : Finite (pullback q s : Scheme.{u}) :=
    Finite.of_injective (remainderFiberMap f s) (remainderFiberMap f s).injective
  let e : Fin (Nat.card (pullback q s : Scheme.{u})) ↪ (pullback q s : Scheme.{u}) :=
    (Finite.equivFin (pullback q s : Scheme.{u})).symm.toEmbedding
  obtain ⟨V, hsV, hV⟩ := Etale.exists_geometricFiber_injections_neighborhood q s e
  obtain ⟨x, hyV⟩ := f.toNormalization.denseRange.exists_mem_open V.isOpen ⟨s default, hsV⟩
  let Ω' := SeparableClosure (U.residueField x)
  let t : Spec (CommRingCat.of Ω') ⟶ U :=
    Spec.map (CommRingCat.ofHom (algebraMap (U.residueField x) Ω')) ≫
      U.fromSpecResidueField x
  have ht : t default = x := by
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have htV : (t ≫ f.toNormalization) default ∈ V := by
    rw [Scheme.Hom.comp_apply, ht]
    exact hyV
  obtain ⟨i⟩ := hV Ω' (t ≫ f.toNormalization) htV
  obtain ⟨hfinite, hlt⟩ := remainder_degree_lt_over_source f d hbound t
  have : Finite (pullback q (t ≫ f.toNormalization) : Scheme.{u}) := hfinite
  have hle : Nat.card (pullback q s : Scheme.{u}) ≤
      Nat.card (pullback q (t ≫ f.toNormalization) : Scheme.{u}) := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective i i.injective
  exact ⟨inferInstance, hle.trans_lt hlt⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Etale

/-- For an actual étale map between spectra, the existing affine bound
supplies both a uniform bound for the original fibers and a strictly smaller
bound for its normalization remainder. No global-bound premise is added. -/
theorem exists_normalizationRemainder_degree_bound_spec
    {R S : CommRingCat.{u}} (f : Spec S ⟶ Spec R) [Etale f] :
    ∃ d : ℕ,
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (s : Spec (CommRingCat.of Ω) ⟶ Spec R),
        Finite (pullback f s : Scheme.{u}) ∧ Nat.card (pullback f s : Scheme.{u}) ≤ d) ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (s : Spec (CommRingCat.of Ω) ⟶ f.normalization),
        Finite (pullback ((f.etaleNormalizationRemainder).ι ≫
            pullback.snd f f.fromNormalization) s : Scheme.{u}) ∧
          Nat.card (pullback ((f.etaleNormalizationRemainder).ι ≫
            pullback.snd f f.fromNormalization) s : Scheme.{u}) < d) := by
  obtain ⟨d, hd⟩ := exists_uniform_geometricFiber_bound_spec f
  exact ⟨d, hd, f.normalizationRemainder_degree_lt_of_bound d hd⟩

end AlgebraicGeometry.Etale
