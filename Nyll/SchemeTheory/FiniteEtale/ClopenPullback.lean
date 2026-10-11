/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.Topology.Sets.Closeds

/-!
# Descending clopen subsets through finite étale equivalences

A clopen subscheme is a subterminal finite étale scheme. An equivalence on
finite étale schemes lifts this object and detects its subterminality, so
its lift is again a clopen subscheme. Fullness also detects containment of
clopen subsets. Consequently every clopen subset descends uniquely.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteEtale

private def clopenFiniteEtale {X : Scheme.{u}} (U : Clopens X) : FiniteEtale X where
  toComma := Over.mk (Scheme.Opens.ι U.toOpens)
  prop := by
    let : IsClosedImmersion (Scheme.Opens.ι U.toOpens) :=
      IsClosedImmersion.of_isPreimmersion (Scheme.Opens.ι U.toOpens) (by
        rw [Scheme.Opens.range_ι]
        exact U.isClosed)
    change IsFiniteEtale (Scheme.Opens.ι U.toOpens)
    exact @IsFiniteEtale.mk _ _ _ inferInstance inferInstance

private lemma range_clopenFiniteEtale {X : Scheme.{u}} (U : Clopens X) :
    Set.range (clopenFiniteEtale U).hom = (U : Set X) :=
  Scheme.Opens.range_ι U.toOpens

private lemma clopen_subset_of_preimage_subset {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(FiniteEtale.pullback f).Full] (U V : Clopens Y)
    (h : f ⁻¹' (U : Set Y) ⊆ f ⁻¹' (V : Set Y)) :
    (U : Set Y) ⊆ (V : Set Y) := by
  let F := FiniteEtale.pullback f
  let : IsOpenImmersion (clopenFiniteEtale V).hom :=
    inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι V.toOpens))
  have hrange : Set.range (F.obj (clopenFiniteEtale U)).hom ⊆
      Set.range (F.obj (clopenFiniteEtale V)).hom := by
    change Set.range (Limits.pullback.snd (clopenFiniteEtale U).hom f) ⊆
      Set.range (Limits.pullback.snd (clopenFiniteEtale V).hom f)
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd,
      range_clopenFiniteEtale, range_clopenFiniteEtale]
    exact h
  let : IsOpenImmersion (F.obj (clopenFiniteEtale V)).hom :=
    inferInstanceAs (IsOpenImmersion
      (Limits.pullback.snd (clopenFiniteEtale V).hom f))
  let k : F.obj (clopenFiniteEtale U) ⟶ F.obj (clopenFiniteEtale V) :=
    MorphismProperty.Over.homMk
      (IsOpenImmersion.lift (F.obj (clopenFiniteEtale V)).hom
        (F.obj (clopenFiniteEtale U)).hom hrange)
      (IsOpenImmersion.lift_fac _ _ hrange)
  let a : clopenFiniteEtale U ⟶ clopenFiniteEtale V := F.preimage k
  intro y hy
  have hy' : y ∈ Set.range (clopenFiniteEtale U).hom := by
    rw [range_clopenFiniteEtale]
    exact hy
  obtain ⟨x, hx⟩ := hy'
  have hyV : y ∈ Set.range (clopenFiniteEtale V).hom := by
    refine ⟨a.left x, ?_⟩
    rw [← Scheme.Hom.comp_apply, MorphismProperty.Over.w a]
    exact hx
  rw [range_clopenFiniteEtale] at hyV
  exact hyV

/-- If pullback is an equivalence on finite étale schemes, every clopen subset
of the source is the inverse image of a unique clopen subset of the target. -/
theorem existsUnique_clopen_preimage_of_pullback_isEquivalence
    {X Y : Scheme.{u}} (f : X ⟶ Y) [(FiniteEtale.pullback f).IsEquivalence]
    (U : Clopens X) :
    ∃! V : Clopens Y, f ⁻¹' (V : Set Y) = (U : Set X) := by
  let F := FiniteEtale.pullback f
  let V : FiniteEtale Y := F.objPreimage (clopenFiniteEtale U)
  let e : F.obj V ≅ clopenFiniteEtale U := F.objObjPreimageIso (clopenFiniteEtale U)
  have hsub {T : FiniteEtale Y} (a b : T ⟶ V) : a = b := by
    let : Category (MorphismProperty.Over
        (@IsFiniteEtale : MorphismProperty Scheme.{u})
        (⊤ : MorphismProperty Scheme.{u}) X) := FiniteEtale.instCategory X
    apply F.map_injective
    apply (cancel_mono e.hom).mp
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono (Scheme.Opens.ι U.toOpens)).mp
    exact (MorphismProperty.Over.w (F.map a ≫ e.hom)).trans
      (MorphismProperty.Over.w (F.map b ≫ e.hom)).symm
  let : IsFiniteEtale (𝟙 Y) := @IsFiniteEtale.mk _ _ _ inferInstance inferInstance
  let m : V ⟶ FiniteEtale.mk (𝟙 Y) :=
    MorphismProperty.Over.homMk V.hom (Category.comp_id V.hom)
  let : Mono m :=
    { right_cancellation := fun a b _ ↦ hsub a b }
  have hV : IsOpenImmersion V.hom ∧ IsClosedImmersion V.hom :=
    (FiniteEtale.mono_iff Y V (FiniteEtale.mk (𝟙 Y)) m).mp inferInstance
  let : IsOpenImmersion V.hom := hV.1
  let : IsClosedImmersion V.hom := hV.2
  let C : Clopens Y :=
    ⟨Set.range V.hom,
      ⟨V.hom.isClosedEmbedding.isClosed_range, IsOpenImmersion.isOpen_range V.hom⟩⟩
  let es : (F.obj V).left ≅ (clopenFiniteEtale U).left :=
    ((FiniteEtale.forget X) ⋙ Over.forget X).mapIso e
  have he : es.hom ≫ (Scheme.Opens.ι U.toOpens) = Limits.pullback.snd V.hom f :=
    MorphismProperty.Over.w e.hom
  have hC : f ⁻¹' (C : Set Y) = (U : Set X) := by
    calc
      f ⁻¹' (C : Set Y) = Set.range (Limits.pullback.snd V.hom f) :=
        (Scheme.Pullback.range_snd V.hom f).symm
      _ = Set.range (es.hom ≫ (Scheme.Opens.ι U.toOpens)) :=
        congrArg (fun p : (F.obj V).left ⟶ X ↦ Set.range p) he.symm
      _ = Set.range (Scheme.Opens.ι U.toOpens) := by
        change Set.range ((Scheme.Opens.ι U.toOpens) ∘ es.hom) =
          Set.range (Scheme.Opens.ι U.toOpens)
        exact es.hom.surjective.range_comp (Scheme.Opens.ι U.toOpens)
      _ = (U : Set X) := Scheme.Opens.range_ι U.toOpens
  refine ⟨C, hC, ?_⟩
  intro D hD
  apply Clopens.ext
  apply Set.Subset.antisymm
  · apply clopen_subset_of_preimage_subset f D C
    exact (hD.trans hC.symm).subset
  · apply clopen_subset_of_preimage_subset f C D
    exact (hC.trans hD.symm).subset

end AlgebraicGeometry.FiniteEtale
