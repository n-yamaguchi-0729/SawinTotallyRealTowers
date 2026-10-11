/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Connected.Clopen

/-!
# Maps from a connected scheme to a coproduct

This file supplies the coproduct-fiber step used internally for Stacks Project,
Tag `03QR`.  A morphism from a connected scheme to a coproduct factors through
a unique summand, so its morphism set is the dependent sum of the morphism sets
to the individual summands.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Morphisms from a connected scheme to a coproduct are uniquely morphisms
to one of its summands. -/
noncomputable def homSigmaEquiv {ι : Type u} (Y : ι → Scheme.{u})
    (Z : Scheme.{u}) [ConnectedSpace Z] :
    (Z ⟶ ∐ Y) ≃ Σ i, (Z ⟶ Y i) :=
  (Equiv.ofBijective
    (fun f : Σ i, (Z ⟶ Y i) ↦ f.2 ≫ Sigma.ι Y f.1)
    (by
      constructor
      · rintro ⟨i, f⟩ ⟨j, g⟩ h
        let z : Z := Classical.arbitrary Z
        have hpoint :
            Sigma.ι Y i (f z) = Sigma.ι Y j (g z) := by
          change f ≫ Sigma.ι Y i = g ≫ Sigma.ι Y j at h
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]
        have hij : i = j :=
          congrArg Sigma.fst ((sigmaι_eq_iff Y i j (f z) (g z)).mp hpoint)
        subst j
        have hfg : f = g := (cancel_mono (Sigma.ι Y i)).mp h
        subst g
        rfl
      · intro f
        have hf :
            Continuous (fun z : Z ↦ (sigmaMk Y).symm (f z)) :=
          (sigmaMk Y).symm.continuous.comp f.continuous
        obtain ⟨i, g, _, hg⟩ := hf.exists_lift_sigma
        have hRange : Set.range f ⊆ Set.range (Sigma.ι Y i) := by
          rintro _ ⟨z, rfl⟩
          refine ⟨g z, ?_⟩
          have hz := congrArg (sigmaMk Y) (congrFun hg z)
          simpa only [Function.comp_apply, Homeomorph.apply_symm_apply,
            sigmaMk_mk] using hz.symm
        let : IsOpenImmersion (Sigma.ι Y i) :=
          (sigmaOpenCover Y).map_prop i
        refine ⟨⟨i, IsOpenImmersion.lift (Sigma.ι Y i) f hRange⟩, ?_⟩
        exact IsOpenImmersion.lift_fac (Sigma.ι Y i) f hRange)).symm

@[simp]
theorem homSigmaEquiv_symm_apply {ι : Type u} (Y : ι → Scheme.{u})
    (Z : Scheme.{u}) [ConnectedSpace Z] (f : Σ i, (Z ⟶ Y i)) :
    (homSigmaEquiv Y Z).symm f = f.2 ≫ Sigma.ι Y f.1 :=
  rfl

/-- The coproduct decomposition of morphisms is natural under precomposition.
In particular, precomposition cannot change the selected summand. -/
theorem homSigmaEquiv_comp {ι : Type u} (Y : ι → Scheme.{u})
    {Z Z' : Scheme.{u}} [ConnectedSpace Z] [ConnectedSpace Z']
    (f : Z' ⟶ Z) (g : Z ⟶ ∐ Y) :
    homSigmaEquiv Y Z' (f ≫ g) =
      ⟨(homSigmaEquiv Y Z g).1, f ≫ (homSigmaEquiv Y Z g).2⟩ := by
  apply (homSigmaEquiv Y Z').symm.injective
  rw [Equiv.symm_apply_apply, homSigmaEquiv_symm_apply, Category.assoc]
  have hg := (homSigmaEquiv Y Z).symm_apply_apply g
  rw [homSigmaEquiv_symm_apply] at hg
  exact congrArg (fun q ↦ f ≫ q) hg.symm

end AlgebraicGeometry.Scheme
