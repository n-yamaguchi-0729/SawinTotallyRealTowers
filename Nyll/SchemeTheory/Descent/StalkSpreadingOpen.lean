/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.StalkSpreading
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Spreading a stalk morphism on an arbitrary scheme

The actual affine-neighborhood stalk is identified by its canonical stalk
isomorphism. Finite-presentation spreading on that affine neighborhood then
produces a morphism on an actual open of the original scheme, with the
original stalk factorization retained. No finiteness assumption on the
ambient scheme is needed.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A relative morphism from an actual stalk into a locally finitely
presented scheme extends over an open neighborhood of that point. -/
theorem exists_open_extension_fromSpecStalk
    {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFinitePresentation f]
    (x : X) (a : Spec (X.presheaf.stalk x) ⟶ Y)
    (ha : a ≫ f = X.fromSpecStalk x) :
    ∃ (W : X.Opens) (hxW : x ∈ W) (b : W.toScheme ⟶ Y),
      W.fromSpecStalkOfMem x hxW ≫ b = a ∧ b ≫ f = W.ι := by
  obtain ⟨A₀, hA₀, hxA₀, _⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ (⊤ : X.Opens) from trivial)
  let A : X.Opens := A₀
  have hA : IsAffineOpen A := hA₀
  have hxA : x ∈ A := hxA₀
  have : IsAffine A.toScheme := hA
  let xA : A.toScheme := ⟨x, hxA⟩
  let qA : Spec (A.toScheme.presheaf.stalk xA) ⟶ A.toScheme :=
    A.toScheme.fromSpecStalk xA
  let r : Spec (A.toScheme.presheaf.stalk xA) ⟶ Spec (X.presheaf.stalk x) :=
    Spec.map (A.ι.stalkMap xA)
  have hr : r ≫ X.fromSpecStalk x = qA ≫ A.ι :=
    Scheme.SpecMap_stalkMap_fromSpecStalk A.ι
  let fA : pullback f A.ι ⟶ A.toScheme := pullback.snd f A.ι
  let aA : Spec (A.toScheme.presheaf.stalk xA) ⟶ pullback f A.ι :=
    pullback.lift (r ≫ a) qA (by rw [Category.assoc, ha]; exact hr)
  have haA : aA ≫ fA = qA := pullback.lift_snd _ _ _
  obtain ⟨B, hxB, bB, hbBa, hbBf⟩ :=
    exists_open_extension_fromSpecStalk_of_isAffine fA xA aA haA
  let W : X.Opens := A.ι ''ᵁ B
  have hxW : x ∈ W := ⟨xA, hxB, rfl⟩
  let e : B.toScheme ≅ W.toScheme := A.ι.isoImage B
  let bW : W.toScheme ⟶ Y := e.inv ≫ bB ≫ pullback.fst f A.ι
  have hbWf : bW ≫ f = W.ι := by
    change (e.inv ≫ bB ≫ pullback.fst f A.ι) ≫ f = W.ι
    rw [Category.assoc, Category.assoc, pullback.condition,
      ← Category.assoc bB, hbBf]
    exact A.ι.isoImage_inv_ι B
  have hrW : r ≫ W.fromSpecStalkOfMem x hxW =
      B.fromSpecStalkOfMem xA hxB ≫ e.hom := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hr,
      Category.assoc, Scheme.Hom.isoImage_hom_ι,
      ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  have : IsIso r := inferInstanceAs (IsIso (Spec.map (A.ι.stalkMap xA)))
  refine ⟨W, hxW, bW, ?_, hbWf⟩
  apply (cancel_epi r).mp
  change r ≫ (W.fromSpecStalkOfMem x hxW ≫
    (e.inv ≫ bB ≫ pullback.fst f A.ι)) = r ≫ a
  rw [← Category.assoc r, hrW]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hbBa]
  exact pullback.lift_fst _ _ _

end AlgebraicGeometry.Scheme
