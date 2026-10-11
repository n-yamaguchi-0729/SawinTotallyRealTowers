/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.StalkSpreading
import Nyll.SchemeTheory.LocalGeometry.StalkDominantNeighborhood
import Nyll.SchemeTheory.Morphisms.DominantBaseChange
import Nyll.SchemeTheory.Morphisms.UnramifiedHomExt
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!+# Spreading a stalk section compatibly with an existing open section

For a separated etale target over an affine scheme with finitely many
irreducible components, a stalk section which agrees with an existing open
section extends to a neighborhood with the same agreement on the overlap.
The open need not be quasi-compact. Compatibility is obtained from actual
dominance after deleting the components which miss the chosen point.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A compatible section on the actual stalk spreads compatibly to an open
neighborhood, without a quasi-compactness assumption on the original open. -/
theorem exists_compatible_open_extension_fromSpecStalk
    {X Y : Scheme.{u}} [IsAffine X]
    (hfin : (irreducibleComponents X).Finite)
    (f : Y ⟶ X) [Etale f] [IsSeparated f]
    (U : X.Opens) (s : U.toScheme ⟶ Y) (hs : s ≫ f = U.ι)
    (x : X) (a : Spec (X.presheaf.stalk x) ⟶ Y)
    (ha : a ≫ f = X.fromSpecStalk x)
    (hcompat : pullback.snd (X.fromSpecStalk x) U.ι ≫ s =
      pullback.fst (X.fromSpecStalk x) U.ι ≫ a) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (b : V.toScheme ⟶ Y),
      V.fromSpecStalkOfMem x hxV ≫ b = a ∧ b ≫ f = V.ι ∧
      X.homOfLE (show U ⊓ V ≤ U from inf_le_left) ≫ s =
        X.homOfLE (show U ⊓ V ≤ V from inf_le_right) ≫ b := by
  obtain ⟨W, hxW, b, hba, hbf⟩ :=
    Scheme.exists_open_extension_fromSpecStalk_of_isAffine (X := X) f x a ha
  obtain ⟨V₀, hxV₀, hdom⟩ := X.exists_open_fromSpecStalkOfMem_isDominant hfin x
  let V : X.Opens := W ⊓ V₀
  have hxV : x ∈ V := ⟨hxW, hxV₀⟩
  let l : Spec (X.presheaf.stalk x) ⟶ V.toScheme := V.fromSpecStalkOfMem x hxV
  let iW : V.toScheme ⟶ W.toScheme := X.homOfLE inf_le_left
  let i₀ : V.toScheme ⟶ V₀.toScheme := X.homOfLE inf_le_right
  have hlW : l ≫ iW = W.fromSpecStalkOfMem x hxW := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  have hl₀ : l ≫ i₀ = V₀.fromSpecStalkOfMem x hxV₀ := by
    apply (cancel_mono V₀.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  have : IsDominant (l ≫ i₀) := hl₀.symm ▸ hdom
  have : IsDominant l := IsDominant.of_comp_of_isOpenImmersion l i₀
  let bV : V.toScheme ⟶ Y := iW ≫ b
  have hbVa : l ≫ bV = a := by
    rw [← Category.assoc, hlW, hba]
  have hbVf : bV ≫ f = V.ι := by
    rw [Category.assoc, hbf, Scheme.homOfLE_ι]
  let O : X.Opens := U ⊓ V
  let dU : O.toScheme ⟶ U.toScheme := X.homOfLE inf_le_left
  let dV : O.toScheme ⟶ V.toScheme := X.homOfLE inf_le_right
  let qO : pullback dV l ⟶ O.toScheme := pullback.fst dV l
  let qS : pullback dV l ⟶ Spec (X.presheaf.stalk x) := pullback.snd dV l
  have hq : qO ≫ O.ι = qS ≫ X.fromSpecStalk x := by
    rw [← X.homOfLE_ι (show O ≤ V from inf_le_right), ← Category.assoc,
      pullback.condition, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  have hkcond : qS ≫ X.fromSpecStalk x = (qO ≫ dU) ≫ U.ι := by
    rw [Category.assoc, Scheme.homOfLE_ι]
    exact hq.symm
  let k : pullback dV l ⟶ pullback (X.fromSpecStalk x) U.ι :=
    pullback.lift qS (qO ≫ dU) hkcond
  have hk : (qO ≫ dU) ≫ s = qS ≫ a := by
    have ht := congrArg
      (fun z : pullback (X.fromSpecStalk x) U.ι ⟶ Y => k ≫ z) hcompat
    simpa only [k, ← Category.assoc, pullback.lift_snd, pullback.lift_fst] using ht
  have heq : qO ≫ (dU ≫ s) = qO ≫ (dV ≫ bV) := by
    calc
      qO ≫ (dU ≫ s) = qS ≫ a := by rw [← Category.assoc, hk]
      _ = qO ≫ (dV ≫ bV) := by
        rw [← Category.assoc, pullback.condition, Category.assoc, hbVa]
  let s₁ : Over.mk O.ι ⟶ Over.mk f := Over.homMk (dU ≫ s) (by
    change (dU ≫ s) ≫ f = O.ι
    rw [Category.assoc, hs, Scheme.homOfLE_ι])
  let s₂ : Over.mk O.ι ⟶ Over.mk f := Over.homMk (dV ≫ bV) (by
    change (dV ≫ bV) ≫ f = O.ι
    rw [Category.assoc, hbVf, Scheme.homOfLE_ι])
  let q : Over.mk (qO ≫ O.ι) ⟶ Over.mk O.ι := Over.homMk qO rfl
  have : IsDominant q.left := isDominant_pullback_fst_of_isOpenMap dV l dV.isOpenEmbedding.isOpenMap
  have : FormallyUnramified (Over.mk f).hom := inferInstanceAs (FormallyUnramified f)
  have : LocallyOfFiniteType (Over.mk f).hom := inferInstanceAs (LocallyOfFiniteType f)
  have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  have hs₁₂ : s₁ = s₂ := Over.hom_ext_of_isDominant_of_unramified s₁ s₂ q
    (Over.OverMorphism.ext heq)
  refine ⟨V, hxV, bV, hbVa, hbVf, ?_⟩
  exact congrArg (fun z : Over.mk O.ι ⟶ Over.mk f => z.left) hs₁₂

end AlgebraicGeometry.Scheme
