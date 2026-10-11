/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.CompatibleStalkSpreading
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Stalk

/-!+# Compatible stalk spreading through an affine chart

We base-change the actual target to a finite-component affine neighborhood,
transport the given section through the chart's actual stalk map, and apply
affine compatible spreading. The resulting section and its overlap equation
are transported back through the canonical open-image isomorphisms.
Strict henselizations are not reconstructed or changed in this step.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- An affine chart with finitely many irreducible components suffices for
compatible extension from the original scheme stalk. -/
theorem exists_compatible_open_extension_fromSpecStalk_of_affineNeighborhood
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [IsSeparated f]
    (U : X.Opens) (s : U.toScheme ⟶ Y) (hs : s ≫ f = U.ι)
    (x : X) (A : X.Opens) (hA : IsAffineOpen A) (hxA : x ∈ A)
    (hfin : (irreducibleComponents A.toScheme).Finite)
    (a : Spec (X.presheaf.stalk x) ⟶ Y) (ha : a ≫ f = X.fromSpecStalk x)
    (hcompat : pullback.snd (X.fromSpecStalk x) U.ι ≫ s =
      pullback.fst (X.fromSpecStalk x) U.ι ≫ a) :
    ∃ (W : X.Opens), x ∈ W ∧ ∃ b : W.toScheme ⟶ Y,
      b ≫ f = W.ι ∧
      X.homOfLE (show U ⊓ W ≤ U from inf_le_left) ≫ s =
        X.homOfLE (show U ⊓ W ≤ W from inf_le_right) ≫ b := by
  have : IsAffine A.toScheme := hA
  let xA : A.toScheme := ⟨x, hxA⟩
  let q : Spec (X.presheaf.stalk x) ⟶ X := X.fromSpecStalk x
  let qA : Spec (A.toScheme.presheaf.stalk xA) ⟶ A.toScheme :=
    A.toScheme.fromSpecStalk xA
  let r : Spec (A.toScheme.presheaf.stalk xA) ⟶ Spec (X.presheaf.stalk x) :=
    Spec.map (A.ι.stalkMap xA)
  have hr : r ≫ q = qA ≫ A.ι := Scheme.SpecMap_stalkMap_fromSpecStalk A.ι
  let fA : pullback f A.ι ⟶ A.toScheme := pullback.snd f A.ι
  let aA : Spec (A.toScheme.presheaf.stalk xA) ⟶ pullback f A.ι :=
    pullback.lift (r ≫ a) qA (by rw [Category.assoc, ha]; exact hr)
  have haA : aA ≫ fA = qA := pullback.lift_snd _ _ _
  let UA : A.toScheme.Opens := A.ι ⁻¹ᵁ U
  let uU : UA.toScheme ⟶ U.toScheme := A.ι ∣_ U
  have huU : uU ≫ U.ι = UA.ι ≫ A.ι := morphismRestrict_ι A.ι U
  let sA : UA.toScheme ⟶ pullback f A.ι :=
    pullback.lift (uU ≫ s) UA.ι (by rw [Category.assoc, hs]; exact huU)
  have hsA : sA ≫ fA = UA.ι := pullback.lift_snd _ _ _
  have hkcond : (pullback.fst qA UA.ι ≫ r) ≫ q =
      (pullback.snd qA UA.ι ≫ uU) ≫ U.ι := by
    rw [Category.assoc, hr, ← Category.assoc, pullback.condition,
      Category.assoc, ← huU, ← Category.assoc]
  let k : pullback qA UA.ι ⟶ pullback q U.ι := pullback.lift
    (pullback.fst qA UA.ι ≫ r) (pullback.snd qA UA.ι ≫ uU) hkcond
  have hAcompat : pullback.snd qA UA.ι ≫ sA = pullback.fst qA UA.ι ≫ aA := by
    apply pullback.hom_ext
    · have hkfst : k ≫ pullback.fst q U.ι = pullback.fst qA UA.ι ≫ r :=
        pullback.lift_fst _ _ _
      have hksnd : k ≫ pullback.snd q U.ι = pullback.snd qA UA.ι ≫ uU :=
        pullback.lift_snd _ _ _
      have h : k ≫ (pullback.snd q U.ι ≫ s) =
          k ≫ (pullback.fst q U.ι ≫ a) :=
        congrArg (fun z : pullback q U.ι ⟶ Y => k ≫ z) hcompat
      have h' : (pullback.snd qA UA.ι ≫ uU) ≫ s =
          (pullback.fst qA UA.ι ≫ r) ≫ a := by
        rw [← Category.assoc, hksnd, ← Category.assoc, hkfst] at h
        exact h
      rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst]
      simpa only [Category.assoc] using h'
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd]
      exact pullback.condition.symm
  obtain ⟨B, hxB, bB, _, hbBf, hbBU⟩ :=
    Scheme.exists_compatible_open_extension_fromSpecStalk hfin fA UA sA hsA
      xA aA haA hAcompat
  let W : X.Opens := A.ι ''ᵁ B
  have hxW : x ∈ W := ⟨xA, hxB, rfl⟩
  let e : B.toScheme ≅ W.toScheme := A.ι.isoImage B
  let bW : W.toScheme ⟶ Y := e.inv ≫ bB ≫ pullback.fst f A.ι
  have hbWf : bW ≫ f = W.ι := by
    change (e.inv ≫ bB ≫ pullback.fst f A.ι) ≫ f = W.ι
    rw [Category.assoc, Category.assoc, pullback.condition,
      ← Category.assoc bB, hbBf]
    exact A.ι.isoImage_inv_ι B
  let OA : A.toScheme.Opens := UA ⊓ B
  let O : X.Opens := U ⊓ W
  have hrange : Set.range (OA.ι ≫ A.ι) = Set.range O.ι := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    change A.ι '' (A.ι ⁻¹' (U : Set X) ∩ (B : Set A.toScheme)) =
      (U : Set X) ∩ A.ι '' (B : Set A.toScheme)
    exact Set.image_preimage_inter A.ι B U
  let eO : OA.toScheme ≅ O.toScheme :=
    IsOpenImmersion.isoOfRangeEq (OA.ι ≫ A.ι) O.ι hrange
  have heO : eO.hom ≫ O.ι = OA.ι ≫ A.ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac (OA.ι ≫ A.ι) O.ι hrange
  let dUA : OA.toScheme ⟶ UA.toScheme := A.toScheme.homOfLE inf_le_left
  let dB : OA.toScheme ⟶ B.toScheme := A.toScheme.homOfLE inf_le_right
  let dU : O.toScheme ⟶ U.toScheme := X.homOfLE inf_le_left
  let dW : O.toScheme ⟶ W.toScheme := X.homOfLE inf_le_right
  have heOU : eO.hom ≫ dU = dUA ≫ uU := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι, heO, Category.assoc, huU,
      ← Category.assoc, Scheme.homOfLE_ι]
  have heOW : eO.hom ≫ dW = dB ≫ e.hom := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι, heO, Category.assoc,
      Scheme.Hom.isoImage_hom_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have heb : e.hom ≫ bW = bB ≫ pullback.fst f A.ι := by
    change e.hom ≫ (e.inv ≫ bB ≫ pullback.fst f A.ι) = _
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
  have hoverlap : dUA ≫ (uU ≫ s) = dB ≫ (bB ≫ pullback.fst f A.ι) := by
    have h := congrArg (fun z : OA.toScheme ⟶ pullback f A.ι =>
      z ≫ pullback.fst f A.ι) hbBU
    simpa only [sA, Category.assoc, pullback.lift_fst] using h
  refine ⟨W, hxW, bW, hbWf, ?_⟩
  apply (cancel_epi eO.hom).mp
  change eO.hom ≫ (dU ≫ s) = eO.hom ≫ (dW ≫ bW)
  rw [← Category.assoc, heOU, Category.assoc,
    ← Category.assoc eO.hom, heOW, Category.assoc, heb]
  exact hoverlap

end AlgebraicGeometry.Scheme
