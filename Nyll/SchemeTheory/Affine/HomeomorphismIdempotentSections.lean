/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Topology.Homeomorph.Defs

/-!
# Lifting idempotent sections through a scheme homeomorphism

An idempotent section is locally zero or one. Its two open pieces transport
through a homeomorphism and the constant sections glue there. In particular,
an idempotent on a closed fibre lifts to every infinitesimal thickening.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- A morphism inducing a homeomorphism lifts every idempotent global
section. The lift is constructed by gluing its zero and one pieces. -/
theorem exists_appTop_eq_of_isHomeomorph_of_isIdempotentElem
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsHomeomorph f)
    (e : Γ(X, ⊤)) (he : IsIdempotentElem e) :
    ∃ a : Γ(Y, ⊤), f.appTop a = e := by
  let U : Y.Opens := ⟨f '' (X.basicOpen e : Set X),
    hf.isOpenMap _ (X.basicOpen e).isOpen⟩
  let V : Y.Opens := ⟨f '' (X.basicOpen (1 - e) : Set X),
    hf.isOpenMap _ (X.basicOpen (1 - e)).isOpen⟩
  have hcov : U ⊔ V = ⊤ := by
    apply top_le_iff.mp
    intro y _
    obtain ⟨x, rfl⟩ := hf.surjective y
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
        (X.presheaf.germ ⊤ x trivial e) with hx | hx
    · exact Or.inl ⟨x, (Scheme.mem_basicOpen_top X e x).mpr hx, rfl⟩
    · have hx' : IsUnit (X.presheaf.germ ⊤ x trivial (1 - e)) := by
        simpa only [map_sub, map_one] using hx
      exact Or.inr ⟨x, (Scheme.mem_basicOpen_top X (1 - e) x).mpr hx', rfl⟩
  have hdisj : U ⊓ V = ⊥ := by
    apply le_bot_iff.mp
    rintro y ⟨⟨x, hx, hxy⟩, ⟨z, hz, hzy⟩⟩
    have hxz : x = z := hf.injective (hxy.trans hzy.symm)
    have hx0 : x ∈ X.basicOpen e ⊓ X.basicOpen (1 - e) := ⟨hx, hxz.symm ▸ hz⟩
    rw [← Scheme.basicOpen_mul, he.mul_one_sub_self, Scheme.basicOpen_zero] at hx0
    exact hx0
  let W : Bool → Y.Opens := fun b => cond b U V
  let s : ∀ b : Bool, Γ(Y, W b) :=
    fun b => Bool.rec (motive := fun b => Γ(Y, W b)) 0 1 b
  have hW : (⊤ : Y.Opens) ≤ ⨆ b, W b := by
    rw [← hcov]
    exact sup_le (le_iSup W true) (le_iSup W false)
  have hEmpty (b c : Bool) (hbc : b ≠ c) : W b ⊓ W c = ⊥ := by
    cases b with
    | false =>
      cases c with
      | false => exact (hbc rfl).elim
      | true => exact (inf_comm V U).trans hdisj
    | true =>
      cases c with
      | false => exact hdisj
      | true => exact (hbc rfl).elim
  have hCompatible : TopCat.Presheaf.IsCompatible Y.presheaf W s := by
    intro b c
    by_cases hbc : b = c
    · subst c
      rfl
    · have : Subsingleton Γ(Y, W b ⊓ W c) :=
        CommRingCat.subsingleton_of_isTerminal
          (Y.sheaf.isTerminalOfEqEmpty (hEmpty b c hbc))
      exact Subsingleton.elim _ _
  obtain ⟨a, ha, _⟩ := Y.sheaf.existsUnique_gluing' W ⊤
    (fun b => homOfLE le_top) hW s hCompatible
  have haU : Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a = 1 := ha true
  have haV : Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op a = 0 := ha false
  refine ⟨a, TopCat.Presheaf.section_ext X.sheaf ⊤ _ _ (fun x hxTop => ?_)⟩
  have hxImage : f x ∈ (⊤ : Y.Opens) := Set.mem_univ (f x)
  have hMap : X.presheaf.germ ⊤ x hxTop (f.appTop a) =
      f.stalkMap x (Y.presheaf.germ ⊤ (f x) hxImage a) :=
    (f.germ_stalkMap_apply ⊤ x hxImage a).symm
  refine hMap.trans ?_
  have hIdem : IsIdempotentElem (X.presheaf.germ ⊤ x hxTop e) :=
    he.map (X.presheaf.germ ⊤ x hxTop).hom
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
      (X.presheaf.germ ⊤ x hxTop e) with hx | hx
  · have hxU : f x ∈ U :=
      ⟨x, (Scheme.mem_basicOpen_top X e x).mpr hx, rfl⟩
    have hga : Y.presheaf.germ ⊤ (f x) hxImage a = 1 :=
      (Y.presheaf.germ_res_apply
        (homOfLE (show U ≤ ⊤ from le_top)) (f x) hxU a).symm.trans
          ((congrArg (Y.presheaf.germ U (f x) hxU) haU).trans (map_one _))
    have hge : X.presheaf.germ ⊤ x hxTop e = 1 :=
      (IsIdempotentElem.iff_eq_one_of_isUnit hx).mp hIdem
    exact (congrArg (f.stalkMap x) hga).trans ((map_one _).trans hge.symm)
  · have hx' : IsUnit (X.presheaf.germ ⊤ x hxTop (1 - e)) := by
      simpa only [map_sub, map_one] using hx
    have hxV : f x ∈ V :=
      ⟨x, (Scheme.mem_basicOpen_top X (1 - e) x).mpr hx', rfl⟩
    have hga : Y.presheaf.germ ⊤ (f x) hxImage a = 0 :=
      (Y.presheaf.germ_res_apply
        (homOfLE (show V ≤ ⊤ from le_top)) (f x) hxV a).symm.trans
          ((congrArg (Y.presheaf.germ V (f x) hxV) haV).trans (map_zero _))
    have hge : X.presheaf.germ ⊤ x hxTop e = 0 :=
      sub_eq_self.mp ((IsIdempotentElem.iff_eq_one_of_isUnit hx).mp hIdem.one_sub)
    exact (congrArg (f.stalkMap x) hga).trans ((map_zero _).trans hge.symm)

end AlgebraicGeometry.Scheme.Hom
