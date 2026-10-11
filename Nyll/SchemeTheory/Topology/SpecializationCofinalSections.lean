/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Topology.Sheaves.Stalks

/-!
# Global sections detected on a specialization-cofinal subset

Suppose every point specializes to a point of a subset `Z`. Equality of
global sections is detected by their germs on `Z`. A global section of a
sheaf lies in a subsheaf if its germs on `Z` lie in the subsheaf stalks.
The latter assertion constructs local lifts near points of `Z`, uses
specialization to cover the whole space, and glues by the monomorphism.

These are the stalk and local-lifting steps in the subsheaf reduction
for Stacks Project, tag 09ZG. No identification of restriction stalks is
assumed or asserted in this file.

Reference: https://stacks.math.columbia.edu/tag/09ZG.
The Lean proofs are original.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite

namespace SchemeTheory

variable {X : TopCat.{u}} {Z : Set X}

/-- Global sections are determined by their germs on a subset to which
every point has a specialization. -/
theorem globalSection_eq_of_germs_on_specialization_cofinal
    (hZ : ∀ x : X, ∃ z ∈ Z, x ⤳ z)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
    (s t : F.obj.obj (op (⊤ : Opens X)))
    (hst : ∀ z ∈ Z,
      TopCat.Presheaf.germ F.obj ⊤ z trivial s =
        TopCat.Presheaf.germ F.obj ⊤ z trivial t) : s = t := by
  let FP : X.Presheaf (Type u) := F.obj
  apply TopCat.Presheaf.section_ext F ⊤ s t
  intro x _
  obtain ⟨z, hz, hxz⟩ := hZ x
  have heq : FP.stalkSpecializes hxz (FP.germ ⊤ z trivial s) =
      FP.stalkSpecializes hxz (FP.germ ⊤ z trivial t) :=
    congrArg (FP.stalkSpecializes hxz) (hst z hz)
  change FP.germ ⊤ x trivial s = FP.germ ⊤ x trivial t
  have hg : FP.germ ⊤ z trivial ≫ FP.stalkSpecializes hxz =
      FP.germ ⊤ x trivial :=
    TopCat.Presheaf.germ_stalkSpecializes FP (U := ⊤) trivial hxz
  have hs := congrArg (fun k : FP.obj (op (⊤ : Opens X)) ⟶ FP.stalk x => k s) hg
  have ht := congrArg (fun k : FP.obj (op (⊤ : Opens X)) ⟶ FP.stalk x => k t) hg
  exact hs.symm.trans (heq.trans ht)

/-- A global section has a preimage under a sheaf monomorphism whenever
its germs have preimages on a specialization-cofinal subset. -/
theorem exists_globalSection_lift_of_germs_on_specialization_cofinal
    (hZ : ∀ x : X, ∃ z ∈ Z, x ⤳ z)
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)}
    (m : F ⟶ G) [Mono m]
    (s : G.obj.obj (op (⊤ : Opens X)))
    (hs : ∀ z ∈ Z, ∃ a : TopCat.Presheaf.stalk F.obj z,
      (TopCat.Presheaf.stalkFunctor (Type u) z).map m.hom a =
        TopCat.Presheaf.germ G.obj ⊤ z trivial s) :
    ∃ t : F.obj.obj (op (⊤ : Opens X)), m.hom.app (op ⊤) t = s := by
  classical
  let FP : X.Presheaf (Type u) := F.obj
  let GP : X.Presheaf (Type u) := G.obj
  have hlocal (z : X) (hz : z ∈ Z) :
      ∃ (V : Opens X) (_ : z ∈ V) (t : FP.obj (op V)),
        m.hom.app (op V) t = GP.map (homOfLE (show V ≤ ⊤ from le_top)).op s := by
    obtain ⟨a, ha⟩ := hs z hz
    obtain ⟨V, hzV, t, hat⟩ := FP.exists_germ_eq a
    have heq : GP.germ V z hzV (m.hom.app (op V) t) =
        GP.germ ⊤ z trivial s := by
      rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply, hat]
      exact ha
    obtain ⟨W, hzW, iWV, iWtop, hW⟩ := GP.germ_eq (U := V) (V := ⊤)
      z hzV trivial (m.hom.app (op V) t) s heq
    refine ⟨W, hzW, FP.map iWV.op t, ?_⟩
    exact (m.hom.naturality_apply iWV.op t).trans hW
  have hlocal_all (x : X) :
      ∃ (V : Opens X) (_ : x ∈ V) (t : FP.obj (op V)),
        m.hom.app (op V) t = GP.map (homOfLE (show V ≤ ⊤ from le_top)).op s := by
    obtain ⟨z, hz, hxz⟩ := hZ x
    obtain ⟨V, hzV, t, ht⟩ := hlocal z hz
    exact ⟨V, hxz.mem_open V.isOpen hzV, t, ht⟩
  choose V hxV t ht using hlocal_all
  have hcover : (⊤ : Opens X) ≤ iSup V := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hxV x⟩
  have hinj (W : Opens X) : Function.Injective (m.hom.app (op W)) := by
    have hm : Mono m.hom :=
      (sheafToPresheaf (Opens.grothendieckTopology X) (Type u)).map_mono m
    have hmW : Mono (m.hom.app (op W)) := (NatTrans.mono_iff_mono_app m.hom).mp hm _
    exact (CategoryTheory.mono_iff_injective (m.hom.app (op W))).mp hmW
  have hcompatible : TopCat.Presheaf.IsCompatible FP V t := by
    intro x y
    apply hinj (V x ⊓ V y)
    rw [m.hom.naturality_apply, m.hom.naturality_apply, ht x, ht y,
      ← types_comp_apply, ← types_comp_apply, ← GP.map_comp, ← GP.map_comp]
    exact congrArg (fun i : op (⊤ : Opens X) ⟶ op (V x ⊓ V y) => GP.map i s)
      (Subsingleton.elim _ _)
  obtain ⟨r, hr, _⟩ := TopCat.Sheaf.existsUnique_gluing' F V ⊤
    (fun x => homOfLE (show V x ≤ ⊤ from le_top)) hcover t hcompatible
  refine ⟨r, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' G V ⊤
    (fun x => homOfLE (show V x ≤ ⊤ from le_top)) hcover
  intro x
  rw [← m.hom.naturality_apply, hr x]
  exact ht x

end SchemeTheory
