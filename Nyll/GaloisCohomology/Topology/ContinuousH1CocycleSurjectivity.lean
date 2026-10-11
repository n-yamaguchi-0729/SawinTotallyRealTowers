/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Topology.ContinuousH1Lifting

/-! # Cocycle lifting implies surjectivity on actual continuous H¹ -/

open CategoryTheory TopRep ContRepresentation

namespace ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem homogeneous_oneCocycle_eq_difference
    (X : TopRep.{u} ℤ G) (z : cocycles X 1) (g h : G) :
    ((homogeneousCochains X).iCycles 1 z).1 g h =
      (crossedHomOfCocycle X z).toFun h - (crossedHomOfCocycle X z).toFun g := by
  let σ := (homogeneousCochains X).iCycles 1 z
  have hz := ConcreteCategory.congr_hom ((homogeneousCochains X).iCycles_d 1 2) z
  have hd := congrArg (fun τ => τ 1 g h) (homogeneousCochains.d_apply X 1 σ)
  have hz' := congrArg (fun τ => τ.1 1 g h) hz
  change (((homogeneousCochains X).d 1 2).hom σ).1 1 g h = 0 at hz'
  rw [hd] at hz'
  simp only [d_succ, d_zero, TopRep.hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun,
    ContinuousMap.const_apply, ContinuousMap.comp_apply, ConcreteCategory.hom_ofHom,
    ContinuousMap.sub_apply] at hz'
  exact sub_eq_zero.mp hz'

/-- Exact lifting of all continuous crossed homomorphisms gives a surjection on H¹. -/
theorem map_surjective_of_crossedHom_lifting
    (X Y : TopRep.{u} ℤ G)
    (f : TopRep.res (ContinuousMonoidHom.id G) X ⟶ Y)
    (hlift : ∀ c : CrossedHom Y, ∃ d : CrossedHom X,
      ∀ g : G, f.hom (d.toFun g) = c.toFun g) :
    Function.Surjective (map (ContinuousMonoidHom.id G) f 1).hom := by
  intro a
  obtain ⟨z, rfl⟩ := π_surjective Y 1 a
  obtain ⟨d, hd⟩ := hlift (crossedHomOfCocycle Y z)
  refine ⟨π X 1 d.toCocycle, ?_⟩
  have hcycles : cocyclesMap (ContinuousMonoidHom.id G) f 1 d.toCocycle = z := by
    let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)
    have hinj := (ModuleCat.mono_iff_injective (F.map ((homogeneousCochains Y).iCycles 1))).mp
      inferInstance
    apply hinj
    change (homogeneousCochains Y).iCycles 1
      (cocyclesMap (ContinuousMonoidHom.id G) f 1 d.toCocycle) =
        (homogeneousCochains Y).iCycles 1 z
    have hmap := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (cochainsMap (ContinuousMonoidHom.id G) f) 1) d.toCocycle
    change (homogeneousCochains Y).iCycles 1
      (cocyclesMap (ContinuousMonoidHom.id G) f 1 d.toCocycle) =
      (cochainsMap (ContinuousMonoidHom.id G) f).f 1
        ((homogeneousCochains X).iCycles 1 d.toCocycle) at hmap
    rw [hmap, d.iCycles_toCocycle]
    apply Subtype.ext
    ext g h
    change f.hom (d.toFun h - d.toFun g) = ((homogeneousCochains Y).iCycles 1 z).1 g h
    rw [map_sub, hd, hd, homogeneous_oneCocycle_eq_difference]
  have hnat := ConcreteCategory.congr_hom (π_map (ContinuousMonoidHom.id G) f 1) d.toCocycle
  change (map (ContinuousMonoidHom.id G) f 1) (π X 1 d.toCocycle) = _ at hnat
  exact hnat.trans (congrArg (π Y 1) hcycles)

end ContinuousCohomology
