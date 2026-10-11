/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Topology.ContinuousCrossedHom

/-! # Lifting crossed homomorphisms through a surjective H¹ map -/

open CategoryTheory TopRep ContRepresentation

namespace ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
private theorem hom_action {R : Type} [Ring R] [TopologicalSpace R]
    {X Y : TopRep.{u} R G}
    (f : TopRep.res (ContinuousMonoidHom.id G) X ⟶ Y) (g : G) (t : X) :
    f.hom (X.ρ g t) = Y.ρ g (f.hom t) := f.hom.isIntertwining g t

/-- Surjectivity on H¹ and on coefficients gives exact lifts of continuous
crossed homomorphisms. The continuity of orbit maps supplies the continuous
principal cocycle used to adjust a lifted cohomology class. -/
theorem exists_crossedHom_lift_of_map_surjective
    (X Y : TopRep.{u} ℤ G)
    (f : TopRep.res (ContinuousMonoidHom.id G) X ⟶ Y)
    (hf : Function.Surjective f.hom)
    (horbit : ∀ a : X, Continuous (fun g : G => X.ρ g a))
    (hH1 : Function.Surjective (map (ContinuousMonoidHom.id G) f 1).hom)
    (c : CrossedHom Y) :
    ∃ d : CrossedHom X, ∀ g : G, f.hom (d.toFun g) = c.toFun g := by
  obtain ⟨a, ha⟩ := hH1 (π Y 1 c.toCocycle)
  obtain ⟨z, hz⟩ := π_surjective X 1 a
  have hclass : π Y 1 (cocyclesMap (ContinuousMonoidHom.id G) f 1 z) =
      π Y 1 c.toCocycle := by
    have hnat := ConcreteCategory.congr_hom (π_map (ContinuousMonoidHom.id G) f 1) z
    change (map (ContinuousMonoidHom.id G) f 1) (π X 1 z) = _ at hnat
    rw [hz] at hnat
    exact hnat.symm.trans ha
  let w := cocyclesMap (ContinuousMonoidHom.id G) f 1 z - c.toCocycle
  have hw : π Y 1 w = 0 := by
    change π Y 1 (cocyclesMap (ContinuousMonoidHom.id G) f 1 z - c.toCocycle) = 0
    rw [map_sub, hclass, sub_self]
  obtain ⟨b, hb⟩ := exists_boundary_of_π_eq_zero Y 0 w hw
  let e := crossedHomOfCocycle X z
  have hvalue (g : G) : f.hom (e.toFun g) - c.toFun g =
      Y.ρ g (b.1 1) - b.1 1 := by
    have hbi := congrArg (fun τ => τ g) (b.2 g)
    have hbi' : Y.ρ g (b.1 1) = b.1 g := by
      simpa only [coind₁_apply_apply, inv_mul_cancel] using hbi
    rw [hbi']
    have hbd := congrArg (fun τ => τ.1 1 g) hb
    have hd := congrArg (fun τ => τ 1 g) (homogeneousCochains.d_apply Y 0 b)
    rw [hd] at hbd
    simp only [d_succ, d_zero, TopRep.hom_sub, ContIntertwiningMap.sub_apply,
      coind₁ι_toFun, coind₁Map_toFun, ConcreteCategory.hom_ofHom,
      ContinuousMap.sub_apply] at hbd
    have hmap := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (cochainsMap (ContinuousMonoidHom.id G) f) 1) z
    have hmap' : (homogeneousCochains Y).iCycles 1
        (cocyclesMap (ContinuousMonoidHom.id G) f 1 z) =
      (cochainsMap (ContinuousMonoidHom.id G) f).f 1
        ((homogeneousCochains X).iCycles 1 z) := hmap
    change b.1 g - b.1 1 = ((homogeneousCochains Y).iCycles 1 w).1 1 g at hbd
    dsimp only [w] at hbd
    rw [map_sub, hmap', c.iCycles_toCocycle] at hbd
    change b.1 g - b.1 1 = f.hom (e.toFun g) - (c.toFun g - c.toFun 1) at hbd
    rw [c.map_one, sub_zero] at hbd
    exact hbd.symm
  obtain ⟨t, ht⟩ := hf (b.1 1)
  let d : CrossedHom X :=
    { toFun := fun g => e.toFun g - (X.ρ g t - t)
      continuous_toFun := e.continuous_toFun.sub ((horbit t).sub continuous_const)
      map_mul := by
        intro g h
        rw [e.map_mul, map_mul]
        change e.toFun g + X.ρ g (e.toFun h) - (X.ρ g (X.ρ h t) - t) = _
        rw [map_sub, map_sub]
        abel }
  refine ⟨d, ?_⟩
  intro g
  change f.hom (e.toFun g - (X.ρ g t - t)) = c.toFun g
  have hft := hom_action f g t
  rw [map_sub, map_sub, hft, ht]
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp (hvalue g)).trans (add_comm _ _))

end ContinuousCohomology
