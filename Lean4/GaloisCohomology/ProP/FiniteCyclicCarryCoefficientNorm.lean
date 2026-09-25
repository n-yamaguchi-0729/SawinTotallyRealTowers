/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.FiniteCyclicCarryCocycle
import GaloisCohomology.ProP.FiniteCyclicBarPeriodicH2Comparison
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Rep.Basic

set_option autoImplicit false

/-!
# Vanishing of a coefficient-changed cyclic carry class

A coefficient morphism sends the carry cocycle of a fixed element to the carry
cocycle of its image. If that image is the norm of an actual element in the
target representation, the resulting degree-two cohomology class is zero.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- A concrete norm preimage kills the coefficient-changed cyclic carry class. -/
theorem finiteCyclicCarry_coefficientMap_eq_zero_of_norm
    (A B : Rep R G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (φ : A ⟶ B)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap)
    (b : B) (hb : B.norm.hom b = φ.hom a.1) :
    groupCohomology.map (MonoidHom.id G) φ 2
        (groupCohomology.H2π A (finiteCyclicCarryTwoCocycle A g hg a)) = 0 := by
  have ha : A.ρ g a.1 = a.1 := by
    have hzero := a.2
    change A.ρ g a.1 - a.1 = 0 at hzero
    exact sub_eq_zero.mp hzero
  let aB : LinearMap.ker (Rep.applyAsHom B g - 𝟙 B).hom.toLinearMap :=
    ⟨φ.hom a.1, by
      change B.ρ g (φ.hom a.1) - φ.hom a.1 = 0
      rw [← Rep.hom_comm_apply φ g a.1, ha, sub_self]⟩
  have hcarry :
      groupCohomology.mapCocycles₂ (MonoidHom.id G) φ
          (finiteCyclicCarryTwoCocycle A g hg a) =
        finiteCyclicCarryTwoCocycle B g hg aB := by
    apply Subtype.ext
    funext xy
    change φ.hom (finiteCyclicCarry g hg xy.1 xy.2 • a.1) =
      finiteCyclicCarry g hg xy.1 xy.2 • φ.hom a.1
    exact map_nsmul φ.hom (finiteCyclicCarry g hg xy.1 xy.2) a.1
  rw [groupCohomology.H2π_comp_map_apply, hcarry,
    H2π_finiteCyclicCarryTwoCocycle]
  apply (Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff
    B g hg 2 (by decide) aB).2
  exact ⟨b, hb⟩

end ClassFieldTower.Cohomology
