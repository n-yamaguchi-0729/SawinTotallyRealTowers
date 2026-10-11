/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Boundary.CyclotomicInversion
import Nyll.ProCGroups.Generation.Basic

/-!
# Topologically cyclic inertia and cyclotomic inversion

This file upgrades the elementwise abelian consequence of cyclotomic
inversion to a statement about an entire topologically cyclic inertia group.
The generator is killed by inversion and oddness, and continuity then kills
the whole restriction.
-/

namespace ProCGroups.Boundary

universe u v w

/-- A continuous map to an abelian Hausdorff group is trivial on a
topologically cyclic inertia group when the image of a topological generator
has order prime to two and its ambient image is conjugate to its inverse. -/
theorem restriction_eq_one_of_topological_generator_isConj_inv_of_coprime_two
    {I : Type u} {G : Type v} {A : Type w}
    [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
    [Group G] [TopologicalSpace G]
    [CommGroup A] [TopologicalSpace A] [T2Space A]
    (inertiaMap : I →ₜ* G) (q : G →ₜ* A) {gamma : I}
    (hGenerates :
      Generation.TopologicallyGenerates (G := I) ({gamma} : Set I))
    (hConj : IsConj (inertiaMap gamma) (inertiaMap gamma)⁻¹)
    (hCoprime : Nat.Coprime (orderOf (q (inertiaMap gamma))) 2) :
    q.comp inertiaMap = 1 := by
  apply
    Generation.continuousMonoidHom_ext_of_topologicallyGenerates
      hGenerates
  intro x hx
  have hxgamma : x = gamma := Set.mem_singleton_iff.mp hx
  subst x
  change q (inertiaMap gamma) = 1
  exact
    map_eq_one_of_isConj_inv_of_coprime_two
      q.toMonoidHom hConj hCoprime

end ProCGroups.Boundary
