/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Topologies.FullSubgroupTopology.QuotientFormation

/-!
# Quotient varieties

A quotient variety is a quotient formation stable under pullback along group homomorphisms. This
file shows that the corresponding notion of open subgroup is likewise preserved by comap.
-/

open Set
open scoped Topology

namespace ProCGroups.Topologies

universe u

/-- A quotient variety is a quotient formation with the closure properties needed for varieties. -/
structure QuotientVariety extends QuotientFormation where
  /-- Admissible quotient kernels are closed under pullback along group homomorphisms. -/
  comap_closed :
    ∀ {G H : Type u} [Group G] [Group H] (f : G →* H) {N : Subgroup H},
      toQuotientFormation.contains N → toQuotientFormation.contains (N.comap f)

namespace QuotientVariety

variable (C : QuotientVariety)
variable {G H : Type u} [Group G] [Group H]

/-- Abstract form of the fact that full pro-\(C\) openness pulls back along a homomorphism. -/
theorem isOpenSubgroup_comap (f : G →* H) {K : Subgroup H}
    (hK : C.toQuotientFormation.IsOpenSubgroup K) :
    C.toQuotientFormation.IsOpenSubgroup (K.comap f) := by
  rcases hK with ⟨N, hN, hNK⟩
  refine ⟨N.comap f, C.comap_closed f hN, ?_⟩
  intro x hx
  exact hNK hx

end QuotientVariety

end ProCGroups.Topologies
