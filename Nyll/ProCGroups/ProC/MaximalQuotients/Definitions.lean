/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ProCGroup

/-!
# Maximal pro-\(C\) quotients

`IsMaximalProCQuotient C π` states that `π` is a continuous quotient map onto
a profinite group with a pro-\(C\) basis and that every continuous map to a
pro-\(C\) target factors through it uniquely.
-/

namespace ProCGroups.ProC

universe u

/-- Maximal pro-\(C\) quotient groups via their universal property. -/
structure IsMaximalProCQuotient
    (C : FiniteGroupClass)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
      [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    (π : G →* Q) : Prop where
  /-- The quotient \(Q\) has an open-normal basis whose finite quotients lie in \(C\). -/
  hasOpenNormalBasisInClass : HasOpenNormalBasisInClass C Q
  /-- The quotient homomorphism \(\pi\) is continuous. -/
  continuous_π : Continuous π
  /-- The quotient homomorphism \(\pi\) is surjective. -/
  surjective_π : Function.Surjective π
  /--
  Every continuous homomorphism from \(G\) to a pro-\(C\) target factors uniquely and
  continuously through \(Q\).
  -/
  existsUnique_lift :
    ∀ {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H],
      HasOpenNormalBasisInClass C H →
      ∀ (φ : G →* H), Continuous φ →
        ∃! φbar : Q →* H, Continuous φbar ∧ φbar.comp π = φ

end ProCGroups.ProC
