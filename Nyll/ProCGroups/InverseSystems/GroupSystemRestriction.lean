/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.InverseSystems.CofinalityAndDensity

/-!
# Group structures on restricted inverse systems

The existing restriction keeps the stage groups and transition homomorphisms.
This canonical instance permits both homomorphisms to the restricted limit and
its coordinatewise group laws to use the original inverse-system owner.
-/

namespace ProCGroups.InverseSystems

universe u v

variable {I : Type u} [Preorder I] (S : InverseSystem.{u, v} (I := I))
  [∀ i, Group (S.X i)] [IsGroupSystem S]

instance InverseSystem.restrict_groups (J : Set I) :
    ∀ j : J, Group ((S.restrict J).X j) :=
  fun j => inferInstanceAs (Group (S.X j.val))

instance InverseSystem.restrict_isGroupSystem (J : Set I) :
    IsGroupSystem (S.restrict J) where
  map_one := fun {_ _} h => IsGroupSystem.map_one (S := S) h
  map_mul := fun {_ _} h x y => IsGroupSystem.map_mul (S := S) h x y
  map_inv := fun {_ _} h x => IsGroupSystem.map_inv (S := S) h x

end ProCGroups.InverseSystems
