/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Roots of unity under field embeddings

Proves that a field embedding induces a bijection on n-th roots of unity for nonzero n when the
source contains a primitive n-th root. It also bundles root groups and their maps induced by
coefficient homomorphisms.
-/

namespace RamificationTheory.HilbertRamification

open CategoryTheory

universe u v

/-- If the lower field has a primitive n-th root, its full n-th root group
maps bijectively to the full n-th root group in every field extension. -/
theorem restrictRootsOfUnity_bijective_of_primitiveRoot
    {k : Type u} {l : Type v} [Field k] [Field l] (f : k →+* l)
    (n : ℕ) [NeZero n] (hroot : ∃ ζ : k, IsPrimitiveRoot ζ n) :
    Function.Bijective (restrictRootsOfUnity f n) := by
  have hinj : Function.Injective (restrictRootsOfUnity f n) := by
    intro x y h
    apply Subtype.ext
    apply Units.ext
    apply f.injective
    have hv := congrArg (fun z : rootsOfUnity n l => ((z : lˣ) : l)) h
    exact hv
  obtain ⟨ζ, hζ⟩ := hroot
  apply hinj.bijective_of_nat_card_le
  rw [hζ.card_rootsOfUnity]
  exact card_rootsOfUnity l n

/-- A full root group as its native group object. -/
def rootsGroupObject (k : Type u) [CommRing k] (n : ℕ) : GrpCat.{u} :=
  GrpCat.of (rootsOfUnity n k)

/-- The actual root-group map induced by a coefficient ring map. -/
def rootsGroupMap {k l : Type u} [CommRing k] [CommRing l] (f : k →+* l) (n : ℕ) :
    GrpCat.Hom (rootsGroupObject k n) (rootsGroupObject l n) where
  hom' := restrictRootsOfUnity f n

/-- The native root-group morphism is onto whenever its source field
already contains a primitive root of the nonzero degree. -/
theorem rootsGroupMap_surjective_of_primitiveRoot
    {k l : Type u} [Field k] [Field l] (f : k →+* l)
    (n : ℕ) [NeZero n] (hroot : ∃ ζ : k, IsPrimitiveRoot ζ n) :
    Function.Surjective (rootsGroupMap f n).hom'.toFun :=
  (restrictRootsOfUnity_bijective_of_primitiveRoot f n hroot).2

end RamificationTheory.HilbertRamification
