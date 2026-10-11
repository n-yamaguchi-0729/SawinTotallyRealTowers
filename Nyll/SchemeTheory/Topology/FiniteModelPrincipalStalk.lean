/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Topology.Sheaves.Alexandrov
import Mathlib.Topology.Sheaves.Stalks
import Nyll.SchemeTheory.Topology.CompactOpenFiniteModels

/-!
# Principal-neighborhood stalks in finite compact-open models

The germ map from a principal Alexandrov neighborhood is an isomorphism:
that neighborhood is a terminal object in the opposite neighborhood
category defining the actual stalk. A singleton compact-open model
recovers its generating compact open at every point of that open.
The Lean proofs are original.
-/

noncomputable section

universe u

open CategoryTheory Limits TopCat TopologicalSpace Topology Opposite

namespace SchemeTheory

/-- The actual germ map identifies sections on a principal open with the
stalk of any type-valued presheaf in the upper-set topology. -/
def principalOpenStalkIso {Y : TopCat.{u}} [Preorder Y] [Topology.IsUpperSet Y]
    (P : Y.Presheaf (Type u)) (y : Y) :
    P.obj (op (Alexandrov.principalOpen y)) ≅ TopCat.Presheaf.stalk P y := by
  let W : OpenNhds y :=
    ⟨Alexandrov.principalOpen y, Alexandrov.self_mem_principalOpen y⟩
  have hterminal : IsTerminal (op W) := by
    exact IsTerminal.ofUniqueHom
      (fun V : (OpenNhds y)ᵒᵖ => (homOfLE (show W ≤ V.unop from
        (Alexandrov.principalOpen_le_iff V.unop.1).mpr V.unop.2)).op)
      (fun _ f => Subsingleton.elim f _)
  have hg : IsIso (TopCat.Presheaf.germ P (Alexandrov.principalOpen y) y
      (Alexandrov.self_mem_principalOpen y)) :=
    isIso_ι_of_isTerminal hterminal ((OpenNhds.inclusion y).op ⋙ P)
  exact asIso (TopCat.Presheaf.germ P (Alexandrov.principalOpen y) y
    (Alexandrov.self_mem_principalOpen y))

theorem principalOpenStalkIso_hom {Y : TopCat.{u}} [Preorder Y] [Topology.IsUpperSet Y]
    (P : Y.Presheaf (Type u)) (y : Y) :
    (principalOpenStalkIso P y).hom = TopCat.Presheaf.germ P
      (Alexandrov.principalOpen y) y (Alexandrov.self_mem_principalOpen y) := rfl

namespace CompactOpenFiniteModel

/-- A single compact-open coordinate gives exactly that open as the
principal-neighborhood preimage at each point it contains. -/
theorem neighborhood_singleton {X : TopCat.{u}} (U : CompactOpens X)
    (x : X) (hx : x ∈ (U : Set X)) : neighborhood {U} x = U.toOpens := by
  classical
  apply Opens.ext
  ext y
  constructor
  · intro hy
    exact (mem_neighborhood {U} x y).mp hy U (Finset.mem_singleton_self U) hx
  · intro hy
    refine (mem_neighborhood {U} x y).mpr ?_
    intro V hV _
    have hVU : V = U := Finset.mem_singleton.mp hV
    subst V
    exact hy

end CompactOpenFiniteModel

end SchemeTheory
