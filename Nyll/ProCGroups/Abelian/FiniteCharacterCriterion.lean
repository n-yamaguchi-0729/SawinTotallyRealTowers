/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.ProCGroups.Abelian.ProfiniteCharacterCriterion
import Nyll.ProCGroups.Abelian.ProfiniteBidual
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Finite coefficient detection of profinite abelian isomorphisms

Every actual circle character has finite image. Thus bijectivity on characters
with finite subgroup coefficients gives bijectivity on all circle characters,
and consequently a topological group isomorphism of the original groups.
-/

noncomputable section

namespace ProCGroups.Duality

open ProCGroups.ProC

universe u v

variable {G : Type u} {H : Type v} [CommGroup G] [CommGroup H]
  [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  [CompactSpace G] [CompactSpace H]
  [TotallyDisconnectedSpace G] [TotallyDisconnectedSpace H]

private theorem exists_finite_character_range (χ : PontryaginDual G) :
    ∃ (A : Subgroup Circle) (_ : Finite A) (χA : G →ₜ* A),
      ∀ g : G, (χA g : Circle) = χ g := by
  obtain ⟨U, hU⟩ := exists_openNormal_le_character_ker χ
  let Q := G ⧸ (U : Subgroup G)
  let q : G →ₜ* Q := OpenNormalSubgroup.quotientProj U
  let χQ : Q →ₜ* Circle := ProCGroups.QuotientGroup.liftₜ (U : Subgroup G) χ hU
  let A : Subgroup Circle := χQ.toMonoidHom.range
  have : Finite A := Finite.of_surjective χQ.toMonoidHom.rangeRestrict
    χQ.toMonoidHom.rangeRestrict_surjective
  let χAQ : Q →ₜ* A :=
    { toMonoidHom := χQ.toMonoidHom.rangeRestrict
      continuous_toFun := continuous_of_discreteTopology }
  exact ⟨A, inferInstance, χAQ.comp q, fun _ => rfl⟩

/-- Finite coefficient pullbacks determine the pullback on all circle characters. -/
theorem bijective_character_pullback_of_finite (f : G →ₜ* H)
    (hf : ∀ (A : Subgroup Circle) [Finite A], Function.Bijective (f.compLeft A)) :
    Function.Bijective (PontryaginDual.map f) := by
  constructor
  · apply (injective_iff_map_eq_one (PontryaginDual.map f)).mpr
    intro χ hχ
    obtain ⟨A, hA, χA, hχA⟩ := exists_finite_character_range χ
    have hcomp : f.compLeft A χA = 1 := by
      apply ContinuousMonoidHom.ext
      intro g
      apply Subtype.ext
      change (χA (f g) : Circle) = 1
      rw [hχA]
      exact congrArg (fun ψ : PontryaginDual G => ψ g) hχ
    have hzero : χA = 1 := (hf A).injective (hcomp.trans (map_one (f.compLeft A)).symm)
    apply PontryaginDual.ext
    intro g
    rw [← hχA, hzero]
    rfl
  · intro χ
    obtain ⟨A, hA, χA, hχA⟩ := exists_finite_character_range χ
    obtain ⟨ψ, hψ⟩ := (hf A).surjective χA
    let i : A →ₜ* Circle :=
      { toMonoidHom := A.subtype
        continuous_toFun := continuous_subtype_val }
    refine ⟨i.comp ψ, ?_⟩
    apply PontryaginDual.ext
    intro g
    have hh : ψ (f g) = χA g := congrArg (fun z : G →ₜ* A => z g) hψ
    exact (congrArg Subtype.val hh).trans (hχA g)

/-- An actual map inducing bijections on all finite subgroup-valued characters
is a topological isomorphism. -/
def equivOfBijectiveFiniteCharacterPullback (f : G →ₜ* H)
    (hf : ∀ (A : Subgroup Circle) [Finite A], Function.Bijective (f.compLeft A)) :
    G ≃ₜ* H :=
  equivOfBijectiveCharacterPullback f (bijective_character_pullback_of_finite f hf)

end ProCGroups.Duality
