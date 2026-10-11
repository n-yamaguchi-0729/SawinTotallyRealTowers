/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Nyll.ProCGroups.Topologies.QuotientMaps
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Abelianization modulo a power

For a topological group `G`, first quotient by the closed commutator subgroup,
then by the subgroup of `q`-th powers. Continuous homomorphisms descend to
this quotient, and maps to commutative groups of exponent dividing `q` factor
through it.
-/

namespace ProCGroups.Abelian

universe u v

/-- The abelianization of a topological group modulo its `q`-th powers. -/
abbrev abelianModPower
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (q : ℕ) : Type u :=
  TopologicalAbelianization G ⧸
    (powMonoidHom (α := TopologicalAbelianization G) q).range

/-- A continuous homomorphism induces a homomorphism of abelianizations
modulo `q`-th powers. -/
noncomputable def abelianModPowerMap
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {H : Type v} [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
    (q : ℕ) (f : G →ₜ* H) :
    abelianModPower G q →ₜ* abelianModPower H q :=
  let φ : abelianModPower G q →* abelianModPower H q :=
    QuotientGroup.map
      (powMonoidHom (α := TopologicalAbelianization G) q).range
      (powMonoidHom (α := TopologicalAbelianization H) q).range
      (TopologicalAbelianization.map f).toMonoidHom
      (by
        rintro x ⟨y, rfl⟩
        exact ⟨TopologicalAbelianization.map f y, by
          exact (map_pow (TopologicalAbelianization.map f) y q).symm⟩)
  { toMonoidHom := φ
    continuous_toFun := by
      rw [← (QuotientGroup.isOpenQuotientMap_mk
        (N := (powMonoidHom (α := TopologicalAbelianization G) q).range)).continuous_comp_iff]
      change Continuous (fun x : TopologicalAbelianization G =>
        ((TopologicalAbelianization.map f x : TopologicalAbelianization H) :
          abelianModPower H q))
      exact QuotientGroup.continuous_mk.comp (TopologicalAbelianization.map f).continuous }

/-- The induced map on abelianizations modulo powers sends the class of a
representative to the class of its image. -/
@[simp] theorem abelianModPowerMap_mk
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {H : Type v} [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
    (q : ℕ) (f : G →ₜ* H) (g : G) :
    abelianModPowerMap q f
      (QuotientGroup.mk' (powMonoidHom (α := TopologicalAbelianization G) q).range
        (TopologicalAbelianization.mk G g)) =
      QuotientGroup.mk' (powMonoidHom (α := TopologicalAbelianization H) q).range
        (TopologicalAbelianization.mk H (f g)) := by
  rfl

/-- A continuous homomorphism to a commutative group of exponent dividing `q`
factors through the topological abelianization modulo `q`-th powers. -/
noncomputable def abelianModPowerLift
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {A : Type v} [TopologicalSpace A] [CommGroup A] [T1Space A]
    (q : ℕ) (f : G →ₜ* A) (hpow : ∀ a : A, a ^ q = 1) :
    abelianModPower G q →ₜ* A :=
  ProCGroups.QuotientGroup.liftₜ
    (powMonoidHom (α := TopologicalAbelianization G) q).range
    (TopologicalAbelianization.lift f) (by
      rintro x ⟨y, rfl⟩
      change (TopologicalAbelianization.lift f) (y ^ q) = 1
      rw [map_pow]
      exact hpow _)

/-- The factorization through `Gᵃᵇ/q` evaluates to the original map on
representatives. -/
@[simp] theorem abelianModPowerLift_mk
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {A : Type v} [TopologicalSpace A] [CommGroup A] [T1Space A]
    (q : ℕ) (f : G →ₜ* A) (hpow : ∀ a : A, a ^ q = 1) (g : G) :
    abelianModPowerLift q f hpow
      (QuotientGroup.mk' (powMonoidHom (α := TopologicalAbelianization G) q).range
        (TopologicalAbelianization.mk G g)) = f g := by
  simpa only [abelianModPowerLift, ProCGroups.QuotientGroup.liftₜ_apply_mk] using
    (TopologicalAbelianization.lift_apply_mk f g)

/-- Surjectivity is preserved by the factorization through `Gᵃᵇ/q`. -/
theorem abelianModPowerLift_surjective
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {A : Type v} [TopologicalSpace A] [CommGroup A] [T1Space A]
    (q : ℕ) (f : G →ₜ* A) (hpow : ∀ a : A, a ^ q = 1)
    (hf : Function.Surjective f) :
    Function.Surjective (abelianModPowerLift q f hpow) := by
  intro a
  obtain ⟨g, rfl⟩ := hf a
  exact ⟨QuotientGroup.mk' (powMonoidHom (α := TopologicalAbelianization G) q).range
    (TopologicalAbelianization.mk G g), abelianModPowerLift_mk q f hpow g⟩


variable {G H J : Type*}
  [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
  [TopologicalSpace J] [Group J] [IsTopologicalGroup J]

/-- The canonical continuous quotient map to abelianization modulo powers. -/
def abelianModPowerMk (G : Type*) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (q : ℕ) : G →ₜ* abelianModPower G q :=
  { toMonoidHom := (QuotientGroup.mk'
      (powMonoidHom (α := TopologicalAbelianization G) q).range).comp
        (TopologicalAbelianization.mk G)
    continuous_toFun := QuotientGroup.continuous_mk.comp
      (TopologicalAbelianization.mkₜ G).continuous }

/-- Every class modulo commutators and powers has a group representative. -/
theorem abelianModPowerMk_surjective (q : ℕ) :
    Function.Surjective (abelianModPowerMk G q) :=
  (QuotientGroup.mk'_surjective _).comp (TopologicalAbelianization.surjective_mk G)

/-- Passage to abelianizations modulo powers respects composition. -/
theorem abelianModPowerMap_comp (q : ℕ) (f : G →ₜ* H) (g : H →ₜ* J) :
    abelianModPowerMap q (g.comp f) =
      (abelianModPowerMap q g).comp (abelianModPowerMap q f) := by
  ext x
  obtain ⟨a, rfl⟩ := abelianModPowerMk_surjective (G := G) q x
  rfl

/-- The induced map carries the class of an element to the class of its image. -/
theorem abelianModPowerMap_mk_apply (q : ℕ) (f : G →ₜ* H) (a : G) :
    abelianModPowerMap q f (abelianModPowerMk G q a) =
      abelianModPowerMk H q (f a) := rfl


end ProCGroups.Abelian
