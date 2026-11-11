/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingEquivalence
public import Nyll.GaloisCohomology.ProP.FiniteCyclicBarPeriodicCarryIdentity
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryCocycle
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Rep.Res

/-!
# The actual norm-prefix primitive of a cyclic carry

An element of a finite cyclic representation gives a normalized cochain
by applying its left-regular morphism to the original generator prefixes.
The original carry identity computes its differential as the carry times
the norm of that same element. Consequently a specified norm preimage
gives an explicit primitive, retained as a cochain rather than only as
the vanishing of a degree-two cohomology class.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped BigOperators

namespace ClassFieldTower.Cohomology

universe u v

section Prefix

variable {R : Type u} {G : Type v} [CommRing R] [CommGroup G] [Fintype G]

/-- The concrete prefix cochain attached to the specified element.
It uses the original left-regular prefixes of the chosen generator. -/
def finiteCyclicNormPrefixCochain (B : Rep.{max u v} R G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (b : B) : G → B :=
  fun x => (Rep.leftRegularHom B b).hom
    (finiteCyclicGeneratorPrefix (R := R) g hg x)

/-- The value of the retained cochain is the actual finite orbit sum
of its specified norm preimage. -/
theorem finiteCyclicNormPrefixCochain_apply (B : Rep.{max u v} R G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (b : B) (x : G) :
    finiteCyclicNormPrefixCochain B g hg b x =
      ∑ i ∈ Finset.range (finiteCyclicGeneratorCoordinate g hg x).val, B.ρ (g ^ i) b := by
  unfold finiteCyclicNormPrefixCochain finiteCyclicGeneratorPrefix finiteCyclicPrefixNat
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Rep.leftRegularHom_hom_single, one_smul]

/-- The concrete prefix primitive is normalized at the identity. -/
theorem finiteCyclicNormPrefixCochain_one (B : Rep.{max u v} R G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (b : B) :
    finiteCyclicNormPrefixCochain B g hg b 1 = 0 := by
  unfold finiteCyclicNormPrefixCochain
  rw [finiteCyclicGeneratorPrefix_one, map_zero]

/-- Evaluating the original full prefix at a coefficient element
gives the norm of that element in its original representation. -/
theorem finiteCyclicPrefixNat_card_leftRegularHom (B : Rep.{max u v} R G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (b : B) :
    (Rep.leftRegularHom B b).hom (finiteCyclicPrefixNat (R := R) g (Nat.card G)) =
      B.norm.asHom.hom b := by
  rw [finiteCyclicPrefixNat_card_eq_norm_one g hg]
  have h := congrArg
    (fun φ : Rep.leftRegular R G ⟶ B => φ.hom (MonoidAlgebra.single 1 (1 : R)))
    (Rep.norm_comm (Rep.leftRegularHom B b))
  change B.norm.asHom.hom ((Rep.leftRegularHom B b).hom (MonoidAlgebra.single 1 1)) =
    (Rep.leftRegularHom B b).hom
      ((Rep.leftRegular R G).norm.asHom.hom (MonoidAlgebra.single 1 1)) at h
  rw [Rep.leftRegularHom_hom_single, one_smul, map_one, Module.End.one_apply] at h
  exact h.symm

end Prefix

/-- Restricting integer scalars leaves the actual norm-prefix cochain
unchanged. Both sides evaluate the same finite orbit sum. -/
theorem finiteCyclicNormPrefixCochain_integerLift_apply
    {G : Type u} [CommGroup G] [Fintype G] (B : Rep.{u} ℤ G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (b : B) (x : G) :
    finiteCyclicNormPrefixCochain
        ((Rep.coefficientRingEquivalence
          (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) G).functor.obj B) g hg b x =
      finiteCyclicNormPrefixCochain B g hg b x := by
  erw [finiteCyclicNormPrefixCochain_apply, finiteCyclicNormPrefixCochain_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

section Cohomology

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- The differential of the same prefix cochain is the original
positive carry multiplied by the norm of its specified element. -/
theorem finiteCyclicNormPrefixCochain_d₁₂_apply (B : Rep R G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (b : B) (x y : G) :
    groupCohomology.d₁₂ B (finiteCyclicNormPrefixCochain B g hg b) (x, y) =
      finiteCyclicCarry g hg x y • B.norm.asHom.hom b := by
  change B.ρ x ((Rep.leftRegularHom B b).hom
        (finiteCyclicGeneratorPrefix (R := R) g hg y)) -
      (Rep.leftRegularHom B b).hom
        (finiteCyclicGeneratorPrefix (R := R) g hg (x * y)) +
      (Rep.leftRegularHom B b).hom
        (finiteCyclicGeneratorPrefix (R := R) g hg x) = _
  rw [← Rep.hom_comm_apply, ← map_sub, ← map_add,
    finiteCyclicGeneratorPrefix_carry, map_nsmul,
    finiteCyclicPrefixNat_card_leftRegularHom B g hg b]

/-- Pulling back the same explicit prefix cochain and changing its
coefficients preserves its displayed carry differential. The source
group may be larger than the cyclic quotient and need not be abelian. -/
theorem finiteCyclicNormPrefixCochain_pullback_d₁₂_apply
    {H : Type u} [Group H] (B : Rep R G) (D : Rep R H)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (b : B)
    (f : H →* G) (φ : Rep.res f B ⟶ D) (x y : H) :
    groupCohomology.d₁₂ D
        (fun z => φ.hom (finiteCyclicNormPrefixCochain B g hg b (f z))) (x, y) =
      finiteCyclicCarry g hg (f x) (f y) • φ.hom (B.norm.asHom.hom b) := by
  change D.ρ x (φ.hom (finiteCyclicNormPrefixCochain B g hg b (f y))) -
      φ.hom (finiteCyclicNormPrefixCochain B g hg b (f (x * y))) +
      φ.hom (finiteCyclicNormPrefixCochain B g hg b (f x)) = _
  rw [map_mul, ← Rep.hom_comm_apply, ← map_sub, ← map_add]
  change φ.hom (groupCohomology.d₁₂ B
    (finiteCyclicNormPrefixCochain B g hg b) (f x, f y)) = _
  rw [finiteCyclicNormPrefixCochain_d₁₂_apply, map_nsmul]

/-- A specified norm preimage gives a primitive of the original
carry cocycle after changing coefficients. The conclusion keeps the
explicit norm-prefix cochain. -/
theorem finiteCyclicNormPrefixCochain_d₁₂_of_coefficient_norm
    (A B : Rep R G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (φ : A ⟶ B)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap)
    (b : B) (hb : B.norm.asHom.hom b = φ.hom a.1) :
    groupCohomology.d₁₂ B (finiteCyclicNormPrefixCochain B g hg b) =
      (groupCohomology.mapCocycles₂ (MonoidHom.id G) φ
        (finiteCyclicCarryTwoCocycle A g hg a) : G × G → B) := by
  funext xy
  change groupCohomology.d₁₂ B (finiteCyclicNormPrefixCochain B g hg b) (xy.1, xy.2) =
    φ.hom (finiteCyclicCarry g hg xy.1 xy.2 • a.1)
  rw [finiteCyclicNormPrefixCochain_d₁₂_apply, hb, map_nsmul]

end Cohomology

end ClassFieldTower.Cohomology
