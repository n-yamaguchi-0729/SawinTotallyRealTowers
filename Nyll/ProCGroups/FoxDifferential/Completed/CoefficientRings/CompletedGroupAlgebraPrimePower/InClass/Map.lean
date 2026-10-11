/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.InClass.System.Ring.Projection

/-!
# Fox differential: coefficient rings — prime-power completed group algebra — in class — map

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraMapStageInClass`
  The finite-stage component of a class-restricted prime-power completed group-algebra map.
- `primePowerCompletedGroupAlgebraMapInClass`
  The class-restricted prime-power completed group-algebra map induced by a continuous homomorphism,
  as an additive map on the inverse-limit subtype.
- `primePowerCompletedGroupAlgebraMapStageInClass_of`
  The class-indexed prime-power stage map sends a group-like basis element to the basis element
  supported at its quotient image.
- `primePowerCompletedGroupAlgebraMapStageInClass_single`
  The class-indexed prime-power stage map transports a singleton coefficient to the singleton at its
  quotient image.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ)
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section MapStageInClass

variable {G0 H0 : Type u}
variable [Group G0] [TopologicalSpace G0] [IsTopologicalGroup G0]
variable [Group H0] [TopologicalSpace H0] [IsTopologicalGroup H0]

/-- The finite-stage component of a class-restricted prime-power completed group-algebra map. -/
def primePowerCompletedGroupAlgebraMapStageInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψ : ContinuousMonoidHom G0 H0) (i : PrimePowerCompletedGroupAlgebraIndexInClass H0 C) :
    PrimePowerCompletedGroupAlgebraStageInClass ℓ G0 C
        (i.1, completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ i.2) →+*
      PrimePowerCompletedGroupAlgebraStageInClass ℓ H0 C i :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff (ℓ ^ i.1))
    (completedGroupAlgebraComapQuotientMapInClass (G := G0) (H := H0) C hC ψ i.2)

/--
The class-indexed prime-power stage map sends a group-like basis element to the basis element
supported at its quotient image.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraMapStageInClass_of
    (C : ProCGroups.FiniteGroupClass.{u}) (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψ : ContinuousMonoidHom G0 H0) (i : PrimePowerCompletedGroupAlgebraIndexInClass H0 C)
    (q : CompletedGroupAlgebraQuotientInClass G0 C
      (completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ i.2)) :
    primePowerCompletedGroupAlgebraMapStageInClass (ℓ := ℓ) C hC ψ i
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1)) _ q) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1)) _
        (completedGroupAlgebraComapQuotientMapInClass (G := G0) (H := H0) C hC ψ i.2 q) := by
  simp only [primePowerCompletedGroupAlgebraMapStageInClass, MonoidAlgebra.of_apply,
    MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]

/--
The class-indexed prime-power stage map transports a singleton coefficient to the singleton at its
quotient image.
-/
theorem primePowerCompletedGroupAlgebraMapStageInClass_single
    (C : ProCGroups.FiniteGroupClass.{u}) (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψ : ContinuousMonoidHom G0 H0) (i : PrimePowerCompletedGroupAlgebraIndexInClass H0 C)
    (q : CompletedGroupAlgebraQuotientInClass G0 C
      (completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ i.2))
    (a : ModNCompletedCoeff (ℓ ^ i.1)) :
    primePowerCompletedGroupAlgebraMapStageInClass (ℓ := ℓ) C hC ψ i
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single
        (completedGroupAlgebraComapQuotientMapInClass (G := G0) (H := H0) C hC ψ i.2 q) a := by
  simp only [primePowerCompletedGroupAlgebraMapStageInClass,
    MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]

/--
Surjectivity of the underlying continuous homomorphism implies surjectivity of the finite-stage
class-restricted completed maps.
-/
theorem primePowerCompletedGroupAlgebraMapStageInClass_surjective_of_surjective
    (C : ProCGroups.FiniteGroupClass.{u}) (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψ : ContinuousMonoidHom G0 H0) (hψ : Function.Surjective ψ)
    (i : PrimePowerCompletedGroupAlgebraIndexInClass H0 C) :
    Function.Surjective
      (primePowerCompletedGroupAlgebraMapStageInClass (ℓ := ℓ) C hC ψ i) := by
  intro x
  obtain ⟨y, hy⟩ :=
    Finsupp.mapDomain_surjective (M := ModNCompletedCoeff (ℓ ^ i.1))
      (completedGroupAlgebraComapQuotientMapInClass_surjective_of_surjective
        (G := G0) (H := H0) C hC ψ hψ i.2) x.coeff
  refine ⟨MonoidAlgebra.ofCoeff y, ?_⟩
  apply MonoidAlgebra.coeff_injective
  exact hy

/-- Class-restricted finite-stage maps commute with the prime-power transition maps. -/
theorem primePowerCompletedGroupAlgebraMapStageInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{u}) (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψ : ContinuousMonoidHom G0 H0)
    {i j : PrimePowerCompletedGroupAlgebraIndexInClass H0 C} (hij : i ≤ j) :
    (primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := H0) C hij).comp
        (primePowerCompletedGroupAlgebraMapStageInClass (ℓ := ℓ) C hC ψ j) =
      (primePowerCompletedGroupAlgebraMapStageInClass (ℓ := ℓ) C hC ψ i).comp
        (primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G0) C
          (show
            (i.1, completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ i.2) ≤
              (j.1, completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ j.2) from
            ⟨hij.1,
              completedGroupAlgebraComapIndexInClass_mono
                (G := G0) (H := H0) C hC ψ hij.2⟩)) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      ((primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := H0) C hij).comp
          (primePowerCompletedGroupAlgebraMapStageInClass (ℓ := ℓ) C hC ψ j)) x =
        ((primePowerCompletedGroupAlgebraMapStageInClass (ℓ := ℓ) C hC ψ i).comp
          (primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G0) C
            (show
              (i.1, completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ i.2) ≤
                (j.1,
                  completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ j.2) from
              ⟨hij.1,
                completedGroupAlgebraComapIndexInClass_mono
                  (G := G0) (H := H0) C hC ψ hij.2⟩))) x)
    x ?_ ?_ ?_
  · intro q
    rw [RingHom.comp_apply, RingHom.comp_apply,
      primePowerCompletedGroupAlgebraMapStageInClass_of,
      primePowerCompletedGroupAlgebraTransitionInClass_of,
      primePowerCompletedGroupAlgebraTransitionInClass_of]
    change
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1))
          (CompletedGroupAlgebraQuotientInClass H0 C i.2)
          ((OpenNormalSubgroupInClass.map
            (C := C) (G := H0)
            (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2)
            (completedGroupAlgebraComapQuotientMapInClass
              (G := G0) (H := H0) C hC ψ j.2 q)) =
        primePowerCompletedGroupAlgebraMapStageInClass (ℓ := ℓ) C hC ψ i
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1))
            (CompletedGroupAlgebraQuotientInClass G0 C
              (completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ i.2))
            ((OpenNormalSubgroupInClass.map
              (C := C) (G := G0)
              (U := OrderDual.ofDual
                (completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ i.2))
              (V := OrderDual.ofDual
                (completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ j.2))
              (completedGroupAlgebraComapIndexInClass_mono
                (G := G0) (H := H0) C hC ψ hij.2)) q))
    erw [primePowerCompletedGroupAlgebraMapStageInClass_of]
    exact congrArg (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1))
      (CompletedGroupAlgebraQuotientInClass H0 C i.2))
      (congrFun
        (congrArg DFunLike.coe
          (completedGroupAlgebraComapQuotientMapInClass_compatible
            (G := G0) (H := H0) C hC ψ hij.2)) q)
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    simp only [primePowerCompletedGroupAlgebraTransitionInClass,
        modNCompletedGroupAlgebraStageCoeffMapInClass,
  modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe,
      primePowerCompletedGroupAlgebraMapStageInClass,
  map_intCast, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      MonoidAlgebra.mapDomainRingHom_apply]

/--
The class-restricted prime-power completed group-algebra map induced by a continuous
homomorphism, as an additive map on the inverse-limit subtype.
-/
def primePowerCompletedGroupAlgebraMapInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψ : ContinuousMonoidHom G0 H0) :
    PrimePowerCompletedGroupAlgebraInClass ℓ G0 C →+
      PrimePowerCompletedGroupAlgebraInClass ℓ H0 C where
  toFun x := ⟨fun i =>
      primePowerCompletedGroupAlgebraMapStageInClass (ℓ := ℓ) C hC ψ i
        (primePowerCompletedGroupAlgebraProjectionInClass
          (ℓ := ℓ) (G := G0) C
          (i.1, completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ i.2) x), by
    intro i j hij
    let hsource :
        (i.1, completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ i.2) ≤
          (j.1, completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ j.2) :=
      ⟨hij.1,
        completedGroupAlgebraComapIndexInClass_mono (G := G0) (H := H0) C hC ψ hij.2⟩
    have hx := x.2
      (i.1, completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ i.2)
      (j.1, completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ j.2)
      hsource
    change
      primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G0) C hsource
          (primePowerCompletedGroupAlgebraProjectionInClass
            (ℓ := ℓ) (G := G0) C
            (j.1, completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ j.2) x) =
        primePowerCompletedGroupAlgebraProjectionInClass
          (ℓ := ℓ) (G := G0) C
          (i.1, completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ i.2) x at hx
    have hcompat := congrFun
      (congrArg DFunLike.coe
        (primePowerCompletedGroupAlgebraMapStageInClass_compatible
          (ℓ := ℓ) C hC ψ hij))
      (primePowerCompletedGroupAlgebraProjectionInClass
        (ℓ := ℓ) (G := G0) C
        (j.1, completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ j.2) x)
    rw [RingHom.comp_apply, RingHom.comp_apply] at hcompat
    rw [hx] at hcompat
    change
      primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := H0) C hij
          ((primePowerCompletedGroupAlgebraMapStageInClass (ℓ := ℓ) C hC ψ j)
            (primePowerCompletedGroupAlgebraProjectionInClass
              (ℓ := ℓ) (G := G0) C
              (j.1, completedGroupAlgebraComapIndexInClass
                (G := G0) (H := H0) C hC ψ j.2) x)) =
        (primePowerCompletedGroupAlgebraMapStageInClass (ℓ := ℓ) C hC ψ i)
          (primePowerCompletedGroupAlgebraProjectionInClass
            (ℓ := ℓ) (G := G0) C
            (i.1, completedGroupAlgebraComapIndexInClass
              (G := G0) (H := H0) C hC ψ i.2) x)
    simpa using hcompat⟩
  map_zero' := by
    apply Subtype.ext
    funext i
    simp only [primePowerCompletedGroupAlgebraMapStageInClass,
      primePowerCompletedGroupAlgebraProjectionInClass_zero,
      MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_zero,
      coe_zero_primePowerCompletedGroupAlgebraInClass, Pi.zero_apply]
  map_add' := by
    intro x y
    apply Subtype.ext
    funext i
    simp only [primePowerCompletedGroupAlgebraProjectionInClass_add, map_add,
  coe_add_primePowerCompletedGroupAlgebraInClass, Pi.add_apply]

/--
The class-indexed prime-power completed group-algebra projection is computed by the
corresponding finite-stage map.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraProjectionInClass_map
    (C : ProCGroups.FiniteGroupClass.{u}) (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψ : ContinuousMonoidHom G0 H0) (i : PrimePowerCompletedGroupAlgebraIndexInClass H0 C)
    (x : PrimePowerCompletedGroupAlgebraInClass ℓ G0 C) :
    primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := H0) C i
        (primePowerCompletedGroupAlgebraMapInClass (ℓ := ℓ) C hC ψ x) =
      primePowerCompletedGroupAlgebraMapStageInClass (ℓ := ℓ) C hC ψ i
        (primePowerCompletedGroupAlgebraProjectionInClass
          (ℓ := ℓ) (G := G0) C
          (i.1, completedGroupAlgebraComapIndexInClass (G := G0) (H := H0) C hC ψ i.2) x) := rfl

end MapStageInClass
end

end FoxDifferential
