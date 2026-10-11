/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.DifferentialModule.Map.Comap

/-!
# Fox differential: completed — differential module — map — stage

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraMapStage`
  The finite-stage prime-power group-algebra map induced by the quotient map associated to `ψ` and
  `i`.
- `primePowerCompletedGroupAlgebraMapStage_of`
  The finite-stage prime-power map sends a group-like basis element to the basis element supported
  at its quotient image.
- `primePowerCompletedGroupAlgebraMapStage_single`
  The finite-stage component of the completed group-algebra map sends arbitrary group-ring basis
  coefficients by the pulled-back quotient map.
- `primePowerCompletedGroupAlgebraMapStage_surjective`
  If \(\psi : G \to H\) is surjective, then every finite-stage group-algebra component of the
  completed map is surjective.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The finite-stage prime-power group-algebra map induced by the quotient map associated to `ψ` and
`i`.
-/
def primePowerCompletedGroupAlgebraMapStage
    (ψ : ContinuousMonoidHom G H) (i : PrimePowerCompletedGroupAlgebraIndex H) :
    PrimePowerCompletedGroupAlgebraStage ℓ G
        (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) →+*
      PrimePowerCompletedGroupAlgebraStage ℓ H i :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff (ℓ ^ i.1))
    (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ i.2)

/--
The finite-stage prime-power map sends a group-like basis element to the basis element supported at
its quotient image.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraMapStage_of
    (ψ : ContinuousMonoidHom G H) (i : PrimePowerCompletedGroupAlgebraIndex H)
    (q : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G
      (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)) :
    primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1)) _ q) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1)) _
        (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ i.2 q) := by
  change
    MonoidAlgebra.mapDomain
        (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ i.2)
        (MonoidAlgebra.single q 1) =
      MonoidAlgebra.single
        (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ i.2 q) 1
  exact MonoidAlgebra.mapDomain_single


/--
The finite-stage component of the completed group-algebra map sends arbitrary group-ring basis
coefficients by the pulled-back quotient map.
-/
theorem primePowerCompletedGroupAlgebraMapStage_single
    (ψ : ContinuousMonoidHom G H) (i : PrimePowerCompletedGroupAlgebraIndex H)
    (q : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G
      (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2))
    (a : ModNCompletedCoeff (ℓ ^ i.1)) :
    primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single
        (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ i.2 q) a := by
  change
    MonoidAlgebra.mapDomain
        (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ i.2)
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single
        (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ i.2 q) a
  exact MonoidAlgebra.mapDomain_single

/--
If \(\psi : G \to H\) is surjective, then every finite-stage group-algebra component of the
completed map is surjective.
-/
theorem primePowerCompletedGroupAlgebraMapStage_surjective
    (ψ : ContinuousMonoidHom G H) (hψ : Function.Surjective ψ)
    (i : PrimePowerCompletedGroupAlgebraIndex H) :
    Function.Surjective
      (primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i) := by
  intro x
  refine MonoidAlgebra.induction_linear
    (motive := fun x : PrimePowerCompletedGroupAlgebraStage ℓ H i =>
      ∃ y, primePowerCompletedGroupAlgebraMapStage
          (ℓ := ℓ) (G := G) (H := H) ψ i y = x)
    x ?_ ?_ ?_
  · exact ⟨0, map_zero _⟩
  · rintro x y ⟨x', hx'⟩ ⟨y', hy'⟩
    refine ⟨x' + y', ?_⟩
    rw [map_add, hx', hy']
  · intro q a
    rcases completedGroupAlgebraComapQuotientMap_surjective
        (G := G) (H := H) ψ hψ i.2 q with
      ⟨q', hq'⟩
    refine ⟨MonoidAlgebra.single q' a, ?_⟩
    rw [primePowerCompletedGroupAlgebraMapStage_single, hq']

/-- The finite-stage component of a completed group-algebra map preserves augmentation. -/
theorem primePowerCompletedGroupAlgebraMapStage_augmentation
    (ψ : ContinuousMonoidHom G H) (i : PrimePowerCompletedGroupAlgebraIndex H)
    (x : PrimePowerCompletedGroupAlgebraStage ℓ G
      (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)) :
    modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) H i.2
        (primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i x) =
      modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G
        (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) x := by
  let leftMap :
      PrimePowerCompletedGroupAlgebraStage ℓ G
          (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) →+*
        ModNCompletedCoeff (ℓ ^ i.1) :=
    (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) H i.2).comp
      (primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i)
  let rightMap :
      PrimePowerCompletedGroupAlgebraStage ℓ G
          (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) →+*
        ModNCompletedCoeff (ℓ ^ i.1) :=
    modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G
      (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)
  change leftMap x = rightMap x
  have hmaps : leftMap = rightMap := by
    apply MonoidAlgebra.ringHom_ext
    · intro r
      rcases ZMod.intCast_surjective r with ⟨t, rfl⟩
      change leftMap
          ((algebraMap (ModNCompletedCoeff (ℓ ^ i.1))
            (PrimePowerCompletedGroupAlgebraStage ℓ G
              (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)))
            (t : ModNCompletedCoeff (ℓ ^ i.1))) =
        rightMap
          ((algebraMap (ModNCompletedCoeff (ℓ ^ i.1))
            (PrimePowerCompletedGroupAlgebraStage ℓ G
              (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)))
            (t : ModNCompletedCoeff (ℓ ^ i.1)))
      simp only [map_intCast]
    · intro q
      dsimp [leftMap, rightMap]
      rw [primePowerCompletedGroupAlgebraMapStage_single]
      have hleft :
          modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) H i.2
              (MonoidAlgebra.single
                (completedGroupAlgebraComapQuotientMap
                  (G := G) (H := H) ψ i.2 q) 1) = 1 := by
        simpa only [MonoidAlgebra.of_apply] using
          modNCompletedGroupAlgebraStageAugmentation_of
            (n := ℓ ^ i.1) (G := H) i.2
            (completedGroupAlgebraComapQuotientMap
              (G := G) (H := H) ψ i.2 q)
      have hright :
          modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G
              (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)
              (MonoidAlgebra.single q 1) = 1 := by
        simpa only [MonoidAlgebra.of_apply] using
          modNCompletedGroupAlgebraStageAugmentation_of
            (n := ℓ ^ i.1) (G := G)
            (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) q
      rw [hleft, hright]
  rw [hmaps]

/--
The finite-stage prime-power maps commute with transition maps between refined target indices.
-/
theorem primePowerCompletedGroupAlgebraMapStage_compatible
    (ψ : ContinuousMonoidHom G H) {i j : PrimePowerCompletedGroupAlgebraIndex H} (hij : i ≤ j) :
    (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := H) hij).comp
        (primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ j) =
      (primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i).comp
        (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G)
          (show
            (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) ≤
              (j.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ j.2) from
            ⟨hij.1, completedGroupAlgebraComapIndex_mono (G := G) (H := H) ψ hij.2⟩)) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      ((primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := H) hij).comp
          (primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ j)) x =
        ((primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i).comp
          (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G)
            (show
              (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) ≤
                (j.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ j.2) from
              ⟨hij.1,
                completedGroupAlgebraComapIndex_mono (G := G) (H := H) ψ hij.2⟩))) x)
    x ?_ ?_ ?_
  · intro q
    rw [RingHom.comp_apply, RingHom.comp_apply,
      primePowerCompletedGroupAlgebraMapStage_of,
      primePowerCompletedGroupAlgebraTransition_of,
      primePowerCompletedGroupAlgebraTransition_of]
    change
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1))
          (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2)
          ((OpenNormalSubgroupInClass.map
            (C := ProCGroups.FiniteGroupClass.allFinite) (G := H)
            (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2)
            (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ j.2 q)) =
        primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1))
            (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G
              (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2))
            ((OpenNormalSubgroupInClass.map
              (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
              (U := OrderDual.ofDual
                (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2))
              (V := OrderDual.ofDual
                (completedGroupAlgebraComapIndex (G := G) (H := H) ψ j.2))
              (completedGroupAlgebraComapIndex_mono (G := G) (H := H) ψ hij.2)) q))
    erw [primePowerCompletedGroupAlgebraMapStage_of]
    exact congrArg (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1))
      (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2))
      (congrFun
        (congrArg DFunLike.coe
          (completedGroupAlgebraComapQuotientMap_compatible
            (G := G) (H := H) ψ hij.2)) q)
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    simp only [primePowerCompletedGroupAlgebraTransition, modNCompletedGroupAlgebraStageCoeffMap,
  modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe,
      primePowerCompletedGroupAlgebraMapStage, map_intCast,
  RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, MonoidAlgebra.mapDomainRingHom_apply]

end

end FoxDifferential
