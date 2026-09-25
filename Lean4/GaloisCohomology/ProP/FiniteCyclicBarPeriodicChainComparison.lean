/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.FiniteCyclicBarPeriodicCarryIdentity
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

set_option autoImplicit false
/-!
# Low-degree bar--periodic chain comparison for finite cyclic groups

The generator prefixes and carry identity define the first four components of
a map from the bar resolution to the cyclic periodic resolution.  This file
verifies the chain squares through degree three and extends those components to
a full chain map.
-/

namespace ClassFieldTower.Cohomology

noncomputable section

open CategoryTheory Representation

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- Powers of a specified cyclic generator enumerate the group. -/
noncomputable def finiteCyclicGeneratorPowEquiv
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) : Fin (Nat.card G) ≃ G where
  toFun i := g ^ i.val
  invFun x := ⟨(finiteCyclicGeneratorCoordinate g hg x).val, ZMod.val_lt _⟩
  left_inv i := by
    apply Fin.ext
    change (finiteCyclicGeneratorCoordinate g hg (g ^ i.val)).val = i.val
    rw [finiteCyclicGeneratorCoordinate_pow]
    exact ZMod.val_natCast_of_lt i.isLt
  right_inv x := finiteCyclicGenerator_zpow_coordinate g hg x

/-- The full generator prefix is the norm of the unit basis vector. -/
theorem finiteCyclicPrefixNat_card_eq_norm_one
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    finiteCyclicPrefixNat (R := R) g (Nat.card G) =
      (Rep.leftRegular R G).norm.hom (MonoidAlgebra.single 1 1) := by
  rw [finiteCyclicPrefixNat, ← Fin.sum_univ_eq_sum_range]
  calc
    ∑ i : Fin (Nat.card G), MonoidAlgebra.single (g ^ i.val) (1 : R) =
        ∑ x : G, MonoidAlgebra.single x (1 : R) :=
      Equiv.sum_comp (finiteCyclicGeneratorPowEquiv g hg)
        (fun x : G ↦ MonoidAlgebra.single x (1 : R))
    _ = _ := by
      rw [Rep.norm_apply, Representation.norm, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro x _
      simp

omit [Fintype G] in
/-- Degree zero of the explicit map from the bar resolution to the periodic resolution. -/
noncomputable def finiteCyclicBarToPeriodicZero :
    Rep.free R G (Fin 0 → G) ⟶ Rep.leftRegular R G :=
  Rep.freeLift R G (Rep.leftRegular R G)
    (fun _ ↦ MonoidAlgebra.single 1 1)

/-- Degree one of the explicit bar--periodic map. -/
noncomputable def finiteCyclicBarToPeriodicOne
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Rep.free R G (Fin 1 → G) ⟶ Rep.leftRegular R G :=
  Rep.freeLift R G (Rep.leftRegular R G)
    (fun x ↦ finiteCyclicGeneratorPrefix (R := R) g hg (x 0))

/-- Degree two of the explicit bar--periodic map is the positive carry. -/
noncomputable def finiteCyclicBarToPeriodicTwo
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Rep.free R G (Fin 2 → G) ⟶ Rep.leftRegular R G :=
  Rep.freeLift R G (Rep.leftRegular R G)
    (fun x ↦ finiteCyclicCarry g hg (x 0) (x 1) •
      MonoidAlgebra.single 1 1)

/-- Degree three of the explicit bar--periodic map. -/
noncomputable def finiteCyclicBarToPeriodicThree
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Rep.free R G (Fin 3 → G) ⟶ Rep.leftRegular R G :=
  Rep.freeLift R G (Rep.leftRegular R G)
    (fun x ↦ finiteCyclicCarry g hg (x 1) (x 2) •
      finiteCyclicGeneratorPrefix (R := R) g hg (x 0))

omit [Fintype G] in
@[simp]
theorem finiteCyclicBarToPeriodicZero_generator (x : Fin 0 → G) :
    (finiteCyclicBarToPeriodicZero (R := R) (G := G)).hom
        (Finsupp.single x (MonoidAlgebra.single 1 1)) =
      MonoidAlgebra.single 1 1 := by
  simp [finiteCyclicBarToPeriodicZero]

@[simp]
theorem finiteCyclicBarToPeriodicOne_generator
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x : Fin 1 → G) :
    (finiteCyclicBarToPeriodicOne (R := R) g hg).hom
        (Finsupp.single x (MonoidAlgebra.single 1 1)) =
      finiteCyclicGeneratorPrefix (R := R) g hg (x 0) := by
  simp [finiteCyclicBarToPeriodicOne]

@[simp]
theorem finiteCyclicBarToPeriodicTwo_generator
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x : Fin 2 → G) :
    (finiteCyclicBarToPeriodicTwo (R := R) g hg).hom
        (Finsupp.single x (MonoidAlgebra.single 1 1)) =
      finiteCyclicCarry g hg (x 0) (x 1) • MonoidAlgebra.single 1 1 := by
  simp [finiteCyclicBarToPeriodicTwo]

@[simp]
theorem finiteCyclicBarToPeriodicThree_generator
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x : Fin 3 → G) :
    (finiteCyclicBarToPeriodicThree (R := R) g hg).hom
        (Finsupp.single x (MonoidAlgebra.single 1 1)) =
      finiteCyclicCarry g hg (x 1) (x 2) •
        finiteCyclicGeneratorPrefix (R := R) g hg (x 0) := by
  simp [finiteCyclicBarToPeriodicThree]

/-- The degree-one comparison square. -/
theorem finiteCyclicBarToPeriodicOne_comm
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    finiteCyclicBarToPeriodicOne (R := R) g hg ≫
        (Rep.applyAsHom (Rep.leftRegular R G) g - 𝟙 (Rep.leftRegular R G)) =
      Rep.barComplex.d R G 0 ≫ finiteCyclicBarToPeriodicZero (R := R) (G := G) := by
  apply Rep.free_ext R G (Rep.leftRegular R G)
  intro x
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rw [Rep.barComplex.d_single, finiteCyclicBarToPeriodicOne_generator]
  change
    (Rep.leftRegular R G).ρ g
          (finiteCyclicGeneratorPrefix (R := R) g hg (x 0)) -
        finiteCyclicGeneratorPrefix (R := R) g hg (x 0) = _
  rw [finiteCyclicGeneratorPrefix_sub]
  simp [finiteCyclicBarToPeriodicZero, sub_eq_add_neg]

/-- The degree-two comparison square; the carry has positive sign. -/
theorem finiteCyclicBarToPeriodicTwo_comm
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    finiteCyclicBarToPeriodicTwo (R := R) g hg ≫ (Rep.leftRegular R G).norm =
      Rep.barComplex.d R G 1 ≫ finiteCyclicBarToPeriodicOne (R := R) g hg := by
  apply Rep.free_ext R G (Rep.leftRegular R G)
  intro x
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rw [Rep.barComplex.d_single, finiteCyclicBarToPeriodicTwo_generator]
  simp only [map_nsmul]
  rw [← finiteCyclicPrefixNat_card_eq_norm_one (R := R) g hg]
  simpa [finiteCyclicBarToPeriodicOne, Fin.sum_univ_two, Fin.contractNth,
    Nat.card_eq_fintype_card, sub_eq_add_neg, add_assoc] using
    (finiteCyclicGeneratorPrefix_carry (R := R) g hg (x 0) (x 1)).symm

/-- The degree-three comparison square follows from the carry cocycle law. -/
theorem finiteCyclicBarToPeriodicThree_comm
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    finiteCyclicBarToPeriodicThree (R := R) g hg ≫
        (Rep.applyAsHom (Rep.leftRegular R G) g - 𝟙 (Rep.leftRegular R G)) =
      Rep.barComplex.d R G 2 ≫ finiteCyclicBarToPeriodicTwo (R := R) g hg := by
  apply Rep.free_ext R G (Rep.leftRegular R G)
  intro x
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rw [Rep.barComplex.d_single, finiteCyclicBarToPeriodicThree_generator]
  change
    (Rep.leftRegular R G).ρ g
          (finiteCyclicCarry g hg (x 1) (x 2) •
            finiteCyclicGeneratorPrefix (R := R) g hg (x 0)) -
        finiteCyclicCarry g hg (x 1) (x 2) •
          finiteCyclicGeneratorPrefix (R := R) g hg (x 0) = _
  rw [map_nsmul, ← nsmul_sub, finiteCyclicGeneratorPrefix_sub]
  simp [finiteCyclicBarToPeriodicTwo, Fin.sum_univ_three, Fin.contractNth,
    sub_eq_add_neg, add_assoc]
  have hcR :
      (finiteCyclicCarry g hg (x 0 * x 1) (x 2) : R) +
          finiteCyclicCarry g hg (x 0) (x 1) =
        finiteCyclicCarry g hg (x 1) (x 2) +
          finiteCyclicCarry g hg (x 0) (x 1 * x 2) := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ ↦ (n : R))
      (finiteCyclicCarry_cocycle g hg (x 0) (x 1) (x 2))
  ext z
  by_cases hz : z = 1
  · subst z
    simp
    linear_combination hcR
  · simp [hz]

/-- Inductive data extending the explicit degree-zero through degree-three
components to every degree. -/
noncomputable def finiteCyclicBarToPeriodicAux
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    ∀ n : ℕ,
      Σ' (f :
          (Rep.barResolution R G).complex.X n ⟶
            (Rep.FiniteCyclicGroup.resolution R g hg).complex.X n)
        (f' :
          (Rep.barResolution R G).complex.X (n + 1) ⟶
            (Rep.FiniteCyclicGroup.resolution R g hg).complex.X (n + 1)),
        f' ≫ (Rep.FiniteCyclicGroup.resolution R g hg).complex.d (n + 1) n =
          (Rep.barResolution R G).complex.d (n + 1) n ≫ f
  | 0 => ⟨finiteCyclicBarToPeriodicZero (R := R) (G := G),
      finiteCyclicBarToPeriodicOne (R := R) g hg,
      finiteCyclicBarToPeriodicOne_comm (R := R) g hg⟩
  | 1 => ⟨finiteCyclicBarToPeriodicOne (R := R) g hg,
      finiteCyclicBarToPeriodicTwo (R := R) g hg,
      finiteCyclicBarToPeriodicTwo_comm (R := R) g hg⟩
  | 2 => ⟨finiteCyclicBarToPeriodicTwo (R := R) g hg,
      finiteCyclicBarToPeriodicThree (R := R) g hg,
      finiteCyclicBarToPeriodicThree_comm (R := R) g hg⟩
  | n + 3 =>
      let p := finiteCyclicBarToPeriodicAux g hg (n + 2)
      let q := ProjectiveResolution.liftFSucc
        (Rep.barResolution R G)
        (Rep.FiniteCyclicGroup.resolution R g hg) (n + 2)
        p.1 p.2.1 p.2.2
      ⟨p.2.1, q.1, q.2⟩

theorem finiteCyclicBarToPeriodicAux_succ
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (n : ℕ) :
    (finiteCyclicBarToPeriodicAux (R := R) g hg (n + 1)).1 =
      (finiteCyclicBarToPeriodicAux (R := R) g hg n).2.1 := by
  cases n with
  | zero => rfl
  | succ n =>
      cases n with
      | zero => rfl
      | succ n => rfl

/-- The full bar-to-periodic chain map with the carry as its degree-two
component.  Only degrees at least four use an abstract projective lift. -/
noncomputable def finiteCyclicBarToPeriodicComparison
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Rep.barComplex R G ⟶
      (Rep.FiniteCyclicGroup.resolution R g hg).complex where
  f n := (finiteCyclicBarToPeriodicAux (R := R) g hg n).1
  comm' n m := by
    rintro (rfl : m + 1 = n)
    rw [finiteCyclicBarToPeriodicAux_succ]
    exact (finiteCyclicBarToPeriodicAux (R := R) g hg m).2.2

@[simp]
theorem finiteCyclicBarToPeriodicComparison_f_zero
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    (finiteCyclicBarToPeriodicComparison (R := R) g hg).f 0 =
      finiteCyclicBarToPeriodicZero (R := R) (G := G) := rfl

@[simp]
theorem finiteCyclicBarToPeriodicComparison_f_one
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    (finiteCyclicBarToPeriodicComparison (R := R) g hg).f 1 =
      finiteCyclicBarToPeriodicOne (R := R) g hg := rfl

@[simp]
theorem finiteCyclicBarToPeriodicComparison_f_two
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    (finiteCyclicBarToPeriodicComparison (R := R) g hg).f 2 =
      finiteCyclicBarToPeriodicTwo (R := R) g hg := rfl

@[simp]
theorem finiteCyclicBarToPeriodicComparison_f_three
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    (finiteCyclicBarToPeriodicComparison (R := R) g hg).f 3 =
      finiteCyclicBarToPeriodicThree (R := R) g hg := rfl

/-- The explicit comparison, regarded as a morphism of projective resolutions
lifting the identity of the trivial representation. -/
noncomputable def finiteCyclicBarToPeriodicResolutionHom
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    ProjectiveResolution.Hom
      (Rep.barResolution R G)
      (Rep.FiniteCyclicGroup.resolution R g hg) (𝟙 _) where
  hom := finiteCyclicBarToPeriodicComparison (R := R) g hg
  hom_f_zero_comp_π_f_zero := by
    apply Rep.free_ext R G (Rep.trivial R G R)
    intro x
    let h : G := 1
    have H :
        (Rep.diagonalSuccIsoFree R G 0).inv.hom
            (Finsupp.single x (MonoidAlgebra.single h 1)) =
          MonoidAlgebra.single (h • Fin.partialProd x) (1 : R) := by
      simp only [Rep.diagonalSuccIsoFree, Rep.diagonalSuccIsoTensorTrivial,
        Iso.trans_inv, Rep.hom_comp,
        Representation.IntertwiningMap.comp_apply]
      have step1 :
          (Rep.Hom.hom
              (Rep.leftRegularTensorTrivialIsoFree R G (Fin 0 → G)).inv)
              (Finsupp.single x (MonoidAlgebra.single h 1)) =
            MonoidAlgebra.single h 1 ⊗ₜ[R] MonoidAlgebra.single x 1 :=
        Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single
          x h 1
      rw [step1]
      have key₁ := Representation.linearizeMap_single (k := R)
        (Action.diagonalSuccIsoTensorTrivial G 0).inv (h, x)
          ((1 : R) * 1)
      have key₂ :=
        Representation.LinearizeMonoidal.μ_apply_single_single (k := R)
          (X := Action.leftRegular G)
          (Y := Action.trivial G (Fin 0 → G)) h x 1 1
      exact ((congrArg (fun z ↦
        Representation.linearizeMap
          (Action.diagonalSuccIsoTensorTrivial G 0).inv z) key₂).trans
            key₁).trans (by
              congr 1
              · exact Action.diagonalSuccIsoTensorTrivial_inv_hom_apply h x
              · simp)
    change
      ((Rep.trivial R G R).leftRegularHom 1).hom
          ((finiteCyclicBarToPeriodicZero (R := R) (G := G)).hom
            (Finsupp.single x (MonoidAlgebra.single 1 1))) =
        (Rep.standardComplex.ε R G).hom
          ((Rep.diagonalSuccIsoFree R G 0).inv.hom
            (Finsupp.single x (MonoidAlgebra.single 1 1)))
    rw [finiteCyclicBarToPeriodicZero_generator]
    rw [show (1 : G) = h by simp [h], H]
    simp [Rep.standardComplex.ε, h]

end

end ClassFieldTower.Cohomology
