/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.BarResolutionNaturality
public import Nyll.GaloisCohomology.ProP.FiniteCyclicBarPeriodicCarryIdentity
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
public import Mathlib.RepresentationTheory.Equiv
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Low-degree bar--periodic chain comparison for finite cyclic groups

The generator prefixes and carry identity define the first four components of
a map from the bar resolution to the cyclic periodic resolution.  This file
verifies the chain squares through degree three and extends those components to
a full chain map.
-/

@[expose] public section

namespace ClassFieldTower.Cohomology

noncomputable section

open CategoryTheory Representation

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

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
  change Representation.freeLift (Rep.leftRegular R G).ρ
      (fun _ : Fin 0 → G => MonoidAlgebra.single (1 : G) (1 : R))
        (Finsupp.single x (MonoidAlgebra.single 1 1)) = _
  rw [Representation.freeLift_single_single, map_one, Module.End.one_apply, one_smul]

@[simp]
theorem finiteCyclicBarToPeriodicOne_generator
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x : Fin 1 → G) :
    (finiteCyclicBarToPeriodicOne (R := R) g hg).hom
        (Finsupp.single x (MonoidAlgebra.single 1 1)) =
      finiteCyclicGeneratorPrefix (R := R) g hg (x 0) := by
  change Representation.freeLift (Rep.leftRegular R G).ρ
      (fun y : Fin 1 → G => finiteCyclicGeneratorPrefix (R := R) g hg (y 0))
        (Finsupp.single x (MonoidAlgebra.single 1 1)) = _
  rw [Representation.freeLift_single_single, map_one, Module.End.one_apply, one_smul]

@[simp]
theorem finiteCyclicBarToPeriodicTwo_generator
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x : Fin 2 → G) :
    (finiteCyclicBarToPeriodicTwo (R := R) g hg).hom
        (Finsupp.single x (MonoidAlgebra.single 1 1)) =
      finiteCyclicCarry g hg (x 0) (x 1) • MonoidAlgebra.single 1 1 := by
  change Representation.freeLift (Rep.leftRegular R G).ρ
      (fun y : Fin 2 → G => finiteCyclicCarry g hg (y 0) (y 1) •
        MonoidAlgebra.single (1 : G) (1 : R))
        (Finsupp.single x (MonoidAlgebra.single 1 1)) = _
  rw [Representation.freeLift_single_single, map_one, Module.End.one_apply, one_smul]

@[simp]
theorem finiteCyclicBarToPeriodicThree_generator
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x : Fin 3 → G) :
    (finiteCyclicBarToPeriodicThree (R := R) g hg).hom
        (Finsupp.single x (MonoidAlgebra.single 1 1)) =
      finiteCyclicCarry g hg (x 1) (x 2) •
        finiteCyclicGeneratorPrefix (R := R) g hg (x 0) := by
  change Representation.freeLift (Rep.leftRegular R G).ρ
      (fun y : Fin 3 → G => finiteCyclicCarry g hg (y 1) (y 2) •
        finiteCyclicGeneratorPrefix (R := R) g hg (y 0))
        (Finsupp.single x (MonoidAlgebra.single 1 1)) = _
  rw [Representation.freeLift_single_single, map_one, Module.End.one_apply, one_smul]

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
  change _ = Representation.freeLift (Rep.leftRegular R G).ρ
    (fun _ : Fin 0 → G => MonoidAlgebra.single (1 : G) (1 : R)) _
  rw [Fin.sum_univ_one, map_add, Representation.freeLift_single_single,
    Representation.freeLift_single_single]
  rw [Representation.ofMulAction_single, Representation.ofMulAction_single]
  simp only [Fin.val_zero, Nat.zero_add, pow_one, smul_eq_mul, mul_one, one_smul,
    neg_one_smul, sub_eq_add_neg]

/-- The degree-two comparison square; the carry has positive sign. -/
theorem finiteCyclicBarToPeriodicTwo_comm
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    finiteCyclicBarToPeriodicTwo (R := R) g hg ≫ (Rep.leftRegular R G).norm.asHom =
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
  simp only [Fin.isValue, Nat.reduceAdd, map_add, Fin.sum_univ_three,
    finiteCyclicBarToPeriodicTwo, Rep.freeLift, Rep.hom_ofHom,
    Representation.freeLift_single_single, map_nsmul,
    Representation.ofMulAction_single, smul_eq_mul, mul_one]
  change
    finiteCyclicCarry g hg (x 1) (x 2) •
        (MonoidAlgebra.single (x 0) (1 : R) - MonoidAlgebra.single 1 1) =
      (1 : R) • (finiteCyclicCarry g hg (x 1) (x 2) •
        MonoidAlgebra.single (x 0) 1) +
        (((-1 : R) ^ 1) • (finiteCyclicCarry g hg (x 0 * x 1) (x 2) •
          MonoidAlgebra.single 1 1) +
          ((-1 : R) ^ 2) • (finiteCyclicCarry g hg (x 0) (x 1 * x 2) •
            MonoidAlgebra.single 1 1) +
          ((-1 : R) ^ 3) • (finiteCyclicCarry g hg (x 0) (x 1) •
            MonoidAlgebra.single 1 1))
  have hcR :
      (finiteCyclicCarry g hg (x 0 * x 1) (x 2) : R) +
          finiteCyclicCarry g hg (x 0) (x 1) =
        finiteCyclicCarry g hg (x 1) (x 2) +
          finiteCyclicCarry g hg (x 0) (x 1 * x 2) := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ ↦ (n : R))
      (finiteCyclicCarry_cocycle g hg (x 0) (x 1) (x 2))
  have hcAlg := congrArg (MonoidAlgebra.single (1 : G)) hcR
  simp only [MonoidAlgebra.single_add] at hcAlg
  simp only [pow_succ, pow_zero, one_mul, neg_one_mul, neg_neg, one_smul,
    neg_one_smul, nsmul_sub]
  simp only [MonoidAlgebra.smul_single]
  simp only [nsmul_eq_mul, mul_one]
  linear_combination hcAlg

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
    change
      ((Rep.trivial R G R).leftRegularHom 1).hom
          ((finiteCyclicBarToPeriodicZero (R := R) (G := G)).hom
            (Finsupp.single x (MonoidAlgebra.single 1 1))) =
        ((Rep.barResolution R G).π.f 0).hom
          (Finsupp.single x (MonoidAlgebra.single 1 1))
    rw [finiteCyclicBarToPeriodicZero_generator,
      Rep.barResolution_π_f_zero_generator, Rep.leftRegularHom_hom_single,
      Rep.trivial_ρ_apply, one_smul]

end

end ClassFieldTower.Cohomology
