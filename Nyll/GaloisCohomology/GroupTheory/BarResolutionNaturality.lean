/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.CategoryTheory.Action.Monoidal
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Equiv
public import Mathlib.RepresentationTheory.Homological.Resolution
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.RepresentationTheory.Rep.Res

/-!
# The actual bar resolution under a group map

The map sends each free generator indexed by a tuple to the tuple obtained from the given
group homomorphism. It retains the same coefficient, differentials and augmentation. For a
subgroup this gives a specified comparison with the restricted ambient bar resolution, which
is the comparison required to identify native Shapiro with evaluation of actual cochains.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace Rep

variable (R : Type u) [CommRing R] {G H : Type u} [Group G] [Group H]
  (φ : G →* H)

/-- The actual tuple map between free terms of the bar resolutions. -/
def barMapComponent (n : ℕ) :
    free R G (Fin n → G) ⟶ res φ (free R H (Fin n → H)) :=
  freeLift R G _ (fun x =>
    Finsupp.single (φ ∘ x) (MonoidAlgebra.single (1 : H) (1 : R)))

/-- The free tuple map preserves its coefficient and applies the given group homomorphism. -/
theorem barMapComponent_single_single (n : ℕ) (x : Fin n → G) (g : G) (r : R) :
    (barMapComponent R φ n).hom (Finsupp.single x (MonoidAlgebra.single g r)) =
      Finsupp.single (φ ∘ x) (MonoidAlgebra.single (φ g) r) := by
  change Representation.freeLift (res φ (free R H (Fin n → H))).ρ
      (fun y => Finsupp.single (φ ∘ y) (MonoidAlgebra.single (1 : H) (1 : R)))
        (Finsupp.single x (MonoidAlgebra.single g r)) = _
  rw [Representation.freeLift_single_single]
  change r • Representation.free R H (Fin n → H) (φ g)
      (Finsupp.single (φ ∘ x) (MonoidAlgebra.single (1 : H) (1 : R))) = _
  rw [Representation.free_single_single, mul_one, Finsupp.smul_single,
    MonoidAlgebra.smul_single', mul_one]

/-- The named free generator is sent to the generator of its actual image tuple. -/
theorem barMapComponent_generator (n : ℕ) (x : Fin n → G) :
    (barMapComponent R φ n).hom (Finsupp.single x (MonoidAlgebra.single 1 1)) =
      Finsupp.single (φ ∘ x) (MonoidAlgebra.single 1 1) := by
  rw [barMapComponent_single_single, map_one]

/-- Tuple transport commutes with the original bar differential, including its signs. -/
theorem barMapComponent_comm (n : ℕ) :
    barMapComponent R φ (n + 1) ≫ (resFunctor φ).map (barComplex.d R H n) =
      barComplex.d R G n ≫ barMapComponent R φ n := by
  apply free_ext R G (res φ (free R H (Fin n → H)))
  intro x
  change (barComplex.d R H n).hom
      ((barMapComponent R φ (n + 1)).hom
        (Finsupp.single x (MonoidAlgebra.single 1 1))) =
    (barMapComponent R φ n).hom
      ((barComplex.d R G n).hom (Finsupp.single x (MonoidAlgebra.single 1 1)))
  rw [barMapComponent_generator, barComplex.d_single, barComplex.d_single,
    map_add, map_sum, barMapComponent_single_single]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro j _hj
  rw [barMapComponent_single_single, map_one]
  exact congrArg (fun y => Finsupp.single y
    (MonoidAlgebra.single (1 : H) ((-1 : R) ^ ((j : ℕ) + 1))))
      (Fin.comp_contractNth (· * ·) (· * ·) φ.map_mul j x).symm

/-- The actual chain map from a group's bar complex to the restricted target bar complex. -/
def barMap : barComplex R G ⟶
    ((resFunctor φ).mapHomologicalComplex (.down ℕ)).obj (barComplex R H) where
  f n := barMapComponent R φ n
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    change barMapComponent R φ (j + 1) ≫
        (resFunctor φ).map ((barComplex R H).d (j + 1) j) =
      (barComplex R G).d (j + 1) j ≫ barMapComponent R φ j
    rw [barComplex.d_def, barComplex.d_def]
    exact barMapComponent_comm R φ j

/-- The chain map has the same explicit free-generator component in every degree. -/
theorem barMap_f (n : ℕ) : (barMap R φ).f n = barMapComponent R φ n := rfl

variable (G) in
/-- The existing bar augmentation sends each degree-zero free generator to one. -/
theorem barResolution_π_f_zero_generator (x : Fin 0 → G) :
    ((barResolution R G).π.f 0).hom
      (Finsupp.single x (MonoidAlgebra.single (1 : G) (1 : R))) = (1 : R) := by
  have h : (diagonalSuccIsoFree R G 0).inv.hom
      (Finsupp.single x (MonoidAlgebra.single (1 : G) (1 : R))) =
    MonoidAlgebra.single ((1 : G) • Fin.partialProd x) (1 : R) := by
    simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv,
      Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
    have step : (Rep.Hom.hom (leftRegularTensorTrivialIsoFree R G (Fin 0 → G)).inv)
        (Finsupp.single x (MonoidAlgebra.single (1 : G) (1 : R))) =
      MonoidAlgebra.single (1 : G) (1 : R) ⊗ₜ[R] MonoidAlgebra.single x (1 : R) :=
      Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single x 1 1
    rw [step]
    have h₁ := Representation.linearizeMap_single (k := R)
      (Action.diagonalSuccIsoTensorTrivial G 0).inv ((1 : G), x) ((1 : R) * 1)
    have h₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := R)
      (X := Action.leftRegular G) (Y := Action.trivial G (Fin 0 → G)) (1 : G) x 1 1
    exact ((congrArg (fun z => Representation.linearizeMap
      (Action.diagonalSuccIsoTensorTrivial G 0).inv z) h₂).trans h₁).trans
        (congrArg₂ (fun (y : Fin 1 → G) (r : R) => MonoidAlgebra.single y r)
          (Action.diagonalSuccIsoTensorTrivial_inv_hom_apply (1 : G) x) (mul_one (1 : R)))
  change (standardComplex.ε R G).hom
    ((diagonalSuccIsoFree R G 0).inv.hom
      (Finsupp.single x (MonoidAlgebra.single (1 : G) (1 : R)))) = 1
  rw [h]
  change Finsupp.linearCombination R (fun _ : Fin 1 → G => (1 : R))
    (Finsupp.single ((1 : G) • Fin.partialProd x) (1 : R)) = 1
  rw [Finsupp.linearCombination_single, one_smul]

variable (G) in
/-- The explicit subgroup tuple map lifts the identity of the same trivial representation. -/
def barRestrictionResolutionHom (S : Subgroup G) :
    ProjectiveResolution.Hom (barResolution R S)
      ((resFunctor S.subtype).mapProjectiveResolution (barResolution R G)) (𝟙 _) where
  hom := barMap R S.subtype
  hom_f_zero_comp_π_f_zero := by
    apply free_ext R S (trivial R S R)
    intro x
    change ((barResolution R G).π.f 0).hom
        ((barMapComponent R S.subtype 0).hom
          (Finsupp.single x (MonoidAlgebra.single (1 : S) (1 : R)))) =
      ((barResolution R S).π.f 0).hom
        (Finsupp.single x (MonoidAlgebra.single (1 : S) (1 : R)))
    exact (congrArg (((barResolution R G).π.f 0).hom)
      (barMapComponent_generator R S.subtype 0 x)).trans
        ((barResolution_π_f_zero_generator R G (S.subtype ∘ x)).trans
          (barResolution_π_f_zero_generator R S x).symm)

end Rep
