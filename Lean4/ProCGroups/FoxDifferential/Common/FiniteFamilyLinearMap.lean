import Mathlib.Algebra.Exact.Basic

set_option autoImplicit false

/-!
# Fox differential: common — finite family linear map

The principal declarations in this module are:

- `finiteFamilyLinearMap`
  The linear map represented by a finite family of target vectors.
- `piReindexLinearEquiv`
  Reindex finite coordinate functions by an equivalence of index types.
- `finiteFamilyLinearMap_apply`
  The linear map represented by `generators` evaluates a coordinate vector as the finite sum `∑ i, x
  i • generators i`.
- `finiteFamilyLinearMap_single`
  A finite-family linear map sends a coordinate basis vector to the corresponding generator.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

section FiniteFamilyLinearMap

variable {R : Type*} [Semiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The linear map represented by a finite family of target vectors. -/
def finiteFamilyLinearMap (generators : X → M) :
    (X → R) →ₗ[R] M where
  toFun x := ∑ i, x i • generators i
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

omit [DecidableEq X] in
/--
The linear map represented by `generators` evaluates a coordinate vector as the finite sum `∑ i, x i
• generators i`.
-/
theorem finiteFamilyLinearMap_apply (generators : X → M) (x : X → R) :
    finiteFamilyLinearMap (R := R) generators x = ∑ i, x i • generators i := rfl

/-- A finite-family linear map sends a coordinate basis vector to the corresponding generator. -/
@[simp 900]
theorem finiteFamilyLinearMap_single (generators : X → M) (i : X) :
    finiteFamilyLinearMap (R := R) generators (Pi.single i 1) = generators i := by
  rw [finiteFamilyLinearMap_apply]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, one_smul]
  · intro j _ hji
    simp only [ne_eq, hji, not_false_eq_true, Pi.single_eq_of_ne, zero_smul]
  · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, one_smul, IsEmpty.forall_iff]

section Reindex

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- Reindex finite coordinate functions by an equivalence of index types. -/
def piReindexLinearEquiv (e : X ≃ Y) :
    (X → R) ≃ₗ[R] (Y → R) where
  toFun f := fun y => f (e.symm y)
  invFun f := fun x => f (e x)
  left_inv := by
    intro f
    funext x
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    intro f
    funext y
    simp only [Equiv.apply_symm_apply]
  map_add' := by
    intro f g
    funext y
    simp only [Pi.add_apply]
  map_smul' := by
    intro a f
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

omit [DecidableEq X] [DecidableEq Y] in
/-- Finite-family linear maps are invariant under reindexing of their finite coordinate type. -/
theorem finiteFamilyLinearMap_reindex
    (e : X ≃ Y) (generators : Y → M) :
    finiteFamilyLinearMap (R := R) (fun x : X => generators (e x)) =
      (finiteFamilyLinearMap (R := R) generators).comp
        (piReindexLinearEquiv (R := R) e).toLinearMap := by
  apply LinearMap.ext
  intro f
  rw [finiteFamilyLinearMap_apply, LinearMap.comp_apply, finiteFamilyLinearMap_apply]
  exact
    Fintype.sum_equiv e
      (fun x : X => f x • generators (e x))
      (fun y : Y => f (e.symm y) • generators y)
      (by intro x; simp only [Equiv.symm_apply_apply])

end Reindex

/--
A coordinate map sending a finite generating family to the standard basis is a left inverse to
the corresponding finite-family linear map.
-/
theorem finiteFamilyLinearMap_leftInverse_of_mapsToSingle
    (generators : X → M) (coordinateMap : M →ₗ[R] (X → R))
    (hcoord : ∀ i : X, coordinateMap (generators i) = Pi.single i 1) :
    coordinateMap.comp (finiteFamilyLinearMap (R := R) generators) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  funext k
  rw [LinearMap.comp_apply, finiteFamilyLinearMap_apply, LinearMap.id_apply]
  calc
    coordinateMap (∑ i, x i • generators i) k =
        (∑ i, x i • coordinateMap (generators i)) k := by
          rw [map_sum, Finset.sum_apply, Finset.sum_apply]
          apply Finset.sum_congr rfl
          intro i hi
          simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    _ = (∑ i, x i • (Pi.single i (1 : R) : X → R)) k := by
          rw [Finset.sum_apply, Finset.sum_apply]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hcoord i]
    _ = x k := by
          rw [Finset.sum_apply, Finset.sum_eq_single k]
          · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
          · intro i _ hik
            simp only [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hik), smul_eq_mul, mul_zero]
          · simp only [Finset.mem_univ, not_true_eq_false, Pi.smul_apply, Pi.single_eq_same,
              smul_eq_mul, mul_one,
  IsEmpty.forall_iff]

omit [DecidableEq X] in
/--
The image of a finite-family linear map is exactly the submodule spanned by its target family.
-/
theorem finiteFamilyLinearMap_range_eq_span (generators : X → M) :
    LinearMap.range (finiteFamilyLinearMap (R := R) generators) =
      Submodule.span R (Set.range generators) := by
  classical
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    rw [finiteFamilyLinearMap_apply]
    exact Submodule.sum_mem _ fun i _ =>
      (Submodule.span R (Set.range generators)).smul_mem (x i)
        (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro y ⟨i, rfl⟩
    exact ⟨Pi.single i 1, finiteFamilyLinearMap_single (R := R) generators i⟩

omit [DecidableEq X] in
/-- A finite-family linear map is surjective when its target family spans the codomain. -/
theorem finiteFamilyLinearMap_surjective_of_span_eq_top
    (generators : X → M)
    (hspan : Submodule.span R (Set.range generators) = ⊤) :
    Function.Surjective (finiteFamilyLinearMap (R := R) generators) := by
  apply (LinearMap.range_eq_top).1
  rw [finiteFamilyLinearMap_range_eq_span, hspan]

omit [DecidableEq X] in
/-- Surjectivity of a finite-family map is exactly the statement that the target family spans. -/
theorem finiteFamilyLinearMap_surjective_iff_span_eq_top
    {generators : X → M} :
    Function.Surjective (finiteFamilyLinearMap (R := R) generators) ↔
      Submodule.span R (Set.range generators) = ⊤ := by
  rw [← LinearMap.range_eq_top, finiteFamilyLinearMap_range_eq_span]

end FiniteFamilyLinearMap

end

end FoxDifferential
