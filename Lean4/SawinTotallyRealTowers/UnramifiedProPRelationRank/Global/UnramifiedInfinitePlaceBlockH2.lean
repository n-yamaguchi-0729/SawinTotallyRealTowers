import GaloisCohomology.ProP.MultiplicativeInducedShapiro
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.LocalBlocks

set_option autoImplicit false
/-!
# H² of an unramified infinite-place idele block

The stabilizer of an unramified infinite place has order one. Its higher
cohomology therefore vanishes, and the proved Shapiro and tensor-block
comparisons transfer this to the actual archimedean idele factor. No
cyclicity of the global Galois group is assumed.
-/

open CategoryTheory NumberField
open scoped NumberField TensorProduct

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology CyclicCohomology
open AlgebraicNumberTheory.Valuations HilbertRamification LocalClassFieldTheory

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]
variable (v : InfinitePlace K)

local notation "w" => chosenInfinitePlaceAbove (L := L) v
local notation "u" => infinitePlaceAbsoluteValueExtension v w
  (chosenInfinitePlaceAbove_comap (L := L) v)

local instance : MulDistribMulAction Gal(L / K) (v.Completion ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.Completion)

local instance : MulDistribMulAction (absoluteValueDecompositionGroup K u.1)
    (LocalizedCompletion v.1 u)ˣ :=
  decompositionGroupLocalUnitsAction v.1 v.isNontrivial u

omit [NumberField K] [NumberField L] in
/-- The actual infinite tensor-unit factor has zero degree-two cohomology
when the chosen place above it is unramified. -/
theorem unramifiedInfinitePlaceBlockH2_subsingleton
    (hunram : (w).IsUnramified K) :
    Subsingleton (groupCohomology
      (Rep.ofMulDistribMulAction Gal(L / K) (v.Completion ⊗[K] L)ˣ) 2) := by
  have hcard : Nat.card (absoluteValueDecompositionGroup K u.1) = 1 := by
    change Nat.card (absoluteValueDecompositionGroup K w.1) = 1
    rw [absoluteValueDecompositionGroup_eq_infinitePlaceStabilizer w,
      InfinitePlace.card_stabilizer, if_pos hunram]
  let _ : Subsingleton (absoluteValueDecompositionGroup K u.1) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  let _ : Subsingleton (groupCohomology (Rep.ofMulDistribMulAction
      (absoluteValueDecompositionGroup K u.1) (LocalizedCompletion v.1 u)ˣ) 2) :=
    ModuleCat.isZero_iff_subsingleton.1
      (isZero_groupCohomology_succ_of_subsingleton
        (Rep.ofMulDistribMulAction (absoluteValueDecompositionGroup K u.1)
          (LocalizedCompletion v.1 u)ˣ) 1)
  let _ := multiplicativeInducedCohomology_subsingleton
    (absoluteValueDecompositionGroup K u.1) (LocalizedCompletion v.1 u)ˣ 2
  let e := infinitePlaceTensorUnitsEquivLocalPlaceBlock (K := K) (L := L)
    v v.isNontrivial u
  let i : Rep.ofMulDistribMulAction Gal(L / K) (v.Completion ⊗[K] L)ˣ ≅
      Rep.ofMulDistribMulAction Gal(L / K) (LocalPlaceBlock v.1 v.isNontrivial u) :=
    Rep.mkIso (Representation.Equiv.mk e.toAdditive.toIntLinearEquiv (by
      intro g
      apply LinearMap.ext
      intro x
      exact congrArg Additive.ofMul (infinitePlaceTensorUnitsEquivLocalPlaceBlock_smul
        v v.isNontrivial u g x.toMul)))
  let hi : groupCohomology
      (Rep.ofMulDistribMulAction Gal(L / K) (v.Completion ⊗[K] L)ˣ) 2 ≅
      groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
        (LocalPlaceBlock v.1 v.isNontrivial u)) 2 :=
    (groupCohomology.functor ℤ Gal(L / K) 2).mapIso i
  exact Function.Injective.subsingleton hi.toLinearEquiv.injective

end ClassFieldTower.Martinet.Shafarevich
