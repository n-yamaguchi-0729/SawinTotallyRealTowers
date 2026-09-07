import GaloisCohomology.Cyclic.Herbrand.Induced
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

set_option autoImplicit false
/-!
# Shapiro for the multiplicative induced local blocks

The concrete equivariant-function module used by the local idele block
decomposition has exactly Mathlib's coinduced action after applying
`Additive`.  This file supplies the representation isomorphism and hence
Shapiro in all degrees, for arbitrary ambient groups and subgroups.
-/

open CategoryTheory

noncomputable section

namespace ClassFieldTower.Cohomology

open CyclicCohomology

variable {G : Type} [Group G] (H : Subgroup G)
variable (B : Type) [CommGroup B] [MulDistribMulAction H B]

/-- The multiplicative equivariant-function induced module used by the
local idele blocks is Mathlib's coinduced additive representation. -/
noncomputable def multiplicativeInducedRepIsoCoind :
    Rep.ofMulDistribMulAction G (InducedModule (B := B) H) ≅
      Rep.coind H.subtype (Rep.ofMulDistribMulAction H B) := by
  let e : Additive (InducedModule (B := B) H) ≃+
      Rep.coind H.subtype (Rep.ofMulDistribMulAction H B) :=
    { toFun := fun f ↦ ⟨fun x ↦ Additive.ofMul (f.toMul.1 x), by
        intro h x
        exact congrArg Additive.ofMul (f.toMul.2 h x)⟩
      invFun := fun f ↦ Additive.ofMul ⟨fun x ↦ (f.1 x).toMul, by
        intro h x
        exact congrArg Additive.toMul (f.2 h x)⟩
      left_inv := fun f ↦ by
        apply Additive.toMul.injective
        apply Subtype.ext
        rfl
      right_inv := fun f ↦ by
        apply Subtype.ext
        rfl
      map_add' := fun f g ↦ by
        apply Subtype.ext
        rfl }
  exact Rep.mkIso (Representation.Equiv.mk e.toIntLinearEquiv (by
    intro g
    ext f x
    rfl))

/-- Shapiro's lemma for the actual multiplicative induced module used
in the finite-place idele decomposition, in every cohomological degree. -/
noncomputable def multiplicativeInducedCohomologyIso (i : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction G (InducedModule (B := B) H)) i ≅
      groupCohomology (Rep.ofMulDistribMulAction H B) i :=
  (groupCohomology.functor ℤ G i).mapIso (multiplicativeInducedRepIsoCoind H B) ≪≫
    groupCohomology.coindIso (Rep.ofMulDistribMulAction H B) i

/-- Vanishing passes from a subgroup representation to its concrete
multiplicative induced module via the proved Shapiro isomorphism. -/
theorem multiplicativeInducedCohomology_subsingleton (i : ℕ)
    [Subsingleton (groupCohomology (Rep.ofMulDistribMulAction H B) i)] :
    Subsingleton
      (groupCohomology (Rep.ofMulDistribMulAction G (InducedModule (B := B) H)) i) :=
  Function.Injective.subsingleton
    (multiplicativeInducedCohomologyIso H B i).toLinearEquiv.injective

end ClassFieldTower.Cohomology
