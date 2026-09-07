import ProCGroups.FoxDifferential.Completed.Residue.FreeGroup.Basic

set_option autoImplicit false

/-!
# Fox differential: completed — residue — free group — universal

The principal declarations in this module are:

- `residueFreeCrossedHomEquivLinearMap`
  Residue crossed homomorphisms on a free group are represented by the universal residue module.
- `residueFreeGroupFoxDerivativeVectorLinearMap`
  The linear map from the residue universal module representing the residue derivative vector.
- `residueFreeGroupFoxDerivativeVectorLinearMap_universal`
  The representing linear map evaluates on the universal differential as the residue derivative
  vector.
- `existsUnique_residueFreeGroupFoxDerivativeVectorLinearMap`
  Existence and uniqueness of the linear map representing the residue derivative vector.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v


variable {X : Type u} {H : Type v} [Group H] [DecidableEq X]

/--
Residue crossed homomorphisms on a free group are represented by the universal residue module.
-/
def residueFreeCrossedHomEquivLinearMap
    (n : ℕ) (ψ : FreeGroup X →* H) :
    ScalarCrossedHom (residueGroupRingScalar n ψ) (ResidueFreeFoxCoordinates n H X) ≃
      (ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H]
        ResidueFreeFoxCoordinates n H X) :=
  residueCrossedHomEquivLinearMap
    (A := ResidueFreeFoxCoordinates n H X) n ψ

/-- The linear map from the residue universal module representing the residue derivative vector. -/
def residueFreeGroupFoxDerivativeVectorLinearMap
    (n : ℕ) (ψ : FreeGroup X →* H) :
    ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H]
      ResidueFreeFoxCoordinates n H X :=
  residueDifferentialModuleLift
    (A := ResidueFreeFoxCoordinates n H X) n ψ
    (residueFreeGroupFoxDerivativeVector n ψ)

/--
The representing linear map evaluates on the universal differential as the residue derivative
vector.
-/
@[simp]
theorem residueFreeGroupFoxDerivativeVectorLinearMap_universal
    (n : ℕ) (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    residueFreeGroupFoxDerivativeVectorLinearMap n ψ
        (residueUniversalDifferential n ψ w) =
      residueFreeGroupFoxDerivativeVector n ψ w := by
  exact residueDifferentialModuleLift_universal
    (A := ResidueFreeFoxCoordinates n H X) n ψ
    (residueFreeGroupFoxDerivativeVector n ψ) w

/-- Existence and uniqueness of the linear map representing the residue derivative vector. -/
theorem existsUnique_residueFreeGroupFoxDerivativeVectorLinearMap
    (n : ℕ) (ψ : FreeGroup X →* H) :
    ∃! f :
        ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H]
          ResidueFreeFoxCoordinates n H X,
      ∀ w : FreeGroup X,
        f (residueUniversalDifferential n ψ w) =
          residueFreeGroupFoxDerivativeVector n ψ w := by
  exact existsUnique_residueDifferentialModuleLift
    (A := ResidueFreeFoxCoordinates n H X) n ψ
    (residueFreeGroupFoxDerivativeVector n ψ)

end

end FoxDifferential
