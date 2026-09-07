import ProCGroups.FoxDifferential.Common.FreeCrossedDifferential
import ProCGroups.FoxDifferential.Completed.Residue.Core

set_option autoImplicit false

/-!
# Fox differential: completed — residue — free group — basic

The principal declarations in this module are:

- `ResidueFreeFoxCoordinates`
  Residue Fox-coordinate vectors with coefficients in \((\mathbb{Z}/n\mathbb{Z})[H]\).
- `residueFreeGroupFoxDerivativeVector`
  Residue free-group Fox derivative vector, with coefficients pushed forward along
  \(\psi:\mathrm{FreeGroup}(X)\to H\).
- `residueFreeGroupFoxDerivativeVector_of`
  The residue free-group derivative vector sends a free generator to the corresponding coordinate
  basis vector.
- `residueFreeGroupFoxDerivativeVector_unique`
  Uniqueness of the residue free-group derivative vector among crossed differentials with standard
  coordinate values on free generators.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v


variable {X : Type u} {H : Type v} [Group H] [DecidableEq X]

/-- Residue Fox-coordinate vectors with coefficients in \((\mathbb{Z}/n\mathbb{Z})[H]\). -/
abbrev ResidueFreeFoxCoordinates (n : ℕ) (H : Type v) (X : Type u) : Type (max u v) :=
  X → ResidueGroupRing n H

/--
Residue free-group Fox derivative vector, with coefficients pushed forward along
\(\psi:\mathrm{FreeGroup}(X)\to H\).
-/
def residueFreeGroupFoxDerivativeVector (n : ℕ) (ψ : FreeGroup X →* H)
    : ScalarCrossedHom (residueGroupRingScalar n ψ) (ResidueFreeFoxCoordinates n H X) :=
  freeCrossedHomWithCoeff
    (A := ResidueFreeFoxCoordinates n H X)
    (residueGroupRingScalar n ψ)
    (fun x => Pi.single x (1 : ResidueGroupRing n H))

/-- A coordinate of the residue free-group Fox derivative. -/
def residueFreeGroupFoxDerivative (n : ℕ) (ψ : FreeGroup X →* H) (i : X) :
    ScalarCrossedHom (residueGroupRingScalar n ψ) (ResidueGroupRing n H) :=
  (residueFreeGroupFoxDerivativeVector n ψ).mapLinear
    { toFun := fun v => v i
      map_add' := by intro v w; rfl
      map_smul' := by intro r v; rfl }

/--
The residue free-group derivative vector sends a free generator to the corresponding coordinate
basis vector.
-/
@[simp]
theorem residueFreeGroupFoxDerivativeVector_of (n : ℕ) (ψ : FreeGroup X →* H) (x : X) :
    residueFreeGroupFoxDerivativeVector n ψ (FreeGroup.of x) =
      Pi.single x (1 : ResidueGroupRing n H) := by
  exact freeCrossedHomWithCoeff_of
    (A := ResidueFreeFoxCoordinates n H X) (residueGroupRingScalar n ψ)
    (fun y => Pi.single y (1 : ResidueGroupRing n H)) x

/--
Uniqueness of the residue free-group derivative vector among crossed differentials with standard
coordinate values on free generators.
-/
theorem residueFreeGroupFoxDerivativeVector_unique
    (n : ℕ) (ψ : FreeGroup X →* H)
    (delta : ScalarCrossedHom (residueGroupRingScalar n ψ)
      (ResidueFreeFoxCoordinates n H X))
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : ResidueGroupRing n H)) :
    delta = residueFreeGroupFoxDerivativeVector n ψ := by
  exact freeCrossedHomWithCoeff_unique
    (A := ResidueFreeFoxCoordinates n H X)
    (residueGroupRingScalar n ψ)
    (fun x => Pi.single x (1 : ResidueGroupRing n H)) delta hbasis

/-- Existence and uniqueness theorem for the residue free-group derivative vector. -/
theorem existsUnique_residueFreeGroupFoxDerivativeVector
    (n : ℕ) (ψ : FreeGroup X →* H) :
    ∃! delta : ScalarCrossedHom (residueGroupRingScalar n ψ)
        (ResidueFreeFoxCoordinates n H X),
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : ResidueGroupRing n H) := by
  exact existsUnique_freeCrossedHomWithCoeff
    (A := ResidueFreeFoxCoordinates n H X)
    (residueGroupRingScalar n ψ)
    (fun x => Pi.single x (1 : ResidueGroupRing n H))


end

end FoxDifferential
