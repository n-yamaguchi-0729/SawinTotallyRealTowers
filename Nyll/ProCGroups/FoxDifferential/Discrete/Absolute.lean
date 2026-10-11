/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.Naturality
import Nyll.ProCGroups.FoxDifferential.Discrete.FoxCalculus.Boundary

/-!
# Fox differential: discrete — absolute

The principal declarations in this module are:

- `freeGroupFoxDerivative`
  The absolute Fox derivative of a free-group word, with coefficients in
  \(\mathbb{Z}[\mathrm{FreeGroup}(X)]\).
- `freeGroupFoxDerivative_one`
  The absolute Fox derivative of the identity word is zero.
- `freeGroupFoxDerivative_of`
  The absolute Fox derivative of a free generator is the corresponding coordinate vector.
- `freeGroupFoxDerivative_mul`
  Product rule for the absolute Fox derivative.
-/

namespace FoxDifferential

noncomputable section

namespace FoxCalculus

open scoped BigOperators commutatorElement

universe u v

variable {X : Type u} [DecidableEq X]

/--
The absolute Fox derivative of a free-group word, with coefficients in
\(\mathbb{Z}[\mathrm{FreeGroup}(X)]\).
-/
def freeGroupFoxDerivative (w : FreeGroup X) :
    RelativeFreeFoxCoordinates (H := FreeGroup X) X :=
  relativeFreeGroupFoxDerivative (H := FreeGroup X) X
    (MonoidHom.id (FreeGroup X)) w

/-- The absolute Fox derivative of the identity word is zero. -/
@[simp]
theorem freeGroupFoxDerivative_one :
    freeGroupFoxDerivative (X := X) (1 : FreeGroup X) = 0 := by
  simp only [freeGroupFoxDerivative, relativeFreeGroupFoxDerivative_one]

/-- The absolute Fox derivative of a free generator is the corresponding coordinate vector. -/
@[simp]
theorem freeGroupFoxDerivative_of (x : X) :
    freeGroupFoxDerivative (X := X) (FreeGroup.of x) =
      Pi.single x (1 : GroupRing (FreeGroup X)) := by
  simp only [freeGroupFoxDerivative, relativeFreeGroupFoxDerivative_of]

/-- Product rule for the absolute Fox derivative. -/
theorem freeGroupFoxDerivative_mul (u v : FreeGroup X) :
    freeGroupFoxDerivative (X := X) (u * v) =
      freeGroupFoxDerivative (X := X) u +
        (MonoidAlgebra.of ℤ (FreeGroup X) u : GroupRing (FreeGroup X)) •
          freeGroupFoxDerivative (X := X) v := by
  simpa [freeGroupFoxDerivative] using
    relativeFreeGroupFoxDerivative_mul (H := FreeGroup X) X
      (MonoidHom.id (FreeGroup X)) u v

/-- Inverse rule for the absolute Fox derivative. -/
theorem freeGroupFoxDerivative_inv (w : FreeGroup X) :
    freeGroupFoxDerivative (X := X) w⁻¹ =
      -((MonoidAlgebra.of ℤ (FreeGroup X) w⁻¹ : GroupRing (FreeGroup X)) •
        freeGroupFoxDerivative (X := X) w) := by
  simpa [freeGroupFoxDerivative] using
    relativeFreeGroupFoxDerivative_inv (H := FreeGroup X) X
      (MonoidHom.id (FreeGroup X)) w

/-- Positive-power rule for the absolute Fox derivative. -/
theorem freeGroupFoxDerivative_pow (w : FreeGroup X) (n : ℕ) :
    freeGroupFoxDerivative (X := X) (w ^ n) =
      (Finset.range n).sum (fun k =>
        (MonoidAlgebra.of ℤ (FreeGroup X) (w ^ k) : GroupRing (FreeGroup X)) •
          freeGroupFoxDerivative (X := X) w) := by
  simpa [freeGroupFoxDerivative] using
    relativeFreeGroupFoxDerivative_pow (H := FreeGroup X) X
      (MonoidHom.id (FreeGroup X)) w n

/-- Conjugation rule for the absolute Fox derivative. -/
theorem freeGroupFoxDerivative_conj (g h : FreeGroup X) :
    freeGroupFoxDerivative (X := X) (g * h * g⁻¹) =
      freeGroupFoxDerivative (X := X) g +
        (MonoidAlgebra.of ℤ (FreeGroup X) g : GroupRing (FreeGroup X)) •
          freeGroupFoxDerivative (X := X) h -
        (MonoidAlgebra.of ℤ (FreeGroup X) (g * h * g⁻¹) :
          GroupRing (FreeGroup X)) •
          freeGroupFoxDerivative (X := X) g := by
  simpa [freeGroupFoxDerivative] using
    relativeFreeGroupFoxDerivative_conj (H := FreeGroup X) X
      (MonoidHom.id (FreeGroup X)) g h

/-- Commutator rule for the absolute Fox derivative. -/
theorem freeGroupFoxDerivative_commutator (g h : FreeGroup X) :
    freeGroupFoxDerivative (X := X) ⁅g, h⁆ =
      freeGroupFoxDerivative (X := X) g +
        (MonoidAlgebra.of ℤ (FreeGroup X) g : GroupRing (FreeGroup X)) •
          freeGroupFoxDerivative (X := X) h -
        (MonoidAlgebra.of ℤ (FreeGroup X) (g * h * g⁻¹) :
          GroupRing (FreeGroup X)) •
          freeGroupFoxDerivative (X := X) g -
        (MonoidAlgebra.of ℤ (FreeGroup X) ⁅g, h⁆ : GroupRing (FreeGroup X)) •
          freeGroupFoxDerivative (X := X) h := by
  simpa [freeGroupFoxDerivative] using
    relativeFreeGroupFoxDerivative_commutator (H := FreeGroup X) X
      (MonoidHom.id (FreeGroup X)) g h

variable [Fintype X]

/--
The Euler formula for the free-group Fox derivative expresses a word as the augmentation term
plus the sum of generator derivatives.
-/
theorem freeGroupFoxDerivative_euler_formula (w : FreeGroup X) :
    (MonoidAlgebra.of ℤ (FreeGroup X) w : GroupRing (FreeGroup X)) - 1 =
      ∑ x : X,
        freeGroupFoxDerivative (X := X) w x *
          augmentationGenerator (FreeGroup X) (FreeGroup.of x) := by
  simpa [freeGroupFoxDerivative] using
    relativeFreeGroupFoxDerivative_euler_formula (H := FreeGroup X) X
      (MonoidHom.id (FreeGroup X)) w

variable {H : Type v} [Group H]

omit [Fintype X] in
/--
Relative Fox derivatives are obtained from the absolute derivative by pushing coefficients
forward along \(\psi\).
-/
theorem relativeFreeGroupFoxDerivative_eq_map_freeGroupFoxDerivative
    (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    relativeFreeGroupFoxDerivative (H := H) X ψ w =
      relativeFreeFoxCoordinatesMap (X := X) ψ
        (freeGroupFoxDerivative (X := X) w) := by
  simpa [freeGroupFoxDerivative] using
    relativeFreeGroupFoxDerivative_mapDomain
      (H := FreeGroup X) (K := H) (X := X)
      (MonoidHom.id (FreeGroup X)) ψ w

omit [Fintype X] in
/--
Component form of the absolute-to-relative comparison: each relative Fox derivative coordinate
is the group-ring image of the absolute coordinate.
-/
theorem relativeFreeGroupFoxDerivative_eq_map_freeGroupFoxDerivative_apply
    (ψ : FreeGroup X →* H) (w : FreeGroup X) (x : X) :
    relativeFreeGroupFoxDerivative (H := H) X ψ w x =
      groupRingMap ψ (freeGroupFoxDerivative (X := X) w x) := by
  have h := congrFun
    (relativeFreeGroupFoxDerivative_eq_map_freeGroupFoxDerivative
      (H := H) (X := X) ψ w) x
  simpa [relativeFreeFoxCoordinatesMap] using h

end FoxCalculus

end

end FoxDifferential
