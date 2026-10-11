/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.FreeExpansion

/-!
# Fox differential: discrete — naturality

The principal declarations in this module are:

- `relativeFreeFoxCoordinatesMap`
  A homomorphism of coefficient groups pushes a relative Fox-coordinate vector forward.
- `relativeFreeFoxCoordinatesMap_apply`
  Pushing a relative Fox-coordinate vector along `φ` applies `groupRingMap φ` to the selected
  coordinate.
- `relativeFreeGroupFoxDerivative_mapDomain`
  Relative Fox derivatives are natural under coefficient push-forward.
- `relativeFreeGroupFoxDerivative_mapDomain_apply`
  Component form of coefficient-push-forward naturality for relative free-group Fox derivatives.
-/

namespace FoxDifferential

noncomputable section

namespace FoxCalculus

universe u v w

variable {H : Type v} {K : Type w} [Group H] [Group K]
variable {X : Type u} [DecidableEq X]
variable (ψ : FreeGroup X →* H) (φ : H →* K)

/-- A homomorphism of coefficient groups pushes a relative Fox-coordinate vector forward. -/
def relativeFreeFoxCoordinatesMap :
    RelativeFreeFoxCoordinates (H := H) X → RelativeFreeFoxCoordinates (H := K) X :=
  fun a x => groupRingMap φ (a x)

omit [DecidableEq X] in
/--
Pushing a relative Fox-coordinate vector along `φ` applies `groupRingMap φ` to the selected
coordinate.
-/
@[simp]
theorem relativeFreeFoxCoordinatesMap_apply
    (a : RelativeFreeFoxCoordinates (H := H) X) (x : X) :
    relativeFreeFoxCoordinatesMap (X := X) φ a x = groupRingMap φ (a x) :=
  rfl

/-- Relative Fox derivatives are natural under coefficient push-forward. -/
theorem relativeFreeGroupFoxDerivative_mapDomain (w : FreeGroup X) :
    relativeFreeGroupFoxDerivative (H := K) X (φ.comp ψ) w =
      relativeFreeFoxCoordinatesMap (X := X) φ
        (relativeFreeGroupFoxDerivative (H := H) X ψ w) := by
  let delta : DifferentialHom (φ.comp ψ) (RelativeFreeFoxCoordinates (H := K) X) :=
    { toFun := fun w => relativeFreeFoxCoordinatesMap (X := X) φ
        (relativeFreeGroupFoxDerivative (H := H) X ψ w)
      map_mul' := by
        intro u v
        funext x
        simp only [scalarCrossedAction_apply, relativeFreeGroupFoxDerivative_mul,
          MonoidAlgebra.of_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, map_add, map_mul, groupRingMap_single,
          groupRingScalar, MonoidHom.coe_comp, Function.comp_apply,
          relativeFreeFoxCoordinatesMap] }
  have hbasis :
      ∀ x : X, delta (FreeGroup.of x) = Pi.single x (1 : GroupRing K) := by
    intro x
    change
      relativeFreeFoxCoordinatesMap (X := X) φ
          (relativeFreeGroupFoxDerivative (H := H) X ψ (FreeGroup.of x)) =
        Pi.single x (1 : GroupRing K)
    funext y
    by_cases hxy : x = y
    · subst y
      simp only [relativeFreeFoxCoordinatesMap_apply, relativeFreeGroupFoxDerivative_of,
        Pi.single_eq_same, map_one]
    · have hyx : y ≠ x := Ne.symm hxy
      simp only [relativeFreeFoxCoordinatesMap_apply, relativeFreeGroupFoxDerivative_of,
        Pi.single_eq_of_ne hyx, map_zero]
  exact (congrFun
    (congrArg CrossedHom.toFun
      (relativeFreeGroupFoxHom_unique (H := K) X (φ.comp ψ) delta hbasis)) w).symm

/--
Component form of coefficient-push-forward naturality for relative free-group Fox derivatives.
-/
theorem relativeFreeGroupFoxDerivative_mapDomain_apply (w : FreeGroup X) (x : X) :
    relativeFreeGroupFoxDerivative (H := K) X (φ.comp ψ) w x =
      groupRingMap φ (relativeFreeGroupFoxDerivative (H := H) X ψ w x) := by
  have h := congrFun
    (relativeFreeGroupFoxDerivative_mapDomain (H := H) (K := K) ψ φ w) x
  simpa [relativeFreeFoxCoordinatesMap] using h

end FoxCalculus

end

end FoxDifferential
