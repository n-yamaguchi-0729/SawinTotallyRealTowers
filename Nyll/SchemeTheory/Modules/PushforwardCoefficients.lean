/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.Ring.Basic

/-!
# Coefficients of pushforward section modules

Constructs the prescribed coefficient maps to global and local sections and compares them.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Hom

/-- The actual base-ring map to global sections of the source. -/
def pushforwardGlobalCoefficient {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) : R →+* Γ(X, ⊤) :=
  j.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom

/-- The actual base-ring map to sections over the preimage of an open. -/
def pushforwardSectionCoefficient {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (V : (Spec R).Opens) : R →+* Γ(X, j ⁻¹ᵁ V) :=
  (j.app V).hom.comp
    ((Spec R).presheaf.map V.leTop.op).hom |>.comp (Scheme.ΓSpecIso R).inv.hom

/-- The two coefficient routes agree by the scheme morphism's actual naturality. -/
theorem pushforwardSectionCoefficient_eq_restrict {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (V : (Spec R).Opens) :
    j.pushforwardSectionCoefficient V =
      (X.presheaf.map (j ⁻¹ᵁ V).leTop.op).hom.comp j.pushforwardGlobalCoefficient := by
  apply RingHom.ext
  intro r
  have h := congrArg
    (fun k : Γ(Spec R, ⊤) ⟶ Γ(X, j ⁻¹ᵁ V) => k ((Scheme.ΓSpecIso R).inv r))
    (j.naturality V.leTop.op)
  exact h

/-- The localization open is the literal preimage of the affine basic open. -/
theorem preimage_basicOpen_pushforwardGlobalCoefficient {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (r : R) :
    j ⁻¹ᵁ PrimeSpectrum.basicOpen r = X.basicOpen (j.pushforwardGlobalCoefficient r) := by
  rw [← basicOpen_eq_of_affine (R := R) r]
  exact Scheme.preimage_basicOpen_top j ((Scheme.ΓSpecIso R).inv r)

end AlgebraicGeometry.Scheme.Hom
