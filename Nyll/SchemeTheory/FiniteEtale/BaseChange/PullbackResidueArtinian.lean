/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackResidue
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Artinian residue tensors at pullback points

If one projected residue field is finite over the common residue field, its
tensor product with the other projected residue field is finite-dimensional
over that other field.  The categorical tensor in the pullback-carrier API
is therefore Artinian as well.
-/

noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Pullback

universe u

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

section

variable (T : Triplet f g)

local instance leftAlgebra :
    Algebra (S.residueField T.s) (X.residueField T.x) :=
  (((S.residueFieldCongr T.hx).inv ≫
    f.residueFieldMap T.x).hom).toAlgebra

local instance rightAlgebra :
    Algebra (S.residueField T.s) (Y.residueField T.y) :=
  (((S.residueFieldCongr T.hy).inv ≫
    g.residueFieldMap T.y).hom).toAlgebra

/-- Finiteness of the left residue-field extension makes the categorical
pullback residue tensor Artinian. -/
theorem Triplet.tensor_isArtinian_of_finiteDimensional_left
    [FiniteDimensional (S.residueField T.s) (X.residueField T.x)] :
    IsArtinianRing T.tensor := by
  let E := X.residueField T.x ⊗[S.residueField T.s]
    Y.residueField T.y
  let : Algebra (Y.residueField T.y) E :=
    Algebra.TensorProduct.rightAlgebra
  let : Module.Finite (Y.residueField T.y)
      (Y.residueField T.y ⊗[S.residueField T.s]
        X.residueField T.x) :=
    Module.Finite.base_change
      (S.residueField T.s) (Y.residueField T.y)
      (X.residueField T.x)
  let : Module.Finite (Y.residueField T.y) E :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight
        (S.residueField T.s) (Y.residueField T.y)
        (X.residueField T.x)).toLinearEquiv
  let : IsArtinianRing E := IsArtinianRing.of_finite
    (Y.residueField T.y) E
  exact
    (T.tensorIsoTensorProduct.commRingCatIsoToRingEquiv.symm).isArtinianRing

end

end AlgebraicGeometry.Scheme.Pullback
