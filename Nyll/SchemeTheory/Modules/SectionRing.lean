/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from the definitions at pinned revision
aa2d8b34692b16c70f699536de0d8e75b9a3e9ef:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_GradedOAlgebraSectionRing.lean
Upstream NOTICE and per-file ATTRIBUTION (including earlier FLT and Mathlib notices):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
See SchemeTheory/ANTHROPIC_FLT_SOURCE.md for retained notices.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.TensorPowerComparison
import Nyll.SchemeTheory.Modules.TensorSections
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Section rings of invertible module sheaves

The graded section-ring condition identifies degree `n` with global sections of the
`n`th tensor power. The direct-sum construction in `SectionRingConstruction` satisfies these
compatibilities without an assumed section-ring witness.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.GradedOAlgebra

open AlgebraicGeometry.Scheme.Modules

variable {S : Type u} [CommRing S] {X : Scheme.{u}}

/-- Pull a base scalar back to a global section of the structure sheaf. -/
def baseScalar (f : X ⟶ Spec (CommRingCat.of S)) (s : S) : Γ(X, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom s)

/-- Degreewise sections of tensor powers, compatible with addition, scalars, unit and product. -/
structure IsSectionRing (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) : Prop where
  /-- Every homogeneous component is identified bijectively with its tensor-power sections. -/
  bijective : ∀ n, Function.Bijective (ι n)
  /-- The degreewise identification is additive. -/
  map_add : ∀ n (x y : 𝓡 n), ι n (x + y) = ι n x + ι n y
  /-- Base scalar multiplication agrees with multiplication by the pulled-back scalar. -/
  map_smul : ∀ n (s : S) (x : 𝓡 n), ι n (s • x) = baseScalar f s • ι n x
  /-- The graded unit is the tensor-unit section. -/
  map_one : ι 0 ⟨1, SetLike.GradedOne.one_mem⟩ = unitSection ⊤
  /-- Graded multiplication is induced by tensoring sections. -/
  map_mul : ∀ m n (x : 𝓡 m) (y : 𝓡 n),
    ι (m + n) ⟨(x : R) * (y : R), SetLike.GradedMul.mul_mem x.2 y.2⟩ =
      ((tensorPowAdd L m n).hom.app ⊤) (tensorSections (ι m x) (ι n y))

end AlgebraicGeometry.GradedOAlgebra
