/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.DifferentialModule.Basic

/-!
# Fox differential: discrete — fox calculus — semidirect

The principal declarations in this module are:

- `RelativeFreeFoxCoordinates`
  Fox-coordinate vectors for a homomorphism from a free group to a target group \(H\). The
  coefficients are already pushed forward to \(\mathbb{Z}[H]\); this is the coordinate module which
  will identify \(A_{\psi}\) with \(\mathbb{Z}[H]^X\) for \(\psi:\mathrm{FreeGroup}(X)\to H\).
- `RelativeFoxAction`
  The canonical group-ring scalar action of `H` on relative Fox-coordinate vectors.
-/

namespace FoxDifferential

noncomputable section

namespace FoxCalculus

open scoped BigOperators

universe u v


variable {H : Type v} [Group H]
variable (X : Type u)

/--
Fox-coordinate vectors for a homomorphism from a free group to a target group \(H\). The
coefficients are already pushed forward to \(\mathbb{Z}[H]\); this is the coordinate module
which will identify \(A_{\psi}\) with \(\mathbb{Z}[H]^X\) for \(\psi:\mathrm{FreeGroup}(X)\to
H\).
-/
abbrev RelativeFreeFoxCoordinates : Type _ := X → GroupRing H

/-- The canonical group-ring scalar action of `H` on relative Fox-coordinate vectors. -/
abbrev RelativeFoxAction :
    H →* Multiplicative (AddAut (RelativeFreeFoxCoordinates (H := H) X)) :=
  scalarCrossedAction (A := RelativeFreeFoxCoordinates (H := H) X)
    (groupRingScalar (MonoidHom.id H))

end FoxCalculus

end

end FoxDifferential
