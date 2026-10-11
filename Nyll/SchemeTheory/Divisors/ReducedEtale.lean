/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Noetherian
import Nyll.SchemeTheory.Divisors.Reduced
import Nyll.SchemeTheory.Morphisms.EtaleReduced

/-!
# Reduced boundaries after etale pullback

The closed subscheme of a pulled-back ideal sheaf is the corresponding
scheme-theoretic fibre product.  An etale morphism over a locally Noetherian
reduced base has reduced source, so radical boundary ideals remain radical.
-/

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

namespace Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- A reduced ideal sheaf remains reduced after pullback by an etale
morphism. -/
theorem IsReduced.comap_of_etale (I : X.IdealSheafData)
    (hI : I.IsReduced) (f : Y ⟶ X) [Etale f]
    [IsLocallyNoetherian X] : (I.comap f).IsReduced := by
  let : AlgebraicGeometry.IsReduced I.subscheme := hI.subscheme
  let : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let g : pullback f I.subschemeι ⟶ I.subscheme :=
    pullback.snd f I.subschemeι
  let : Etale g := by
    dsimp only [g]
    infer_instance
  let : AlgebraicGeometry.IsReduced (pullback f I.subschemeι) :=
    Etale.isReduced_of_isLocallyNoetherian g
  let : AlgebraicGeometry.IsReduced (I.comap f).subscheme :=
    isReduced_of_isOpenImmersion (I.comapIso f).hom
  exact (I.comap f).isReduced_of_subscheme

end Scheme.IdealSheafData

end AlgebraicGeometry

end
