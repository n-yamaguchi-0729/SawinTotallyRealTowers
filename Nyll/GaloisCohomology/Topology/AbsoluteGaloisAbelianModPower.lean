/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Topology.AbsoluteGaloisMap
import Nyll.ProCGroups.Abelian.AbelianModPower

/-!
# Functoriality of absolute Galois abelianizations modulo powers

The inner discrepancy in the choice of algebraic-closure embeddings disappears
in every commutative quotient, including the quotient modulo `q`-th powers.
-/

namespace Field.absoluteGaloisGroup

open ProCGroups.Abelian

variable {K L M : Type*} [Field K] [Field L] [Field M]

/-- Absolute Galois restriction on abelianizations modulo powers respects
composition of field embeddings. -/
theorem abelianModPowerMap_map_comp (q : ℕ) (f : K →+* L) (g : L →+* M) :
    abelianModPowerMap q (map (g.comp f)) =
      (abelianModPowerMap q (map f)).comp (abelianModPowerMap q (map g)) := by
  ext x
  obtain ⟨σ, rfl⟩ := abelianModPowerMk_surjective (G := Field.absoluteGaloisGroup M) q x
  change abelianModPowerMk (Field.absoluteGaloisGroup K) q (map (g.comp f) σ) =
    abelianModPowerMk (Field.absoluteGaloisGroup K) q (map f (map g σ))
  exact DFunLike.congr_fun (character_map_comp f g
    (abelianModPowerMk (Field.absoluteGaloisGroup K) q)) σ

end Field.absoluteGaloisGroup
