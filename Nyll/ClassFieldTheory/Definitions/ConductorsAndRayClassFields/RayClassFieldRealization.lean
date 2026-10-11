/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsUnramifiedOutsideModulus
import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
import Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
import Nyll.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension

/-!
# Ray class fields
-/



open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u

/-- A finite abelian extension realizing the ray class group through a
Frobenius-normalized Artin isomorphism. -/
structure RayClassFieldRealization
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) where
  /-- The ray class field. -/
  extension : FiniteAbelianExtension K
  /-- The extension is unramified away from the modulus. -/
  unramifiedOutsideModulus :
    IsUnramifiedOutsideModulus K extension m
  /-- The Artin isomorphism for the ray class field. -/
  artinEquiv : RayClassGroup m ≃* (extension ≃ₐ[K] extension)
  /-- A prime class maps to arithmetic Frobenius. -/
  artin_frobenius :
    ∀ (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∉ m.finitePart.support)
      (w : HeightOneSpectrum (𝓞 extension)),
      w.asIdeal.LiesOver v.asIdeal →
        artinEquiv (rayClassOfFinitePrime m v hv) =
          arithmeticFrobeniusAt (K := K) w

end ClassFieldTheory
