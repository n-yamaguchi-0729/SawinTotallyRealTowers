/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.PlaceEquiv
import Nyll.ClassFieldTheory.Definitions.HilbertSymbols.GlobalInfinitePlaceHilbertSymbol
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.SmallHilbertPairingTransport

/-!
# Naturality of the infinite Hilbert factor

The real-place sign in the explicit infinite Hilbert factor is unchanged
under an equivalence of number fields. This reindexes the infinite part of
the product formula when a field is replaced by a small model.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace ClassFieldTheory

universe u v

/-- Corresponding real embeddings assign the same real value to a field
element and its image under the field equivalence. -/
theorem infinitePlace_embedding_of_isReal_congr
    {F : Type u} {G : Type v} [Field F] [Field G]
    (e : F ≃+* G) (W : InfinitePlace G)
    (hv : ((infinitePlaceEquivOfRingEquiv e).symm W).IsReal)
    (hW : W.IsReal) (x : F) :
    InfinitePlace.embedding_of_isReal hv x =
      InfinitePlace.embedding_of_isReal hW (e x) := by
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply,
    InfinitePlace.embedding_of_isReal_apply]
  change ((W.comap e.toRingHom).embedding) x = W.embedding (e x)
  rw [InfinitePlace.comap_embedding_of_isReal e.toRingHom hv]
  rfl

/-- The explicit infinite Hilbert factor commutes with equivalence of number
fields, including the exceptional quadratic real-place sign. -/
theorem globalInfinitePlaceHilbertSymbol_congr
    {F : Type u} {G : Type v}
    [Field F] [NumberField F] [Field G] [NumberField G]
    (e : F ≃+* G) (n : ℕ+)
    (hmuF : (primitiveRoots (n : ℕ) F).Nonempty)
    (W : InfinitePlace G) (a b : Fˣ) :
    rootsOfUnityEquivOfRingEquiv e n hmuF
        (globalInfinitePlaceHilbertSymbol F n
          ((infinitePlaceEquivOfRingEquiv e).symm W) a b) =
      globalInfinitePlaceHilbertSymbol G n W
        (Units.mapEquiv e.toMulEquiv a)
        (Units.mapEquiv e.toMulEquiv b) := by
  let v := (infinitePlaceEquivOfRingEquiv e).symm W
  let er := rootsOfUnityEquivOfRingEquiv e n hmuF
  change er (globalInfinitePlaceHilbertSymbol F n v a b) =
    globalInfinitePlaceHilbertSymbol G n W
      (Units.mapEquiv e.toMulEquiv a)
      (Units.mapEquiv e.toMulEquiv b)
  have hviff : v.IsReal ↔ W.IsReal := by
    change (W.comap e.toRingHom).IsReal ↔ W.IsReal
    exact InfinitePlace.isReal_comap_iff e
  by_cases hn : (n : ℕ) = 2
  · by_cases hW : W.IsReal
    · have hv : v.IsReal := hviff.mpr hW
      have haiff :
          InfinitePlace.embedding_of_isReal hv (a : F) < 0 ↔
            InfinitePlace.embedding_of_isReal hW
              ((Units.mapEquiv e.toMulEquiv a : Gˣ) : G) < 0 := by
        rw [show ((Units.mapEquiv e.toMulEquiv a : Gˣ) : G) = e (a : F) by
          simp]
        rw [infinitePlace_embedding_of_isReal_congr e W hv hW]
      have hbiff :
          InfinitePlace.embedding_of_isReal hv (b : F) < 0 ↔
            InfinitePlace.embedding_of_isReal hW
              ((Units.mapEquiv e.toMulEquiv b : Gˣ) : G) < 0 := by
        rw [show ((Units.mapEquiv e.toMulEquiv b : Gˣ) : G) = e (b : F) by
          simp]
        rw [infinitePlace_embedding_of_isReal_congr e W hv hW]
      by_cases ha : InfinitePlace.embedding_of_isReal hv (a : F) < 0
      · have haG := haiff.mp ha
        by_cases hb : InfinitePlace.embedding_of_isReal hv (b : F) < 0
        · have hbG := hbiff.mp hb
          simp only [globalInfinitePlaceHilbertSymbol, dite_eq_left hn,
            dite_eq_left hv, dite_eq_left hW, dite_eq_left ha, dite_eq_left hb,
            dite_eq_left haG, dite_eq_left hbG]
          apply Subtype.ext
          apply Units.ext
          change e (-1 : F) = (-1 : G)
          simp
        · have hbG := fun h => hb (hbiff.mpr h)
          simp only [globalInfinitePlaceHilbertSymbol, dite_eq_left hn,
            dite_eq_left hv, dite_eq_left hW, dite_eq_left ha, dite_eq_right hb,
            dite_eq_left haG, dite_eq_right hbG, map_one]
      · have haG := fun h => ha (haiff.mpr h)
        simp only [globalInfinitePlaceHilbertSymbol, dite_eq_left hn,
          dite_eq_left hv, dite_eq_left hW, dite_eq_right ha, dite_eq_right haG,
          map_one]
    · have hv : ¬v.IsReal := fun h => hW (hviff.mp h)
      simp [globalInfinitePlaceHilbertSymbol, hn, hv, hW]
  · simp [globalInfinitePlaceHilbertSymbol, hn]

end ClassFieldTheory
