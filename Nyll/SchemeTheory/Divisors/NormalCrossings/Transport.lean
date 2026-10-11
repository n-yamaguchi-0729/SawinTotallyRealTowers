/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.NormalCrossings.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Transport of split normal-crossings charts

The explicit local chart is invariant under a change of ring model by an
isomorphism.  This is used to pass between a scheme stalk and the canonical
prime-localization model of the same local ring.
-/

namespace EtaleFundamentalGroups

universe u

/-- Split strict-normal-crossings charts are preserved by ring
isomorphisms. -/
theorem IsSplitStrictNormalCrossingsAt.map_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) {d r : ℕ} {f : R} {t : Fin d → R}
    (h : IsSplitStrictNormalCrossingsAt f t r) :
    IsSplitStrictNormalCrossingsAt (e f) (e ∘ t) r := by
  rcases h with ⟨hrpos, hrd, hparams, hprime, hassoc, hbranch⟩
  refine ⟨hrpos, hrd, ?_, ?_, ?_, ?_⟩
  · constructor
    · have hreg : RingTheory.Sequence.IsRegular S
          ((List.ofFn t).map e) :=
        (e.toAddEquiv.isRegular_congr
          (List.forall₂_map_right_iff.mpr
            (List.forall₂_same.mpr fun a _ z ↦ e.map_mul a z))).mp
          hparams.1
      simpa only [List.map_ofFn] using hreg
    · calc
        Ideal.ofList (List.ofFn (e ∘ t)) =
            Ideal.ofList (List.ofFn ((e : R →+* S) ∘ t)) := rfl
        _ =
            Ideal.map (e : R →+* S) (Ideal.ofList (List.ofFn t)) := by
              simpa only [List.map_ofFn] using
                (Ideal.map_ofList (e : R →+* S) (List.ofFn t)).symm
        _ = Ideal.map (e : R →+* S) (IsLocalRing.maximalIdeal R) :=
          congrArg (Ideal.map (e : R →+* S)) hparams.2
        _ = IsLocalRing.maximalIdeal S :=
          IsLocalRing.map_ringEquiv_maximalIdeal e
  · intro i hi
    change Prime (e (t i))
    exact (MulEquiv.prime_iff e.toMulEquiv).mpr (hprime i hi)
  · simpa [boundaryProduct] using hassoc.map e.toMonoidHom
  · intro i hi
    let : IsRegularRing (R ⧸ Ideal.span {t i}) := hbranch i hi
    have hspan : Ideal.span {e (t i)} =
        (Ideal.span {t i}).map e := by
      rw [Ideal.map_span, Set.image_singleton]
    exact IsRegularRing.of_ringEquiv
      (Ideal.quotientEquiv (Ideal.span {t i})
        (Ideal.span {e (t i)}) e hspan)

end EtaleFundamentalGroups
