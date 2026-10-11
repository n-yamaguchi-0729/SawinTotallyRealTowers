/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Lifting quotient idempotents with prescribed open support

If the basic open of an idempotent in a quotient ring lies over an open subset of the
original spectrum, it has a lift whose basic open is contained in that subset. The lift
is obtained from a positive power and need not itself be idempotent.
-/

@[expose] public section

universe u

open TopologicalSpace

namespace PrimeSpectrum

/-- A quotient idempotent has a lift whose basic open lies in any prescribed open
containing its image in the original spectrum. The lift is not asserted to be idempotent. -/
theorem exists_lift_idempotent_basicOpen_le {R : Type u} [CommRing R]
    (I : Ideal R) (e : R ⧸ I) (he : IsIdempotentElem e)
    (U : Opens (PrimeSpectrum R))
    (hU : basicOpen e ≤ Opens.comap
      ⟨comap (Ideal.Quotient.mk I), continuous_comap (Ideal.Quotient.mk I)⟩ U) :
    ∃ g : R, Ideal.Quotient.mk I g = e ∧ basicOpen g ≤ U := by
  classical
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective e
  let J : Ideal R := vanishingIdeal ((U : Set (PrimeSpectrum R))ᶜ)
  have hJ : zeroLocus (J : Set R) = (U : Set (PrimeSpectrum R))ᶜ :=
    (zeroLocus_vanishingIdeal_eq_closure ((U : Set (PrimeSpectrum R))ᶜ)).trans
      U.isOpen.isClosed_compl.closure_eq
  have hradical : a ∈ (I ⊔ J).radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical]
    apply (mem_vanishingIdeal (zeroLocus ((I ⊔ J : Ideal R) : Set R)) a).mpr
    intro x hx
    have hIJx : I ⊔ J ≤ x.asIdeal :=
      (mem_zeroLocus x ((I ⊔ J : Ideal R) : Set R)).mp hx
    have hIx : I ≤ x.asIdeal := le_sup_left.trans hIJx
    have hJx : x ∈ zeroLocus (J : Set R) :=
      (mem_zeroLocus x (J : Set R)).mpr
        (show J ≤ x.asIdeal from le_sup_right.trans hIJx)
    rw [hJ] at hJx
    have hxRange : x ∈ Set.range (comap (Ideal.Quotient.mk I)) := by
      rw [range_comap_of_surjective (R ⧸ I) (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective]
      change RingHom.ker (Ideal.Quotient.mk I) ≤ x.asIdeal
      intro r hr
      exact hIx (Ideal.Quotient.eq_zero_iff_mem.mp hr)
    obtain ⟨y, hy⟩ := hxRange
    by_contra hax
    have hye : y ∈ basicOpen e := by
      rw [mem_basicOpen, ← ha]
      change a ∉ (comap (Ideal.Quotient.mk I) y).asIdeal
      rw [hy]
      exact hax
    have hyU : comap (Ideal.Quotient.mk I) y ∈ U := hU hye
    rw [hy] at hyU
    exact hJx hyU
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hradical
  have hn' : a ^ (n + 1) ∈ I ⊔ J := by
    rw [pow_succ]
    exact (I ⊔ J).mul_mem_right a hn
  obtain ⟨b, hb, g, hg, hbg⟩ := Submodule.mem_sup.mp hn'
  refine ⟨g, ?_, ?_⟩
  · calc
      Ideal.Quotient.mk I g = Ideal.Quotient.mk I b + Ideal.Quotient.mk I g := by
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, zero_add]
      _ = Ideal.Quotient.mk I (b + g) := (map_add (Ideal.Quotient.mk I) b g).symm
      _ = Ideal.Quotient.mk I (a ^ (n + 1)) := congrArg (Ideal.Quotient.mk I) hbg
      _ = e := by rw [map_pow, ha, he.pow_succ_eq n]
  · intro x hx
    by_contra hxU
    exact (mem_basicOpen g x).mp hx ((mem_vanishingIdeal
      ((U : Set (PrimeSpectrum R))ᶜ) g).mp hg x hxU)

end PrimeSpectrum
