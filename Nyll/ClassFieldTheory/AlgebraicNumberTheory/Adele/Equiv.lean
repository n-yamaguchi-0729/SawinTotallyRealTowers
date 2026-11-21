/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.BaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.RelativeBasic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Adelic transport along a field equivalence

Relative transport is tensor congruence. Ordinary transport is its conjugate
under the scalar-extension ring equivalence, and preserves the diagonal.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField

noncomputable section

universe u v w

section Relative

variable {K : Type u} {L : Type v} {M : Type w}
  [Field K] [NumberField K] [Field L] [Algebra K L] [Field M] [Algebra K M]

/-- A base-field algebra equivalence between two realizations of a finite
extension induces the canonical equivalence between their relative adele
algebras. -/
noncomputable def relativeAdeleCongr
    (e : L ≃ₐ[K] M) :
    RelativeAdeleRing K L ≃ₐ[
      NumberField.AdeleRing (𝓞 K) K]
      RelativeAdeleRing K M :=
  Algebra.TensorProduct.congr AlgEquiv.refl e

@[simp]
theorem relativeAdeleCongr_tmul
    (e : L ≃ₐ[K] M)
    (a : NumberField.AdeleRing (𝓞 K) K)
    (x : L) :
    relativeAdeleCongr (K := K) e (a ⊗ₜ[K] x) =
      a ⊗ₜ[K] e x :=
  rfl

/-- Identity field transport is the identity on the relative adele algebra. -/
theorem relativeAdeleCongr_refl (z : RelativeAdeleRing K L) :
    relativeAdeleCongr (K := K) (AlgEquiv.refl : L ≃ₐ[K] L) z = z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a x =>
      rw [relativeAdeleCongr_tmul]
      rfl

end Relative

section Absolute

variable {K : Type u} {M : Type w}
  [Field K] [NumberField K] [Algebra ℚ K]
  [Field M] [NumberField M] [Algebra ℚ M]

/-- The canonical transport of ordinary adele rings along an equivalence
of number fields.  It is the existing relative-adele transport over `ℚ`,
conjugated by the relative-to-ordinary scalar-extension equivalences. -/
noncomputable def adeleCongr
    (e : K ≃ₐ[ℚ] M) :
    NumberField.AdeleRing (𝓞 K) K ≃+*
      NumberField.AdeleRing (𝓞 M) M :=
  (relativeAdeleBaseChangeRingEquiv
      (K := ℚ) (L := K)).symm |>.trans
    ((relativeAdeleCongr (K := ℚ) e).toRingEquiv.trans
      (relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)))

/-- The relative-to-ordinary scalar-extension comparison is natural for
transport of the top number field. -/
theorem relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr
    (e : K ≃ₐ[ℚ] M)
    (z : RelativeAdeleRing ℚ K) :
    relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e z) =
      adeleCongr e
        (relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K) z) := by
  change
    relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e z) =
      relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e
          ((relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := K)).symm
            (relativeAdeleBaseChangeRingEquiv
              (K := ℚ) (L := K) z)))
  rw [RingEquiv.symm_apply_apply]

/-- Transport of ordinary adeles carries the diagonal field embedding to
the diagonal field embedding. -/
@[simp]
theorem adeleCongr_algebraMap
    (e : K ≃ₐ[ℚ] M)
    (x : K) :
    adeleCongr e
        (algebraMap K
          (NumberField.AdeleRing (𝓞 K) K) x) =
      algebraMap M
        (NumberField.AdeleRing (𝓞 M) M) (e x) := by
  have hx :
      (relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K)).symm
          (algebraMap K
            (NumberField.AdeleRing (𝓞 K) K) x) =
        (1 : NumberField.AdeleRing (𝓞 ℚ) ℚ) ⊗ₜ[ℚ] x := by
    apply
      (relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := K)).injective
    rw [RingEquiv.apply_symm_apply,
      relativeAdeleBaseChangeRingEquiv_fieldInclusion]
  change
    relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e
          ((relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := K)).symm
              (algebraMap K
                (NumberField.AdeleRing (𝓞 K) K) x))) =
      algebraMap M
        (NumberField.AdeleRing (𝓞 M) M) (e x)
  rw [hx, relativeAdeleCongr_tmul,
    relativeAdeleBaseChangeRingEquiv_fieldInclusion]

section Composition

variable {N : Type v} [Field N] [NumberField N] [Algebra ℚ N]

omit [NumberField K] [NumberField M] [NumberField N] in
/-- Relative adelic transport over `ℚ` is functorial in the transported
top field. -/
theorem relativeAdeleCongr_trans
    (e : K ≃ₐ[ℚ] M)
    (f : M ≃ₐ[ℚ] N)
    (z : RelativeAdeleRing ℚ K) :
    relativeAdeleCongr (K := ℚ) f
        (relativeAdeleCongr (K := ℚ) e z) =
      relativeAdeleCongr (K := ℚ) (e.trans f) z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a x =>
      rw [relativeAdeleCongr_tmul,
        relativeAdeleCongr_tmul,
        relativeAdeleCongr_tmul]
      rfl

/-- Canonical transport of ordinary adele rings is functorial. -/
theorem adeleCongr_trans
    (e : K ≃ₐ[ℚ] M)
    (f : M ≃ₐ[ℚ] N)
    (a : NumberField.AdeleRing (𝓞 K) K) :
    adeleCongr f (adeleCongr e a) =
      adeleCongr (e.trans f) a := by
  change
    relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := N)
        (relativeAdeleCongr (K := ℚ) f
          ((relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := M)).symm
            (relativeAdeleBaseChangeRingEquiv
              (K := ℚ) (L := M)
              (relativeAdeleCongr (K := ℚ) e
                ((relativeAdeleBaseChangeRingEquiv
                  (K := ℚ) (L := K)).symm a))))) =
      relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := N)
        (relativeAdeleCongr (K := ℚ) (e.trans f)
          ((relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := K)).symm a))
  rw [RingEquiv.symm_apply_apply,
    relativeAdeleCongr_trans]

end Composition

/-- Identity field transport is the identity on ordinary adeles. -/
theorem adeleCongr_refl (a : NumberField.AdeleRing (𝓞 K) K) :
    adeleCongr (AlgEquiv.refl : K ≃ₐ[ℚ] K) a = a := by
  change relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := K)
    (relativeAdeleCongr (K := ℚ) (AlgEquiv.refl : K ≃ₐ[ℚ] K)
      ((relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := K)).symm a)) = a
  rw [relativeAdeleCongr_refl, RingEquiv.apply_symm_apply]

/-- Reversing the field equivalence reverses the adelic transport. -/
theorem adeleCongr_symm (e : K ≃ₐ[ℚ] M) :
    (adeleCongr e).symm = adeleCongr e.symm := rfl

end Absolute
