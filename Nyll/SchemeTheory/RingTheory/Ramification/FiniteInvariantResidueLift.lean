/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.FiniteInvariantRingImage
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Invariant.Basic

/-!
# Finite invariant residue lifts through native ring maps

The finite characteristic-polynomial theorem proves preservation of the
actual coefficient image. The native first isomorphism theorem transports
the resulting image automorphism to the quotient by the kernel. The native
finite stabilizer surjection then gives one group element satisfying all
coefficient equations. No algebra from that kernel quotient to the target
ring is introduced.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

private theorem inverse_fixes_coefficient
    {A T : Type*} [CommRing A] [CommRing T]
    (φ : T ≃+* T) (a : A →+* T) (h : φ.toRingHom.comp a = a) :
    φ.symm.toRingHom.comp a = a := by
  apply RingHom.ext
  intro x
  apply φ.injective
  exact (φ.apply_symm_apply (a.toFun x)).trans
    (congrArg (fun f : A →+* T => f.toFun x) h).symm

private theorem image_mem_iff
    {C T : Type*} [CommRing C] [CommRing T]
    (f : C →+* T) (φ : T ≃+* T)
    (hf : ∀ x : C, ∃ y : C, f.toFun y = φ.toRingHom.toFun (f.toFun x))
    (hb : ∀ x : C, ∃ y : C, f.toFun y = φ.symm.toRingHom.toFun (f.toFun x)) :
    ∀ x : T, x ∈ f.range ↔ φ.toRingHom.toFun x ∈ f.range := by
  intro x
  constructor
  · rintro ⟨c, rfl⟩
    exact hf c
  · rintro ⟨c, hc⟩
    obtain ⟨d, hd⟩ := hb c
    exact ⟨d, hd.trans ((congrArg φ.symm.toRingHom.toFun hc).trans
      (φ.symm_apply_apply x))⟩

private theorem quotientKerEquivRange_coefficient
    {C T : Type*} [CommRing C] [CommRing T]
    (f : C →+* T) (x : C ⧸ RingHom.ker f) :
    ((f.quotientKerEquivRange.toRingHom.toFun x : f.range) : T) =
      (RingHom.kerLift f).toFun x := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  change ((f.quotientKerEquivRange (Ideal.Quotient.mk (RingHom.ker f) c) : f.range) : T) =
    f.toFun c
  simp only [RingHom.quotientKerEquivRange, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk,
    RingHom.coe_rangeRestrict, RingHom.toFun_eq_coe]

private def imageQuotientEquiv
    {C T : Type*} [CommRing C] [CommRing T]
    (f : C →+* T) (φ : T ≃+* T)
    (hf : ∀ x : C, ∃ y : C, f.toFun y = φ.toRingHom.toFun (f.toFun x))
    (hb : ∀ x : C, ∃ y : C, f.toFun y = φ.symm.toRingHom.toFun (f.toFun x)) :
    (C ⧸ RingHom.ker f) ≃+* (C ⧸ RingHom.ker f) :=
  f.quotientKerEquivRange.trans
    ((φ.restrict f.range f.range (image_mem_iff f φ hf hb)).trans
      f.quotientKerEquivRange.symm)

private theorem imageQuotientEquiv_comp
    {C T : Type*} [CommRing C] [CommRing T]
    (f : C →+* T) (φ : T ≃+* T)
    (hf : ∀ x : C, ∃ y : C, f.toFun y = φ.toRingHom.toFun (f.toFun x))
    (hb : ∀ x : C, ∃ y : C, f.toFun y = φ.symm.toRingHom.toFun (f.toFun x)) :
    (RingHom.kerLift f).comp (imageQuotientEquiv f φ hf hb).toRingHom =
      φ.toRingHom.comp (RingHom.kerLift f) := by
  let e : (C ⧸ RingHom.ker f) ≃+* f.range := f.quotientKerEquivRange
  let r : f.range ≃+* f.range := φ.restrict f.range f.range (image_mem_iff f φ hf hb)
  have hinv (y : f.range) :
      (RingHom.kerLift f).toFun (e.symm.toRingHom.toFun y) = (y : T) :=
    (quotientKerEquivRange_coefficient f (e.symm.toRingHom.toFun y)).symm.trans
      (congrArg (fun z : f.range => (z : T)) (e.apply_symm_apply y))
  apply RingHom.ext
  intro x
  change (RingHom.kerLift f).toFun
      (e.symm.toRingHom.toFun (r.toRingHom.toFun (e.toRingHom.toFun x))) =
    φ.toRingHom.toFun ((RingHom.kerLift f).toFun x)
  exact (hinv (r.toRingHom.toFun (e.toRingHom.toFun x))).trans
    (congrArg φ.toRingHom.toFun (quotientKerEquivRange_coefficient f x))

private def imageQuotientAlgEquiv
    {A C T : Type*} [CommRing A] [CommRing C] [CommRing T] [Algebra A C]
    (f : C →+* T) (φ : T ≃+* T)
    (hf : ∀ x : C, ∃ y : C, f.toFun y = φ.toRingHom.toFun (f.toFun x))
    (hb : ∀ x : C, ∃ y : C, f.toFun y = φ.symm.toRingHom.toFun (f.toFun x))
    (hφ : φ.toRingHom.comp (f.comp (algebraMap A C)) = f.comp (algebraMap A C)) :
    (C ⧸ RingHom.ker f) ≃ₐ[A ⧸ (RingHom.ker f).under A] (C ⧸ RingHom.ker f) where
  toRingEquiv := imageQuotientEquiv f φ hf hb
  commutes' z := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    change (imageQuotientEquiv f φ hf hb).toRingHom.toFun
        ((Ideal.Quotient.mk (RingHom.ker f)).toFun ((algebraMap A C).toFun a)) =
      (Ideal.Quotient.mk (RingHom.ker f)).toFun ((algebraMap A C).toFun a)
    apply RingHom.kerLift_injective f
    have he := congrArg (fun g : (C ⧸ RingHom.ker f) →+* T =>
        g.toFun ((Ideal.Quotient.mk (RingHom.ker f)).toFun ((algebraMap A C).toFun a)))
      (imageQuotientEquiv_comp f φ hf hb)
    have ha := congrArg (fun g : A →+* T => g.toFun a) hφ
    exact he.trans ((congrArg φ.toRingHom.toFun
      (RingHom.kerLift_mk f ((algebraMap A C).toFun a))).trans
        (ha.trans (RingHom.kerLift_mk f ((algebraMap A C).toFun a)).symm))

private theorem finiteInvariantImage_forward
    {A C T H : Type*} [CommRing A] [CommRing C] [CommRing T] [IsDomain T]
    [Algebra A C] [Group H] [Finite H] [MulSemiringAction H C]
    [Algebra.IsInvariant A C H]
    (f : C →+* T) (φ : T ≃+* T)
    (hφ : φ.toRingHom.comp (f.comp (algebraMap A C)) = f.comp (algebraMap A C)) :
    ∀ x : C, ∃ y : C, f.toFun y = φ.toRingHom.toFun (f.toFun x) := by
  intro x
  obtain ⟨h, hh⟩ := exists_smul_ringHom_apply_of_invariant (H := H) f φ hφ x
  exact ⟨h • x, hh.symm⟩

private def finiteInvariantImageQuotientAlgEquiv
    {A C T H : Type*} [CommRing A] [CommRing C] [CommRing T] [IsDomain T]
    [Algebra A C] [Group H] [Finite H] [MulSemiringAction H C]
    [Algebra.IsInvariant A C H]
    (f : C →+* T) (φ : T ≃+* T)
    (hφ : φ.toRingHom.comp (f.comp (algebraMap A C)) = f.comp (algebraMap A C)) :
    (C ⧸ RingHom.ker f) ≃ₐ[A ⧸ (RingHom.ker f).under A] (C ⧸ RingHom.ker f) :=
  imageQuotientAlgEquiv f φ
    (finiteInvariantImage_forward (H := H) f φ hφ)
    (finiteInvariantImage_forward (H := H) f φ.symm
      (inverse_fixes_coefficient φ (f.comp (algebraMap A C)) hφ)) hφ

private theorem finiteInvariantImageQuotientAlgEquiv_comp
    {A C T H : Type*} [CommRing A] [CommRing C] [CommRing T] [IsDomain T]
    [Algebra A C] [Group H] [Finite H] [MulSemiringAction H C]
    [Algebra.IsInvariant A C H]
    (f : C →+* T) (φ : T ≃+* T)
    (hφ : φ.toRingHom.comp (f.comp (algebraMap A C)) = f.comp (algebraMap A C)) :
    (RingHom.kerLift f).comp (finiteInvariantImageQuotientAlgEquiv (H := H) f φ hφ).toRingHom =
      φ.toRingHom.comp (RingHom.kerLift f) :=
  imageQuotientEquiv_comp f φ
    (finiteInvariantImage_forward (H := H) f φ hφ)
    (finiteInvariantImage_forward (H := H) f φ.symm
      (inverse_fixes_coefficient φ (f.comp (algebraMap A C)) hφ))

private theorem finiteInvariantQuotient_exists_lift
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    (H : Type*) [Group H] [Finite H] [MulSemiringAction H C]
    [SMulCommClass H A C] [Algebra.IsInvariant A C H]
    (p : Ideal A) (q : Ideal C) [q.IsPrime] [q.LiesOver p]
    (σ : (C ⧸ q) ≃ₐ[A ⧸ p] (C ⧸ q)) :
    ∃ h : H, ∀ c : C, (Ideal.Quotient.mk q).toFun (h • c) =
      σ.toRingHom.toFun ((Ideal.Quotient.mk q).toFun c) := by
  obtain ⟨h, hh⟩ := Ideal.Quotient.stabilizerHom_surjective H p q σ
  refine ⟨h.val, ?_⟩
  intro c
  exact congrArg (fun τ : (C ⧸ q) ≃ₐ[A ⧸ p] (C ⧸ q) =>
    τ.toRingHom.toFun ((Ideal.Quotient.mk q).toFun c)) hh

private theorem ringHomKernel_isPrime
    {C T : Type*} [CommRing C] [CommRing T] [IsDomain T] (f : C →+* T) :
    (RingHom.ker f).IsPrime :=
  RingHom.ker_isPrime f

/-- For a finite invariant action, a target automorphism fixing the original
coefficient map lifts to one group element on the entire coefficient image.
The conclusion is an equation in the target ring for each original element. -/
theorem finiteInvariantRingHom_exists_lift
    {A C T H : Type*} [CommRing A] [CommRing C] [CommRing T] [IsDomain T]
    [Algebra A C] [Group H] [Finite H] [MulSemiringAction H C]
    [SMulCommClass H A C] [Algebra.IsInvariant A C H]
    (f : C →+* T) (φ : T ≃+* T)
    (hφ : φ.toRingHom.comp (f.comp (algebraMap A C)) = f.comp (algebraMap A C)) :
    ∃ h : H, ∀ c : C, f.toFun (h • c) = φ.toRingHom.toFun (f.toFun c) := by
  have : (RingHom.ker f).IsPrime := ringHomKernel_isPrime f
  let σ := finiteInvariantImageQuotientAlgEquiv (H := H) f φ hφ
  obtain ⟨h, hh⟩ := finiteInvariantQuotient_exists_lift H ((RingHom.ker f).under A)
    (RingHom.ker f) σ
  refine ⟨h, ?_⟩
  intro c
  have he := congrArg (fun g : (C ⧸ RingHom.ker f) →+* T =>
      g.toFun ((Ideal.Quotient.mk (RingHom.ker f)).toFun c))
    (finiteInvariantImageQuotientAlgEquiv_comp (H := H) f φ hφ)
  exact (RingHom.kerLift_mk f (h • c)).symm.trans
    ((congrArg (RingHom.kerLift f).toFun (hh c)).trans
      (he.trans (congrArg φ.toRingHom.toFun (RingHom.kerLift_mk f c))))

end EtaleFundamentalGroups.Inertia
