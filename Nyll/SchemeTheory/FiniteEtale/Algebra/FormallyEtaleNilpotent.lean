/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Basic

/-!
# Formally étale lifting across nilpotent thickenings

Formal smoothness gives existence of lifts across nilpotent ideals, while
formal unramifiedness gives uniqueness.  This file combines the two halves
for formally étale algebras and records the resulting rigidity of two
nilpotent thickenings of the same algebra.
-/

noncomputable section

universe u v w x

namespace Algebra.FormallyEtale

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- For a formally étale algebra, reduction modulo any nilpotent ideal is
bijective on algebra homomorphisms. -/
theorem comp_bijective_of_isNilpotent [FormallyEtale R A]
    (I : Ideal B) (hI : IsNilpotent I) :
    Function.Bijective
      ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) := by
  constructor
  · intro f g h
    exact FormallyUnramified.lift_unique I hI f g h
  · exact FormallySmooth.exists_lift I hI

/-- A map from a formally étale algebra to a nilpotent quotient has a unique
lift. -/
theorem existsUnique_lift [FormallyEtale R A]
    (I : Ideal B) (hI : IsNilpotent I) (g : A →ₐ[R] B ⧸ I) :
    ∃! f : A →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f = g := by
  obtain ⟨f, hf⟩ := (comp_bijective_of_isNilpotent I hI).surjective g
  refine ⟨f, hf, fun f' hf' ↦ ?_⟩
  exact (comp_bijective_of_isNilpotent I hI).injective (hf'.trans hf.symm)

variable {C : Type x} [CommRing C] [Algebra R C]

/-- Two formally étale nilpotent thickenings of the same algebra are uniquely
isomorphic over the common quotient. -/
theorem existsUnique_algEquiv_of_surjective
    [FormallyEtale R A] [FormallyEtale R B]
    (qA : A →ₐ[R] C) (qB : B →ₐ[R] C)
    (hqA : Function.Surjective qA) (hqB : Function.Surjective qB)
    (hnA : IsNilpotent <| RingHom.ker (qA : A →+* C))
    (hnB : IsNilpotent <| RingHom.ker (qB : B →+* C)) :
    ∃! e : A ≃ₐ[R] B, qB.comp e.toAlgHom = qA := by
  let f : A →ₐ[R] B := FormallySmooth.liftOfSurjective qA qB hqB hnB
  let g : B →ₐ[R] A := FormallySmooth.liftOfSurjective qB qA hqA hnA
  have hf : qB.comp f = qA :=
    FormallySmooth.comp_liftOfSurjective qA qB hqB hnB
  have hg : qA.comp g = qB :=
    FormallySmooth.comp_liftOfSurjective qB qA hqA hnA
  have hfg : f.comp g = AlgHom.id R B := by
    apply FormallyUnramified.lift_unique' qB hnB
    ext b
    change qB (f (g b)) = qB b
    calc
      qB (f (g b)) = qA (g b) := by
        simpa only [AlgHom.comp_apply] using AlgHom.congr_fun hf (g b)
      _ = qB b := AlgHom.congr_fun hg b
  have hgf : g.comp f = AlgHom.id R A := by
    apply FormallyUnramified.lift_unique' qA hnA
    ext a
    change qA (g (f a)) = qA a
    calc
      qA (g (f a)) = qB (f a) := by
        simpa only [AlgHom.comp_apply] using AlgHom.congr_fun hg (f a)
      _ = qA a := AlgHom.congr_fun hf a
  let e : A ≃ₐ[R] B := AlgEquiv.ofAlgHom f g hfg hgf
  have he : qB.comp e.toAlgHom = qA := by
    change qB.comp f = qA
    exact hf
  refine ⟨e, he, fun e' he' ↦ ?_⟩
  apply AlgEquiv.ext
  exact AlgHom.congr_fun
    (FormallyUnramified.lift_unique' qB hnB e'.toAlgHom e.toAlgHom
      (he'.trans he.symm))

end Algebra.FormallyEtale

end
