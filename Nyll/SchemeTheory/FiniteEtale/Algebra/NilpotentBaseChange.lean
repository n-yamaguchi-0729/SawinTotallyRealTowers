/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.TensorProduct.Quotient
import Nyll.SchemeTheory.FiniteEtale.Algebra.FormallyEtaleNilpotent

/-!
# Finite-etale morphisms across nilpotent base change

Formal etaleness makes morphisms lift uniquely across nilpotent thickenings.
Using the canonical identification
`(R ⧸ I) ⊗[R] B ≃ B ⧸ I B`, this gives full faithfulness of finite-etale
base change along a nilpotent quotient.
-/

noncomputable section

open CategoryTheory

namespace EtaleFundamentalGroups

universe u

private theorem ideal_map_isNilpotent
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {I : Ideal R} (hI : IsNilpotent I) :
    IsNilpotent (I.map (algebraMap R B)) := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  rw [← Ideal.map_pow, hn]
  simp

/-- If reduction to the extended quotient ideal is bijective on maps out of
an algebra, then scalar extension to the quotient of the base ring is also
bijective on those maps. -/
theorem baseChange_algHom_bijective_of_quotient_comp_bijective
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (I : Ideal R)
    (hcomp : Function.Bijective
      ((Ideal.Quotient.mkₐ R (I.map (algebraMap R B))).comp :
        (A →ₐ[R] B) → A →ₐ[R] B ⧸ I.map (algebraMap R B))) :
    Function.Bijective
      (fun f : A →ₐ[R] B ↦
        Algebra.TensorProduct.map (.id (R ⧸ I) (R ⧸ I)) f) := by
  let J : Ideal B := I.map (algebraMap R B)
  let eB := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  let qB : B →ₐ[R] B ⧸ J := Ideal.Quotient.mkₐ R J
  have hcomp' : Function.Bijective
      (qB.comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ J) := by
    simpa only [qB, J] using hcomp
  have heBqB :
      (eB.toAlgHom.restrictScalars R).comp qB =
        (Algebra.TensorProduct.includeRight :
          B →ₐ[R] TensorProduct R (R ⧸ I) B) := by
    ext b
    rfl
  constructor
  · intro f g hfg
    apply hcomp'.1
    apply AlgHom.ext
    intro a
    apply eB.injective
    have h := AlgHom.congr_fun hfg (1 ⊗ₜ[R] a)
    calc
      eB (qB (f a)) = 1 ⊗ₜ[R] f a := AlgHom.congr_fun heBqB (f a)
      _ = 1 ⊗ₜ[R] g a := h
      _ = eB (qB (g a)) := (AlgHom.congr_fun heBqB (g a)).symm
  · intro f
    let qA : A →ₐ[R] TensorProduct R (R ⧸ I) A :=
      Algebra.TensorProduct.includeRight
    let gbar : A →ₐ[R] B ⧸ J :=
      (eB.symm.toAlgHom.restrictScalars R).comp
        ((f.restrictScalars R).comp qA)
    let g : A →ₐ[R] B := Classical.choose
      (hcomp'.2 gbar)
    have hg : qB.comp g = gbar := Classical.choose_spec
      (hcomp'.2 gbar)
    refine ⟨g, ?_⟩
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply AlgHom.ext
      intro a
      have hga := AlgHom.congr_fun hg a
      calc
        1 ⊗ₜ[R] g a = eB (qB (g a)) :=
          (AlgHom.congr_fun heBqB (g a)).symm
        _ = eB (gbar a) := congrArg eB hga
        _ = f (1 ⊗ₜ[R] a) := by simp [gbar, qA]

/-- For a formally etale source, scalar extension to a nilpotent quotient is
bijective on algebra morphisms. -/
theorem finiteEtale_baseChange_algHom_bijective_of_isNilpotent
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FormallyEtale R A]
    (I : Ideal R) (hI : IsNilpotent I) :
    Function.Bijective
      (fun f : A →ₐ[R] B ↦
        Algebra.TensorProduct.map (.id (R ⧸ I) (R ⧸ I)) f) := by
  apply baseChange_algHom_bijective_of_quotient_comp_bijective I
  exact Algebra.FormallyEtale.comp_bijective_of_isNilpotent _
    (ideal_map_isNilpotent hI)

/-- Finite-etale base change along a nilpotent quotient is fully faithful. -/
noncomputable def finiteEtale_baseChange_fullyFaithful_of_isNilpotent
    {R : Type u} [CommRing R] (I : Ideal R) (hI : IsNilpotent I) :
    (CommAlgCat.FiniteEtale.baseChange R (R ⧸ I)).FullyFaithful where
  preimage {A B} f :=
    CommAlgCat.FiniteEtale.ofHom <|
      Classical.choose
        ((finiteEtale_baseChange_algHom_bijective_of_isNilpotent
          (A := A.obj) (B := B.obj) I hI).2 f.hom.hom)
  map_preimage {A B} f := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.Hom.ext
    exact Classical.choose_spec
      ((finiteEtale_baseChange_algHom_bijective_of_isNilpotent
        (A := A.obj) (B := B.obj) I hI).2 f.hom.hom)
  preimage_map {A B} f := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.Hom.ext
    exact
      (finiteEtale_baseChange_algHom_bijective_of_isNilpotent
        (A := A.obj) (B := B.obj) I hI).1 <|
        Classical.choose_spec
          ((finiteEtale_baseChange_algHom_bijective_of_isNilpotent
            (A := A.obj) (B := B.obj) I hI).2
            ((CommAlgCat.FiniteEtale.baseChange R (R ⧸ I)).map f).hom.hom)

end EtaleFundamentalGroups

end
