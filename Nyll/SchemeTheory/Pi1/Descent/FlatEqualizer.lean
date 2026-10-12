/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from the pinned pi1 source:
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/Flat/Equalizer.lean
Original mathlib source:
https://github.com/leanprover-community/mathlib4/blob/53f8a93a7739dd4eb33926f645811ebb6cee21bf/Mathlib/RingTheory/Flat/Equalizer.lean
-/

/-
Nyll-maintained port: imports and proofs have been adapted for the Nyll toolchain.
Upstream notices are preserved; local changes are documented in
Nyll/EtaleFundamentalGroups/Pi1/ATTRIBUTION.md and UPSTREAM.json.
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Algebra.Equalizer
public import Nyll.SchemeTheory.Descent.EqualizerScalars

/-!
# Flat base change of algebra equalizers

Scalar restriction and tensor-product comparisons identify equalizers after
flat base change, using the original algebra homomorphisms.
-/

@[expose] public section

universe u

open TensorProduct

variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R S] [Algebra R B]

namespace Algebra

local notation f " ≟ₐ " g => AlgHom.equalizer f g
--local notation "eq(" f " , " g ")" => AlgHom.equalizer f g

local notation S " ⊗ₘ " f => Algebra.TensorProduct.map (AlgHom.id S S) f

variable (S) in
/-- Identifies equalizers after canceling repeated base change from `R` to `T`. -/
noncomputable
def _root_.AlgHom.equalizerCancelBaseChange (f g : A →ₐ[R] B) (T : Type u) [CommRing T]
    [Algebra R T] :
    (((T ⊗[R] S) ⊗ₘ (T ⊗ₘ f)) ≟ₐ ((T ⊗[R] S) ⊗ₘ (T ⊗ₘ g))) ≃ₐ[T]
      (((T ⊗[R] S) ⊗ₘ f) ≟ₐ ((T ⊗[R] S) ⊗ₘ g)) :=
  AlgHom.equalizerCongr
    (TensorProduct.cancelBaseChange R T (T ⊗[R] S) (T ⊗[R] S) A)
    (TensorProduct.cancelBaseChange R T (T ⊗[R] S) (T ⊗[R] S) B)
    (by ext; simp) (by ext; simp) |>.restrictScalars T

@[simp]
lemma _root_.AlgHom.equalizerCancelBaseChange_algebraMap (f g : A →ₐ[R] B) (T : Type u) [CommRing T]
    [Algebra R T] (x : T ⊗[R] S) :
    AlgHom.equalizerCancelBaseChange S f g T (algebraMap _ _ x) = algebraMap _ _ x := by
  simp [AlgHom.equalizerCancelBaseChange]

lemma _root_.AlgHom.equalizerCongr_symm_apply {R A A' B B' : Type*} [CommSemiring R]
    [Semiring A] [Semiring A'] [Semiring B] [Semiring B']
    [Algebra R A] [Algebra R A'] [Algebra R B] [Algebra R B']
    (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B')
    {f g : A →ₐ[R] B} {f' g' : A' →ₐ[R] B'}
    (hf : eB.toAlgHom.comp f = f'.comp eA) (hg : eB.toAlgHom.comp g = g'.comp eA)
    (x : AlgHom.equalizer f' g') :
    (AlgHom.equalizerCongr eA eB hf hg).symm x =
      ⟨eA.symm x, ((AlgHom.equalizerCongr eA eB hf hg).symm x).2⟩ :=
  rfl

lemma _root_.AlgHom.equalizerCongr_apply {R A A' B B' : Type*} [CommSemiring R]
    [Semiring A] [Semiring A'] [Semiring B] [Semiring B']
    [Algebra R A] [Algebra R A'] [Algebra R B] [Algebra R B']
    (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B')
    {f g : A →ₐ[R] B} {f' g' : A' →ₐ[R] B'}
    (hf : eB.toAlgHom.comp f = f'.comp eA) (hg : eB.toAlgHom.comp g = g'.comp eA)
    (x : AlgHom.equalizer f g) :
    AlgHom.equalizerCongr eA eB hf hg x =
      ⟨eA x, (AlgHom.equalizerCongr eA eB hf hg x).2⟩ :=
  rfl

@[simp]
lemma _root_.AlgHom.equalizerCancelBaseChange_tmul (f g : A →ₐ[R] B) (T : Type u) [CommRing T]
    [Algebra R T] (x : A) (hx : x ∈ AlgHom.equalizer f g) :
    ((AlgHom.equalizerCancelBaseChange S f g T)
      ⟨1 ⊗ₜ[T] (1 ⊗ₜ[R] x), by simp [show f x = g x from hx]⟩) =
        ⟨1 ⊗ₜ x, by simp [show f x = g x from hx]⟩ := by
  ext : 1
  simp [AlgHom.equalizerCancelBaseChange, AlgHom.equalizerCongr_apply]

lemma _root_.AlgHom.tensorEqualizerEquiv_symm_apply
    {R : Type*} (S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] (T : Type*) [CommRing T]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f g : A →ₐ[R] B) [Module.Flat R T]
    (x : A) (hx : x ∈ AlgHom.equalizer f g) :
    (f.tensorEqualizerEquiv S T g).symm ⟨1 ⊗ₜ x, by simp [show f x = g x from hx]⟩ =
      1 ⊗ₜ ⟨x, hx⟩ := by
  apply (f.tensorEqualizerEquiv S T g).injective
  ext
  simp

/-- For flat `T`, identifies the base change of the equalizer of the `S`-base-changed maps
with the equalizer of the further base-changed maps over `T ⊗[R] S`. -/
@[reducible]
noncomputable def auxEquivRHS (f g : A →ₐ[R] B) (T : Type u) [CommRing T] [Algebra R T]
    [Module.Flat R T] :
    T ⊗[R] ((S ⊗ₘ f) ≟ₐ (S ⊗ₘ g)) ≃ₐ[T]
      ((T ⊗[R] S) ⊗ₘ (T ⊗ₘ f)) ≟ₐ ((T ⊗[R] S) ⊗ₘ (T ⊗ₘ g)) :=
  let fS : S ⊗[R] A →ₐ[S] S ⊗[R] B :=
    TensorProduct.map (.id S S) f
  let gS : S ⊗[R] A →ₐ[S] S ⊗[R] B :=
    TensorProduct.map (.id S S) g
  let eBase :
      AlgHom.equalizer fS gS ≃ₐ[R]
        AlgHom.equalizer (fS.restrictScalars R) (gS.restrictScalars R) :=
    (AlgHom.equalizerRestrictScalars R fS gS).symm
  let aux :
      ↥(TensorProduct.map (.id T T) (fS.restrictScalars R) ≟ₐ
        TensorProduct.map (.id T T) (gS.restrictScalars R)) ≃ₐ[T]
      ↥(TensorProduct.map (.id (T ⊗[R] S) (T ⊗[R] S)) f ≟ₐ
        TensorProduct.map (.id (T ⊗[R] S) (T ⊗[R] S)) g) :=
    .trans
      (AlgHom.equalizerCongr
        (TensorProduct.assoc R R T T S A).symm
        (TensorProduct.assoc R R T T S B).symm
        (by ext <;> simp [fS]) (by ext <;> simp [gS]))
      (AlgHom.equalizerRestrictScalars T _ _)
  (TensorProduct.congr .refl eBase).trans <|
    (fS.restrictScalars R).tensorEqualizerEquiv T T
      (gS.restrictScalars R) |>.trans <|
      aux.trans (f.equalizerCancelBaseChange S g T).symm

lemma auxEquivRHS_symm_tmul (f g : A →ₐ[R] B) (T : Type u) [CommRing T] [Algebra R T]
    [Module.Flat R T] (x : S) :
    (auxEquivRHS (S := S) f g T).symm (algebraMap (T ⊗[R] S) _ (1 ⊗ₜ x)) =
      1 ⊗ₜ algebraMap _ _ x := by
  apply (auxEquivRHS (S := S) f g T).injective
  rw [AlgEquiv.apply_symm_apply]
  apply (f.equalizerCancelBaseChange S g T).injective
  change _ = (f.equalizerCancelBaseChange S g T)
    ((f.equalizerCancelBaseChange S g T).symm _)
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  simp only [AlgHom.equalizerCancelBaseChange_algebraMap, SubalgebraClass.coe_algebraMap,
    TensorProduct.algebraMap_apply, algebraMap_self, RingHom.id_apply, AlgEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe, TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom,
    TensorProduct.map_tmul, AlgHom.coe_id, id_eq, AlgEquiv.coe_toAlgHom,
    AlgHom.equalizerRestrictScalars_symm_apply, AlgHom.tensorEqualizerEquiv_apply,
    AlgEquiv.trans_apply, AlgHom.equalizerRestrictScalars_apply]
  change
    (1 ⊗ₜ[R] x) ⊗ₜ[R] (1 : A) =
      (TensorProduct.assoc R R T T S A).symm
        (1 ⊗ₜ[R] (x ⊗ₜ[R] (1 : A)))
  rw [TensorProduct.assoc_symm_tmul]

lemma auxEquivRHS_symm_tmul' (f g : A →ₐ[R] B) (T : Type u) [CommRing T] [Algebra R T]
    [Module.Flat R T] (x : AlgHom.equalizer f g) :
    (auxEquivRHS (S := S) f g T).symm ⟨1 ⊗ₜ (1 ⊗ₜ x), by simp [show f x = g x from x.2]⟩ =
      1 ⊗ₜ ⟨1 ⊗ₜ x, by simp [show f x = g x from x.2]⟩ := by
  apply (auxEquivRHS (S := S) f g T).injective
  rw [AlgEquiv.apply_symm_apply]
  apply (f.equalizerCancelBaseChange S g T).injective
  change _ = (f.equalizerCancelBaseChange S g T)
    ((f.equalizerCancelBaseChange S g T).symm _)
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  simp only [SetLike.coe_mem, AlgHom.equalizerCancelBaseChange_tmul, AlgEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe, TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom,
    TensorProduct.map_tmul, AlgHom.coe_id, id_eq, AlgEquiv.coe_toAlgHom,
    AlgHom.equalizerRestrictScalars_symm_apply, AlgHom.tensorEqualizerEquiv_apply,
    AlgEquiv.trans_apply, AlgHom.equalizerRestrictScalars_apply]
  change
    (1 ⊗ₜ[R] (1 : S)) ⊗ₜ[R] (x : A) =
      (TensorProduct.assoc R R T T S A).symm
        (1 ⊗ₜ[R] ((1 : S) ⊗ₜ[R] (x : A)))
  rw [TensorProduct.assoc_symm_tmul]

/-- For flat `T`, reassociates `T ⊗[R] (S ⊗[R] equalizer f g)` and identifies it with
`(T ⊗[R] S) ⊗[T] equalizer(T ⊗ f, T ⊗ g)` by flat base change. -/
noncomputable
def auxEquivLHS (f g : A →ₐ[R] B) (T : Type u) [CommRing T] [Algebra R T] [Module.Flat R T] :
    T ⊗[R] (S ⊗[R] f ≟ₐ g) ≃ₐ[T] (T ⊗[R] S) ⊗[T] ((T ⊗ₘ f) ≟ₐ (T ⊗ₘ g)) :=
  .trans
    (.trans
      (TensorProduct.assoc R R T T S (f ≟ₐ g)).symm
      (TensorProduct.cancelBaseChange R T T (T ⊗[R] S) (f ≟ₐ g)).symm)
    (TensorProduct.congr .refl (f.tensorEqualizerEquiv T T g))

@[simp]
lemma auxEquivLHS_one_tmul_one (f g : A →ₐ[R] B) (T : Type u) [CommRing T] [Algebra R T]
    [Module.Flat R T] (x : S) :
    auxEquivLHS f g T (1 ⊗ₜ[R] (x ⊗ₜ[R] 1)) = (1 ⊗ₜ x) ⊗ₜ 1 :=
  rfl

lemma auxEquivLHS_one_one_tmul (f g : A →ₐ[R] B) (T : Type u) [CommRing T] [Algebra R T]
    [Module.Flat R T] (x : AlgHom.equalizer f g) :
    (auxEquivLHS (S := S) f g T) (1 ⊗ₜ[R] (1 ⊗ₜ[R] x)) =
      1 ⊗ₜ ⟨1 ⊗ₜ x, by simp [show f x.1 = g x.1 from x.2]⟩ :=
  rfl

lemma _root_.AlgHom.tensorEqualizer_tmul_one (f g : A →ₐ[R] B) (x : S) :
    f.tensorEqualizer S S g (x ⊗ₜ 1) = algebraMap S _ x :=
  rfl

lemma _root_.AlgHom.tensorEqualizer_one_tmul {R : Type*} (S : Type*) [CommRing R]
      [CommRing S] [Algebra R S] (T : Type*) [CommRing T]
      [Algebra R T] [Algebra S T] [IsScalarTower R S T]
      {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (f g : A →ₐ[R] B) (x : AlgHom.equalizer f g) :
    f.tensorEqualizer S T g (1 ⊗ₜ x) = ⟨1 ⊗ₜ x, by simp [show f x.1 = g x.1 from x.2]⟩ :=
  rfl

lemma _root_.AlgHom.tensorEqualizer_tmul_one' {R : Type*} (S : Type*) [CommRing R]
      [CommRing S] [Algebra R S] (T : Type*) [CommRing T]
      [Algebra R T] [Algebra S T] [IsScalarTower R S T]
      {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (f g : A →ₐ[R] B) (x : T) :
    f.tensorEqualizer S T g (x ⊗ₜ 1) = ⟨x ⊗ₜ 1, by simp⟩ :=
  rfl

variable (S) in
lemma TensorProduct.map_tensorEqualizer_bijective_iff_tensorEqualizer_map_bijective
    (f g : A →ₐ[R] B) (T : Type u) [CommRing T] [Algebra R T] [Module.Flat R T] :
    Function.Bijective ⇑(TensorProduct.map (AlgHom.id T T) (AlgHom.tensorEqualizer R S f g)) ↔
    Function.Bijective
            ((TensorProduct.map (.id T T) f).tensorEqualizer T (T ⊗[R] S)
                  (TensorProduct.map (.id T T) g)) := by
  let eLHS : T ⊗[R] (S ⊗[R] f ≟ₐ g) ≃ₐ[T] (T ⊗[R] S) ⊗[T]
      ((T ⊗ₘ f) ≟ₐ (T ⊗ₘ g)) :=
    auxEquivLHS f g T
  let fTS :
      (T ⊗[R] S) ⊗[T] (T ⊗[R] A) →ₐ[T ⊗[R] S]
        (T ⊗[R] S) ⊗[T] (T ⊗[R] B) :=
    TensorProduct.map (.id (T ⊗[R] S) (T ⊗[R] S))
      (TensorProduct.map (.id T T) f)
  let gTS :
      (T ⊗[R] S) ⊗[T] (T ⊗[R] A) →ₐ[T ⊗[R] S]
        (T ⊗[R] S) ⊗[T] (T ⊗[R] B) :=
    TensorProduct.map (.id (T ⊗[R] S) (T ⊗[R] S))
      (TensorProduct.map (.id T T) g)
  let eRestrict :
      (TensorProduct.map (.id T (T ⊗[R] S)) (T ⊗ₘ f) ≟ₐ
          TensorProduct.map (.id T (T ⊗[R] S)) (T ⊗ₘ g)) ≃ₐ[T]
        (fTS ≟ₐ gTS) :=
    AlgHom.equalizerRestrictScalars T fTS gTS
  let eRHS : T ⊗[R] ((S ⊗ₘ f) ≟ₐ (S ⊗ₘ g)) ≃ₐ[T]
      (TensorProduct.map (.id T (T ⊗[R] S)) (T ⊗ₘ f) ≟ₐ
        TensorProduct.map (.id T (T ⊗[R] S)) (T ⊗ₘ g)) :=
    (auxEquivRHS f g T).trans eRestrict.symm
  have : IsScalarTower R T
      (T ⊗[R] ↥(TensorProduct.map (AlgHom.id R S) f ≟ₐ TensorProduct.map (AlgHom.id R S) g)) :=
    TensorProduct.isScalarTower_left
  let u := (TensorProduct.map (.id T T) f).tensorEqualizer T (T ⊗[R] S)
    (TensorProduct.map (.id T T) g)
  have heq : TensorProduct.map (AlgHom.id T T) (AlgHom.tensorEqualizer R S f g) =
      eRHS.symm.toAlgHom.comp
        (((TensorProduct.map (.id T T) f).tensorEqualizer T (T ⊗[R] S)
            (TensorProduct.map (.id T T) g)).comp
          eLHS.toAlgHom) := by
    ext x
    · simp only [TensorProduct.map_restrictScalars_comp_includeRight, AlgHom.coe_comp,
        Function.comp_apply, TensorProduct.includeLeft_apply, TensorProduct.includeRight_apply]
      change _ = eRHS.symm
        (((TensorProduct.map (.id T T) f).tensorEqualizer T (T ⊗[R] S)
          (TensorProduct.map (.id T T) g)) (eLHS (1 ⊗ₜ[R] (x ⊗ₜ[R] 1))))
      simp only [auxEquivLHS_one_tmul_one, eLHS]
      change 1 ⊗ₜ[R] (AlgHom.tensorEqualizer S S f g) (x ⊗ₜ 1) = eRHS.symm
        ((AlgHom.tensorEqualizer T (T ⊗[R] S)
          (TensorProduct.map (AlgHom.id T T) f) (TensorProduct.map (AlgHom.id T T) g))
          ((1 ⊗ₜ[R] x) ⊗ₜ[T] 1))
      rw [AlgHom.tensorEqualizer_tmul_one, AlgHom.tensorEqualizer_tmul_one']
      calc
        _ = (auxEquivRHS (S := S) f g T).symm
            (algebraMap (T ⊗[R] S) _ (1 ⊗ₜ[R] x)) :=
          (auxEquivRHS_symm_tmul (S := S) f g T x).symm
        _ = _ := by
          dsimp [eRHS, eRestrict, fTS, gTS]
          congr 1
    · simp only [TensorProduct.map_restrictScalars_comp_includeRight, AlgHom.coe_comp,
        AlgHom.coe_restrictScalars', Function.comp_apply, TensorProduct.includeRight_apply,
        eLHS]
      change _ = eRHS.symm (u (eLHS (1 ⊗ₜ[R] (1 ⊗ₜ[R] x))))
      rw [auxEquivLHS_one_one_tmul]
      rw [AlgHom.tensorEqualizer_one_tmul, AlgHom.tensorEqualizer_one_tmul]
      calc
        _ = (auxEquivRHS (S := S) f g T).symm
            ⟨1 ⊗ₜ[T] (1 ⊗ₜ[R] x), by simp [show f x = g x from x.2]⟩ :=
          (auxEquivRHS_symm_tmul' (S := S) f g T x).symm
        _ = _ := by
          dsimp [eRHS, eRestrict, fTS, gTS]
          congr 1
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · rw [heq] at H
    rw [← Function.Bijective.of_comp_iff _ eLHS.bijective]
    rw [← Function.Bijective.of_comp_iff' eRHS.symm.bijective]
    exact H
  · rw [heq]
    apply eRHS.symm.bijective.comp
    exact H.comp eLHS.bijective

end Algebra
