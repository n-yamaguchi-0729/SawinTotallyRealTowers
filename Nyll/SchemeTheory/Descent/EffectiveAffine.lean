/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.AlgebraCoaction
public import Nyll.SchemeTheory.Descent.AffineCocycle
public import Nyll.SchemeTheory.Descent.FaithfullyFlatAlgebra
public import Nyll.SchemeTheory.FiniteEtale.Algebra.FaithfullyFlatDescent
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Effective affine descent in schemes

Ordinary tensor descent data give an actual invariant subalgebra. Its spectrum
is the descended scheme: the original scheme is its pullback along the cover,
and finite étaleness descends to this scheme. The comparison uses the canonical
map from the scalar extension of the invariant subalgebra, rather than an
unspecified equivalence. The quotient map is invariant under the geometric
action because each invariant element satisfies the defining equalizer equation.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Algebra.FaithfullyFlatDescent

variable {R B : Type u} [CommRing R] [CommRing B]
variable (f : R →+* B) (C : Type u) [CommRing C] [Algebra B C]

/-- The quotient to the invariant spectrum is unchanged by the geometric coaction.
This uses the defining invariant equation and does not require flatness or coaction laws. -/
theorem invariantsSpec_action_invariant
    (ρ :
      letI : Algebra R B := f.toAlgebra
      letI : Algebra R C := Algebra.compHom C f
      C →ₐ[B] B ⊗[R] C) :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    letI : IsScalarTower R B C := IsScalarTower.of_compHom R B C
    Algebra.Descent.affineCoactionAction R B C (ρ.restrictScalars R) ≫
        Spec.map (CommRingCat.ofHom (invariants f C ρ).val.toRingHom) =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (Spec.map (CommRingCat.ofHom (algebraMap R C))) ≫
        Spec.map (CommRingCat.ofHom (invariants f C ρ).val.toRingHom) := by
  let _ : Algebra R B := f.toAlgebra
  let _ : Algebra R C := Algebra.compHom C f
  let _ : IsScalarTower R B C := IsScalarTower.of_compHom R B C
  rw [Algebra.Descent.affineCoactionAction, Category.assoc, ← Spec.map_comp,
    ← pullbackSpecIso_hom_snd R B C, Category.assoc, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact z.property

end Algebra.FaithfullyFlatDescent

namespace Algebra.Descent

variable {R B : Type u} [CommRing R] [CommRing B]
variable (f : R →+* B) (C : Type u) [CommRing C] [Algebra B C]

/-- The actual invariant spectrum has the original affine scheme as its pullback.
The comparison is the spectrum of the canonical effective-descent equivalence. -/
theorem tensorDescent_isPullback (hf : f.FaithfullyFlat) :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    letI : IsScalarTower R B C := IsScalarTower.of_compHom R B C
    ∀ (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C)
      (_hdiag : (tensorTargetDiagonal R B C).comp θ.toAlgHom = tensorSourceDiagonal R B C)
      (_hcocycle : tensorCocycleLeft R B C θ = tensorCocycleRight R B C θ),
      let A := FaithfullyFlatDescent.invariants f C (tensorCoaction R B C θ)
      IsPullback (Spec.map (CommRingCat.ofHom (algebraMap B C)))
        (Spec.map (CommRingCat.ofHom A.val.toRingHom))
        (Spec.map (CommRingCat.ofHom f))
        (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  let _ : Algebra R B := f.toAlgebra
  let _ : Algebra R C := Algebra.compHom C f
  let _ : IsScalarTower R B C := IsScalarTower.of_compHom R B C
  intro θ hdiag hcocycle
  let A := FaithfullyFlatDescent.invariants f C (tensorCoaction R B C θ)
  let e : B ⊗[R] A ≃ₐ[B] C := tensorDescentEquiv f C hf θ hdiag hcocycle
  let eSpec : Spec (.of C) ≅ Spec (.of (B ⊗[R] A)) :=
    Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  let i : Spec (.of C) ≅ pullback (Spec.map (CommRingCat.ofHom f))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    eSpec ≪≫ (pullbackSpecIso R B A).symm
  have heSpec : eSpec.hom = Spec.map (CommRingCat.ofHom e.toRingHom) := rfl
  have hiFst : i.hom ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
    rw [show i.hom = eSpec.hom ≫ (pullbackSpecIso R B A).inv from rfl,
      Category.assoc, pullbackSpecIso_inv_fst, heSpec, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    exact e.commutes b
  have hiSnd : i.hom ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom A.val.toRingHom) := by
    rw [show i.hom = eSpec.hom ≫ (pullbackSpecIso R B A).inv from rfl,
      Category.assoc, pullbackSpecIso_inv_snd, heSpec, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change e ((1 : B) ⊗ₜ[R] z) = (z : C)
    rw [show e ((1 : B) ⊗ₜ[R] z) = algebraMap B C 1 * (z : C) from rfl,
      map_one, one_mul]
  apply IsPullback.of_iso_pullback _ i hiFst hiSnd
  constructor
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (A.val.commutes r).symm

/-- The spectrum of the invariant algebra is finite étale over the original base
when the algebra carrying the descent datum is finite étale. -/
theorem tensorDescent_isFiniteEtale [Module.Finite B C] [Algebra.Etale B C]
    (hf : f.FaithfullyFlat) :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    letI : IsScalarTower R B C := IsScalarTower.of_compHom R B C
    ∀ (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C)
      (_hdiag : (tensorTargetDiagonal R B C).comp θ.toAlgHom = tensorSourceDiagonal R B C)
      (_hcocycle : tensorCocycleLeft R B C θ = tensorCocycleRight R B C θ),
      let A := FaithfullyFlatDescent.invariants f C (tensorCoaction R B C θ)
      IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  let _ : Algebra R B := f.toAlgebra
  let _ : Algebra R C := Algebra.compHom C f
  let _ : IsScalarTower R B C := IsScalarTower.of_compHom R B C
  intro θ hdiag hcocycle
  let A := FaithfullyFlatDescent.invariants f C (tensorCoaction R B C θ)
  obtain ⟨hfin, het⟩ := FaithfullyFlatDescent.invariants_finite_etale f C hf
    (tensorCoaction R B C θ) (nativeCoactionAxioms f C θ hdiag hcocycle).1
    (nativeCoactionAxioms f C θ hdiag hcocycle).2
  have : Module.Finite R A := hfin
  have : Algebra.Etale R A := het
  have : Algebra.FiniteEtale R A := ⟨⟩
  apply (HasAffineProperty.SpecMap_iff_of_affineAnd (P := @IsFiniteEtale)
    inferInstance RingHom.FiniteEtale.respectsIso _).mpr
  exact (RingHom.finiteEtale_algebraMap_iff).mpr inferInstance

end Algebra.Descent
