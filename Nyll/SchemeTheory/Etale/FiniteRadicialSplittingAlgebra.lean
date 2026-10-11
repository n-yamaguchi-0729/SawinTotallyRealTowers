/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.FiniteRadicialLocalSplitting
public import Nyll.SchemeTheory.FiniteEtale.Algebra.Splitting
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TotallySplit

/-!
# Actual local splitting algebras over a finite radicial surjection

Choose a splitting étale neighborhood upstairs using the finite étale algebra
splitting theorem. The finite radicial section theorem constructs a map to
that neighborhood after an étale base change downstairs. An affine refinement
gives an actual homomorphism from the upstairs splitting algebra to the tensor
base. Base change of the existing splitting equivalence then trivializes the
original finite étale algebra there.

This supplies the local trivial models needed for finite radicial descent;
the finite radicial map itself need not be flat or finitely presented.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- Every finite étale algebra over a finite radicial surjective algebra has
an actual split base change on an étale neighborhood of each point downstairs.
The nested tensor product is the actual scalar extension of the given cover. -/
theorem Etale.exists_split_algebra_over_finite_radicial
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra S A] [Module.Finite R S]
    [Module.Finite S A] [Algebra.Etale S A]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (y : PrimeSpectrum R) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D) (_ : Algebra.Etale R D),
      y ∈ Set.range (PrimeSpectrum.comap (algebraMap R D)) ∧
      (let : Algebra S (D ⊗[R] S) := Algebra.TensorProduct.rightAlgebra;
        Algebra.IsFiniteSplit (D ⊗[R] S) ((D ⊗[R] S) ⊗[S] A)) := by
  let f : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  obtain ⟨x, hxy⟩ := f.surjective y
  obtain ⟨B, hB, hSB, hEtaleB, ⟨q, hqx⟩, hsplitB⟩ :=
    Algebra.exists_etale_isFiniteSplit (A := A) x
  let : CommRing B := hB
  let : Algebra S B := hSB
  let : Algebra.Etale S B := hEtaleB
  let : Algebra.IsFiniteSplit B (B ⊗[S] A) := hsplitB
  let : Algebra R B := Algebra.compHom B (algebraMap R S)
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  let p : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S B))
  obtain ⟨T, e, he, t, s, hpoint, hs, _, _, _⟩ :=
    Etale.exists_local_section_of_finite_radicial (R := R) (S := S) (A := B) q
  let : Etale e := he
  have hty : e t = y :=
    hpoint.trans ((congrArg (PrimeSpectrum.comap (algebraMap R S)) hqx).trans hxy)
  let D : CommRingCat.{u} := T.affineOpenCover.X (T.affineOpenCover.idx t)
  let j : Spec D ⟶ T := T.affineOpenCover.f (T.affineOpenCover.idx t)
  obtain ⟨d, hd⟩ := T.affineOpenCover.covers t
  obtain ⟨r, hr⟩ := Spec.map_surjective (j ≫ e)
  let : Algebra R D := r.hom.toAlgebra
  let eD : Spec D ⟶ Spec (CommRingCat.of R) := Spec.map r
  let : Etale eD := by
    change Etale (Spec.map r)
    rw [hr]
    infer_instance
  have hEtaleD : Algebra.Etale R D :=
    RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale)).mp (inferInstance : Etale eD))
  have hdmap : eD d = y :=
    (congrArg (fun k : Spec D ⟶ Spec (CommRingCat.of R) ↦ k d) hr).trans
      ((congrArg e hd).trans hty)
  let k : pullback f eD ⟶ pullback f e :=
    pullback.lift (pullback.fst f eD) (pullback.snd f eD ≫ j) (by
      rw [Category.assoc, ← hr]
      exact pullback.condition)
  have hks : (k ≫ s) ≫ p = pullback.fst f eD := by
    rw [Category.assoc, hs]
    exact pullback.lift_fst _ _ _
  let C := D ⊗[R] S
  let : Algebra S C := Algebra.TensorProduct.rightAlgebra
  let H : Spec (CommRingCat.of C) ≅ pullback f eD :=
    (pullbackSpecIso R D S).symm ≪≫ pullbackSymmetry eD f
  have hH : H.hom ≫ pullback.fst f eD =
      Spec.map (CommRingCat.ofHom (algebraMap S C)) := by
    simp only [H, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackSymmetry_hom_comp_fst]
    exact pullbackSpecIso_inv_snd R D S
  obtain ⟨β, hβ⟩ := Spec.map_surjective (H.hom ≫ k ≫ s)
  have hβeq : CommRingCat.ofHom (algebraMap S B) ≫ β =
      CommRingCat.ofHom (algebraMap S C) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hβ]
    calc
      (H.hom ≫ k ≫ s) ≫ p = H.hom ≫ ((k ≫ s) ≫ p) := by
        simp only [Category.assoc]
      _ = H.hom ≫ pullback.fst f eD := by rw [hks]
      _ = Spec.map (CommRingCat.ofHom (algebraMap S C)) := hH
  let σ : B →ₐ[S] C := {
    __ := β.hom
    commutes' a := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hβeq) a
  }
  let : Algebra B C := σ.toRingHom.toAlgebra
  let : IsScalarTower S B C := IsScalarTower.of_algebraMap_eq' σ.comp_algebraMap.symm
  have hsplitC : Algebra.IsFiniteSplit C (C ⊗[S] A) :=
    Algebra.IsFiniteSplit.of_algEquiv
      (Algebra.TensorProduct.cancelBaseChange S B C C A)
  exact ⟨D, inferInstance, inferInstance, hEtaleD, ⟨d, hdmap⟩, hsplitC⟩

end AlgebraicGeometry
