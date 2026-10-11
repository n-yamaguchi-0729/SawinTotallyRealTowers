/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint

/-!
# Affine Weil restriction along a finite free algebra

For a finite free commutative `R`-algebra `A` and a finitely presented
commutative `R`-algebra `B`, this file constructs explicitly an
`R`-algebra representing
`C ↦ Hom_R(B, C ⊗[R] A)`.

This is the affine algebra input for the finite étale relative internal Hom
of [Stacks Project, Tag 0BL7](https://stacks.math.columbia.edu/tag/0BL7).
The presentation-dependent construction is kept private; the public theorem
is independent of all choices.
-/


@[expose] public section

open scoped TensorProduct BigOperators

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open TensorProduct
open Module

universe u

namespace CommAlgCat

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

private abbrev BasisIndex (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] := Module.Free.ChooseBasisIndex R A

private abbrev chosenBasis (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] : Module.Basis (BasisIndex R A) R A :=
  Module.Free.chooseBasis R A

variable [Module.Free R A] [Module.Finite R A]
  {ι σ : Type u} (P : Algebra.Presentation R B ι σ)

private def genericImage (i : ι) :
    MvPolynomial (ι × BasisIndex R A) R ⊗[R] A :=
  ∑ j, MvPolynomial.X (i, j) ⊗ₜ[R] chosenBasis R A j

private lemma genericImage_coeff (i : ι) (j : BasisIndex R A) :
    (Algebra.TensorProduct.basis (MvPolynomial (ι × BasisIndex R A) R)
      (chosenBasis R A)).repr (genericImage (R := R) (A := A) i) j =
      MvPolynomial.X (i, j) := by
  classical
  simp only [genericImage, map_sum, Algebra.TensorProduct.basis_repr_tmul]
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [hkj]
  · simp

private def relationCoeff (s : σ) (j : BasisIndex R A) :
    MvPolynomial (ι × BasisIndex R A) R :=
  (Algebra.TensorProduct.basis
      (MvPolynomial (ι × BasisIndex R A) R) (chosenBasis R A)).repr
    (MvPolynomial.aeval (genericImage (R := R) (A := A)) (P.relation s)) j

private def relationsIdeal : Ideal (MvPolynomial (ι × BasisIndex R A) R) :=
  Ideal.span (Set.range fun x : σ × BasisIndex R A =>
    relationCoeff (P := P) x.1 x.2)

private abbrev HomRing :=
  MvPolynomial (ι × BasisIndex R A) R ⧸ relationsIdeal (P := P)

omit [Module.Finite R A] in
private lemma basis_repr_map
    {C D : Type u} [CommRing C] [CommRing D] [Algebra R C] [Algebra R D]
    (f : C →ₐ[R] D) (x : C ⊗[R] A) (j : BasisIndex R A) :
    (Algebra.TensorProduct.basis D (chosenBasis R A)).repr
        (Algebra.TensorProduct.map f (AlgHom.id R A) x) j =
      f ((Algebra.TensorProduct.basis C (chosenBasis R A)).repr x j) := by
  induction x using TensorProduct.inductionOn with
  | tmul c a =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply,
        Finsupp.mapRange_apply, smul_eq_mul, map_mul, f.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

omit [Module.Finite R A] in
private lemma basis_repr_aeval_map
    {C D : Type u} [CommRing C] [CommRing D] [Algebra R C] [Algebra R D]
    {κ : Type u} (f : C →ₐ[R] D) (x : κ → C ⊗[R] A)
    (p : MvPolynomial κ R) (j : BasisIndex R A) :
    (Algebra.TensorProduct.basis D (chosenBasis R A)).repr
        (MvPolynomial.aeval
          (fun i => Algebra.TensorProduct.map f (AlgHom.id R A) (x i)) p) j =
      f ((Algebra.TensorProduct.basis C (chosenBasis R A)).repr
        (MvPolynomial.aeval x p) j) := by
  let tf := Algebra.TensorProduct.map f (AlgHom.id R A)
  calc
    (Algebra.TensorProduct.basis D (chosenBasis R A)).repr
        (MvPolynomial.aeval (fun i => tf (x i)) p) j =
      (Algebra.TensorProduct.basis D (chosenBasis R A)).repr
        (tf (MvPolynomial.aeval x p)) j :=
      congrArg (fun z =>
        (Algebra.TensorProduct.basis D (chosenBasis R A)).repr z j)
        (MvPolynomial.comp_aeval_apply x tf p).symm
    _ = f ((Algebra.TensorProduct.basis C (chosenBasis R A)).repr
        (MvPolynomial.aeval x p) j) := basis_repr_map f _ j

private def quotientImage (i : ι) : HomRing (R := R) (A := A) (B := B) P ⊗[R] A :=
  Algebra.TensorProduct.map
    (Ideal.Quotient.mkₐ R (relationsIdeal (R := R) (A := A) (B := B) P))
    (AlgHom.id R A)
    (genericImage (R := R) (A := A) i)

private lemma aeval_relation_quotientImage (s : σ) :
    MvPolynomial.aeval (quotientImage (R := R) (A := A) (B := B) P)
      (P.relation s) = 0 := by
  let q := Ideal.Quotient.mkₐ R (relationsIdeal (R := R) (A := A) (B := B) P)
  let xq : ι → HomRing (R := R) (A := A) (B := B) P ⊗[R] A :=
    fun i => Algebra.TensorProduct.map q (AlgHom.id R A)
      (genericImage (R := R) (A := A) i)
  have hxq : quotientImage (R := R) (A := A) (B := B) P = xq := rfl
  rw [hxq]
  apply (Algebra.TensorProduct.basis (HomRing (R := R) (A := A) (B := B) P)
    (chosenBasis R A)).repr.injective
  ext j
  rw [map_zero, Finsupp.zero_apply]
  calc
    (Algebra.TensorProduct.basis (HomRing (R := R) (A := A) (B := B) P)
        (chosenBasis R A)).repr
        (MvPolynomial.aeval xq (P.relation s)) j =
      q (relationCoeff (R := R) (A := A) (B := B) P s j) := by
        simpa only [HomRing, relationCoeff, xq, q] using
          (basis_repr_aeval_map
            (A := A) (R := R) q (genericImage (R := R) (A := A)) (P.relation s) j)
    _ = 0 := by
      change Ideal.Quotient.mk (relationsIdeal (R := R) (A := A) (B := B) P)
        (relationCoeff (R := R) (A := A) (B := B) P s j) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      apply Ideal.subset_span
      exact ⟨(s, j), rfl⟩

private def presentationMap : P.Ring →ₐ[R] HomRing (R := R) (A := A) (B := B) P ⊗[R] A :=
  MvPolynomial.aeval (quotientImage (R := R) (A := A) (B := B) P)

private lemma presentationMap_relation (s : σ) :
    presentationMap (R := R) (A := A) (B := B) P (P.relation s) = 0 :=
  aeval_relation_quotientImage (R := R) (A := A) (B := B) P s

private lemma presentation_ker_le :
    P.ker ≤ RingHom.ker (presentationMap (R := R) (A := A) (B := B) P).toRingHom := by
  rw [← P.span_range_relation_eq_ker, Ideal.span_le]
  rintro x ⟨s, rfl⟩
  change presentationMap (R := R) (A := A) (B := B) P (P.relation s) = 0
  exact presentationMap_relation (R := R) (A := A) (B := B) P s

private def presentationLift : P.Quotient →ₐ[R]
    HomRing (R := R) (A := A) (B := B) P ⊗[R] A :=
  Ideal.Quotient.liftₐ P.ker (presentationMap (R := R) (A := A) (B := B) P)
    (fun _ hx ↦ RingHom.mem_ker.mp
      (presentation_ker_le (R := R) (A := A) (B := B) P hx))

private def universal : B →ₐ[R] HomRing (R := R) (A := A) (B := B) P ⊗[R] A :=
  (presentationLift (R := R) (A := A) (B := B) P).comp
    (P.quotientEquiv.restrictScalars R).symm.toAlgHom

private lemma universal_val (i : ι) :
    universal (R := R) (A := A) (B := B) P (P.val i) =
      quotientImage (R := R) (A := A) (B := B) P i := by
  change presentationLift (R := R) (A := A) (B := B) P
    (P.quotientEquiv.symm (P.val i)) = _
  rw [P.quotientEquiv_symm]
  change presentationMap (R := R) (A := A) (B := B) P (P.σ (P.val i)) = _
  have hker : P.σ (P.val i) - MvPolynomial.X i ∈ P.ker := by
    rw [P.ker_eq_ker_aeval_val, RingHom.mem_ker, map_sub,
      P.aeval_val_σ, MvPolynomial.aeval_X, sub_self]
  have hz := RingHom.mem_ker.mp
    (presentation_ker_le (R := R) (A := A) (B := B) P hker)
  rw [map_sub, sub_eq_zero] at hz
  change presentationMap (R := R) (A := A) (B := B) P (P.σ (P.val i)) =
    presentationMap (R := R) (A := A) (B := B) P (MvPolynomial.X i) at hz
  exact hz.trans (MvPolynomial.aeval_X _ i)

variable {C : Type u} [CommRing C] [Algebra R C]

private def coeffAssignment (g : B →ₐ[R] C ⊗[R] A) (x : ι × BasisIndex R A) : C :=
  (Algebra.TensorProduct.basis C (chosenBasis R A)).repr (g (P.val x.1)) x.2

private lemma map_genericImage_coeffAssignment (g : B →ₐ[R] C ⊗[R] A) (i : ι) :
    Algebra.TensorProduct.map (MvPolynomial.aeval (coeffAssignment (P := P) g)) (AlgHom.id R A)
        (genericImage (R := R) (A := A) i) =
      g (P.val i) := by
  rw [genericImage, map_sum]
  simp only [Algebra.TensorProduct.map_tmul, MvPolynomial.aeval_X, AlgHom.coe_id, id_eq]
  calc
    ∑ j, coeffAssignment (P := P) g (i, j) ⊗ₜ[R] chosenBasis R A j =
        ∑ j, coeffAssignment (P := P) g (i, j) •
          (Algebra.TensorProduct.basis C (chosenBasis R A) j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Algebra.TensorProduct.basis_apply]
      simpa only [smul_eq_mul, mul_one] using
        (TensorProduct.smul_tmul' (R := R) (coeffAssignment (P := P) g (i, j))
          (1 : C) (chosenBasis R A j)).symm
    _ = g (P.val i) :=
      (Algebra.TensorProduct.basis C (chosenBasis R A)).sum_repr (g (P.val i))

private lemma aeval_relationCoeff_coeffAssignment (g : B →ₐ[R] C ⊗[R] A)
    (s : σ) (j : BasisIndex R A) :
    MvPolynomial.aeval (coeffAssignment (P := P) g)
      (relationCoeff (P := P) s j) = 0 := by
  rw [relationCoeff, ← basis_repr_map]
  rw [MvPolynomial.comp_aeval_apply]
  simp_rw [map_genericImage_coeffAssignment (P := P) g]
  rw [← MvPolynomial.comp_aeval_apply (f := P.val) g (P.relation s)]
  rw [P.aeval_val_relation, map_zero]
  rfl

private lemma relationsIdeal_le_ker_coeffAssignment (g : B →ₐ[R] C ⊗[R] A) :
    relationsIdeal (P := P) ≤
      RingHom.ker (MvPolynomial.aeval (coeffAssignment (P := P) g)).toRingHom := by
  rw [relationsIdeal, Ideal.span_le]
  rintro x ⟨⟨s, j⟩, rfl⟩
  change MvPolynomial.aeval (coeffAssignment (P := P) g)
    (relationCoeff (R := R) (A := A) (B := B) P s j) = 0
  exact aeval_relationCoeff_coeffAssignment (P := P) g s j

private def liftCoefficients (g : B →ₐ[R] C ⊗[R] A) :
    HomRing (R := R) (A := A) (B := B) P →ₐ[R] C :=
  Ideal.Quotient.liftₐ (relationsIdeal (R := R) (A := A) (B := B) P)
    (MvPolynomial.aeval (coeffAssignment (P := P) g))
    (fun _ hx ↦ RingHom.mem_ker.mp
      (relationsIdeal_le_ker_coeffAssignment (P := P) g hx))

private def homForward (h : HomRing (R := R) (A := A) (B := B) P →ₐ[R] C) :
    B →ₐ[R] C ⊗[R] A :=
  (Algebra.TensorProduct.map h (AlgHom.id R A)).comp
    (universal (R := R) (A := A) (B := B) P)

private lemma homForward_liftCoefficients (g : B →ₐ[R] C ⊗[R] A) :
    homForward (P := P) (liftCoefficients (P := P) g) = g := by
  apply AlgHom.ext
  intro x
  rw [← P.aeval_val_σ x]
  rw [MvPolynomial.comp_aeval_apply (f := P.val)
    (homForward (P := P) (liftCoefficients (P := P) g))]
  rw [MvPolynomial.comp_aeval_apply (f := P.val) g]
  apply AlgHom.congr_fun (x := P.σ x)
  apply MvPolynomial.algHom_ext
  intro i
  simp only [MvPolynomial.aeval_X]
  change Algebra.TensorProduct.map (liftCoefficients (P := P) g) (AlgHom.id R A)
      (universal (R := R) (A := A) (B := B) P (P.val i)) = g (P.val i)
  rw [universal_val]
  change Algebra.TensorProduct.map
      (Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (coeffAssignment (P := P) g)) _)
      (AlgHom.id R A) (quotientImage (R := R) (A := A) (B := B) P i) = _
  rw [quotientImage]
  change ((Algebra.TensorProduct.map
      (Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (coeffAssignment (P := P) g)) _)
      (AlgHom.id R A)).comp
    (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R _) (AlgHom.id R A)))
      (genericImage (R := R) (A := A) i) = _
  rw [← Algebra.TensorProduct.map_comp]
  simpa only [AlgHom.comp_id, Ideal.Quotient.liftₐ_comp] using
    map_genericImage_coeffAssignment (P := P) g i

private lemma coeffAssignment_homForward
    (h : HomRing (R := R) (A := A) (B := B) P →ₐ[R] C)
    (i : ι) (j : BasisIndex R A) :
    coeffAssignment (P := P) (homForward (P := P) h) (i, j) =
      h (Ideal.Quotient.mkₐ R (relationsIdeal (R := R) (A := A) (B := B) P)
        (MvPolynomial.X (i, j))) := by
  change (Algebra.TensorProduct.basis C (chosenBasis R A)).repr
    (Algebra.TensorProduct.map h (AlgHom.id R A)
      (universal (R := R) (A := A) (B := B) P (P.val i))) j = _
  rw [universal_val, basis_repr_map, quotientImage, basis_repr_map, genericImage_coeff]

private lemma liftCoefficients_homForward
    (h : HomRing (R := R) (A := A) (B := B) P →ₐ[R] C) :
    liftCoefficients (P := P) (homForward (P := P) h) = h := by
  apply Ideal.Quotient.algHom_ext
  unfold liftCoefficients
  rw [Ideal.Quotient.liftₐ_comp]
  apply MvPolynomial.algHom_ext
  intro x
  rw [MvPolynomial.aeval_X]
  exact coeffAssignment_homForward (P := P) h x.1 x.2

private def weilHomEquiv :
    (HomRing (R := R) (A := A) (B := B) P →ₐ[R] C) ≃
      (B →ₐ[R] C ⊗[R] A) where
  toFun := homForward (P := P)
  invFun := liftCoefficients (P := P)
  left_inv := liftCoefficients_homForward (P := P)
  right_inv := homForward_liftCoefficients (P := P)

private lemma homForward_comp
    {D : Type u} [CommRing D] [Algebra R D]
    (h : HomRing (R := R) (A := A) (B := B) P →ₐ[R] C)
    (k : C →ₐ[R] D) :
    homForward (P := P) (k.comp h) =
      (Algebra.TensorProduct.map k (AlgHom.id R A)).comp
        (homForward (P := P) h) := by
  unfold homForward
  rw [← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp]
  simp

private def categoryWeilHomEquiv (S : CommAlgCat.{u} R) :
    (CommAlgCat.of R (HomRing (R := R) (A := A) (B := B) P) ⟶ S) ≃
      (CommAlgCat.of R B ⟶
        (MonoidalCategory.tensorRight (CommAlgCat.of R A)).obj S) where
  toFun f := CommAlgCat.ofHom (homForward (P := P) f.hom)
  invFun g := CommAlgCat.ofHom (liftCoefficients (P := P) g.hom)
  left_inv f := by
    apply CommAlgCat.hom_ext
    exact liftCoefficients_homForward (P := P) f.hom
  right_inv g := by
    apply CommAlgCat.hom_ext
    exact homForward_liftCoefficients (P := P) g.hom

private lemma categoryWeilHomEquiv_comp {S T : CommAlgCat.{u} R}
    (f : CommAlgCat.of R (HomRing (R := R) (A := A) (B := B) P) ⟶ S)
    (g : S ⟶ T) :
    categoryWeilHomEquiv (P := P) T (f ≫ g) =
      categoryWeilHomEquiv (P := P) S f ≫
        (MonoidalCategory.tensorRight (CommAlgCat.of R A)).map g := by
  apply CommAlgCat.hom_ext
  change homForward (P := P) (g.hom.comp f.hom) =
    (Algebra.TensorProduct.map g.hom (AlgHom.id R A)).comp
      (homForward (P := P) f.hom)
  exact homForward_comp (P := P) f.hom g.hom

private def corepresentableBy :
    ((MonoidalCategory.tensorRight (CommAlgCat.of R A)) ⋙
      coyoneda.obj (Opposite.op (CommAlgCat.of R B))).CorepresentableBy
        (CommAlgCat.of R (HomRing (R := R) (A := A) (B := B) P)) where
  homEquiv {Y} := categoryWeilHomEquiv (P := P) Y
  homEquiv_comp g f := categoryWeilHomEquiv_comp (P := P) f g

private lemma leftAdjointObjIsDefined (P : Algebra.Presentation R B ι σ) :
    (MonoidalCategory.tensorRight (CommAlgCat.of R A)).leftAdjointObjIsDefined
      (CommAlgCat.of R B) :=
  (corepresentableBy (P := P)).isCorepresentable

/--
If `A` is finite free over `R` and `B` is finitely presented over `R`,
then tensoring commutative `R`-algebras with `A` has a left-adjoint object
at `B`. Equivalently, the functor
`C ↦ Hom_R(B, C ⊗[R] A)` is corepresentable.

This is the affine source lemma for the relative internal Hom in Stacks
Project, Tag `0BL7`.
-/
theorem tensorRight_leftAdjointObjIsDefined
    [Algebra.FinitePresentation R B] :
    (MonoidalCategory.tensorRight (CommAlgCat.of R A)).leftAdjointObjIsDefined
      (CommAlgCat.of R B) :=
  let P := (Algebra.Presentation.ofFinitePresentation R B).reindex
    Equiv.ulift.{u, 0} Equiv.ulift.{u, 0}
  leftAdjointObjIsDefined (P := P)

end CommAlgCat
