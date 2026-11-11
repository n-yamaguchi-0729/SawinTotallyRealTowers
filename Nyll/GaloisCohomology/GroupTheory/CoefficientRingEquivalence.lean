/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Rep.Res
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Coefficient ring equivalences for representations and group cohomology

Restriction along a ring equivalence preserves the underlying additive group,
the group action, and every equivariant map. In particular, restriction along
`ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ` supplies the same integer representation
over a coefficient ring in universe `u`. The cochain comparison below proves
compatibility with ordinary group cohomology whenever both native cohomology
objects are defined, including the original universe-zero integer API.
-/

@[expose] public section

noncomputable section

universe u v v' w uR uS

open CategoryTheory

namespace Rep

section Coefficients

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
  (e : R ≃+* S) (G : Type v) [Monoid G]

/-- Restriction of representation coefficients along a ring equivalence,
using the existing equivalence of module categories. -/
def coefficientRingEquivalence : Rep.{w} S G ≌ Rep.{w} R G :=
  (repIsoAction S G).trans
    (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).mapAction G).trans
      (repIsoAction R G).symm)

/-- The coefficient transport retains the original carrier. -/
theorem coefficientRingEquivalence_obj_V (A : Rep.{w} S G) :
    ((coefficientRingEquivalence e G).functor.obj A).V = A.V := rfl

/-- Scalars act through the given ring equivalence. -/
theorem coefficientRingEquivalence_obj_smul (A : Rep.{w} S G) (r : R) (a : A) :
    @SMul.smul R ((coefficientRingEquivalence e G).functor.obj A)
      ((coefficientRingEquivalence e G).functor.obj A).hV2.toSMul r a = e r • a := rfl

/-- The actual group action is unchanged by coefficient transport. -/
theorem coefficientRingEquivalence_obj_ρ_apply (A : Rep.{w} S G) (g : G) (a : A) :
    ((coefficientRingEquivalence e G).functor.obj A).ρ g a = A.ρ g a := rfl

/-- Equivariant coefficient maps retain their original underlying functions. -/
theorem coefficientRingEquivalence_map_apply {A B : Rep.{w} S G}
    (f : A ⟶ B) (a : A) :
    ((coefficientRingEquivalence e G).functor.map f) a = f a := rfl

variable {G} in
/-- Scalar restriction commutes with restriction of the acting group,
with the same carrier and the same scalar-module owner on both sides. -/
theorem coefficientRingEquivalence_res_obj {H : Type v'} [Monoid H]
    (q : H →* G) (B : Rep.{w} S G) :
    (coefficientRingEquivalence e H).functor.obj (res q B) =
      res q ((coefficientRingEquivalence e G).functor.obj B) := rfl

instance coefficientRingEquivalence_additive :
    (coefficientRingEquivalence e G : Rep.{w} S G ≌ Rep.{w} R G).functor.Additive where
  map_add := by
    intro A B f g
    ext a
    rfl

end Coefficients

section Norm

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
  (e : R ≃+* S) (G : Type v) [Group G] [Fintype G]

/-- The actual representation norm has the original value after scalar transport. -/
theorem coefficientRingEquivalence_obj_norm_apply (B : Rep.{w} S G) (b : B) :
    (((coefficientRingEquivalence e G).functor.obj B).norm).asHom.hom b = B.norm.asHom.hom b := by
  change ((coefficientRingEquivalence e G).functor.obj B).ρ.norm b = B.ρ.norm b
  have hnorm : (((coefficientRingEquivalence e G).functor.obj B).ρ.norm b : B) =
      ∑ g : G, B.ρ g b :=
    LinearMap.sum_apply _
      (fun g : G => ((coefficientRingEquivalence e G).functor.obj B).ρ g) b
  exact hnorm.trans (LinearMap.sum_apply _ (fun g : G => B.ρ g) b).symm

end Norm

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  (e : R ≃+* S) (G : Type v) [Group G]

/-- Invariants commute naturally with the same coefficient transport. -/
def coefficientRingInvariantsNatIso :
    (invariantsFunctor S G : Rep.{w} S G ⥤ ModuleCat.{w} S) ⋙
        ModuleCat.restrictScalars e.toRingHom ≅
      (coefficientRingEquivalence e G).functor ⋙ invariantsFunctor R G :=
  NatIso.ofComponents (fun A =>
    LinearEquiv.toModuleIso
      (X₁ := (ModuleCat.restrictScalars e.toRingHom).obj ((invariantsFunctor S G).obj A))
      (X₂ := (invariantsFunctor R G).obj ((coefficientRingEquivalence e G).functor.obj A))
      (m₁ := ((ModuleCat.restrictScalars e.toRingHom).obj
        ((invariantsFunctor S G).obj A)).isModule)
      (m₂ := ((invariantsFunctor R G).obj
        ((coefficientRingEquivalence e G).functor.obj A)).isModule)
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }) (by
    intro A B f
    ext x
    rfl)

end Rep

namespace ModuleCat

variable {R : Type uR} [Ring R] (e : R ≃+* ℤ)

/-- An additive map of integer modules is linear after the same scalar
restriction, using the supplied module structures on its source and target. -/
def coefficientRingAddHom {M N : ModuleCat.{w} ℤ} (f : M →+ N) :
    (restrictScalars e.toRingHom).obj M ⟶ (restrictScalars e.toRingHom).obj N :=
  (restrictScalars e.toRingHom).map (ofHom
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun n x => map_intCast_smul f ℤ ℤ n x })

/-- The linear adapter evaluates to the original additive map. -/
theorem coefficientRingAddHom_apply {M N : ModuleCat.{w} ℤ} (f : M →+ N) (x : M) :
    coefficientRingAddHom e f x = f x := rfl

end ModuleCat

namespace groupCohomology

section ScalarFormula

variable {R G : Type u} {S : Type uS} [CommRing R] [Ring S] [Group G]
  (e : R ≃+* S) (A : Rep.{u} S G)

/-- The native degree-one coboundary uses exactly the original additive
coefficient group and its original action, even when `S` is in another universe. -/
theorem coefficientRing_d₁₂_apply (f : G → A) (g h : G) :
    d₁₂ ((Rep.coefficientRingEquivalence e G).functor.obj A) f (g, h) =
      A.ρ g (f h) - f (g * h) + f g := rfl

end ScalarFormula

variable {R S G : Type u} [CommRing R] [CommRing S] [Group G]
  (e : R ≃+* S) (A : Rep.{u} S G)

/-- Pointwise identity on cochains, with the scalar structure supplied by
restriction along the ring equivalence. -/
def coefficientRingCochainsIso (n : ℕ) :
    (ModuleCat.restrictScalars e.toRingHom).obj ((inhomogeneousCochains A).X n) ≅
      (inhomogeneousCochains ((Rep.coefficientRingEquivalence e G).functor.obj A)).X n :=
  LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.restrictScalars e.toRingHom).obj ((inhomogeneousCochains A).X n))
    (X₂ := (inhomogeneousCochains
      ((Rep.coefficientRingEquivalence e G).functor.obj A)).X n)
    (m₁ := ((ModuleCat.restrictScalars e.toRingHom).obj
      ((inhomogeneousCochains A).X n)).isModule)
    (m₂ := ((inhomogeneousCochains
      ((Rep.coefficientRingEquivalence e G).functor.obj A)).X n).isModule)
    { toFun := fun f => f
      invFun := fun f => f
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The inhomogeneous complexes agree under the same coefficient restriction.
The comparison is the identity on coefficient-valued functions in every degree. -/
def coefficientRingComplexIso :
    ((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (inhomogeneousCochains A) ≅
        inhomogeneousCochains ((Rep.coefficientRingEquivalence e G).functor.obj A) := by
  refine HomologicalComplex.Hom.isoOfComponents (coefficientRingCochainsIso e A) ?_
  intro i j hij
  change i + 1 = j at hij
  subst j
  change (coefficientRingCochainsIso e A i).hom ≫
      (inhomogeneousCochains
        ((Rep.coefficientRingEquivalence e G).functor.obj A)).d i (i + 1) =
    (ModuleCat.restrictScalars e.toRingHom).map
      ((inhomogeneousCochains A).d i (i + 1)) ≫
        (coefficientRingCochainsIso e A (i + 1)).hom
  rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_def]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply funext
  intro g
  change A.ρ (g 0) (f fun j => g j.succ) +
      ∑ j : Fin (i + 1), e ((-1 : R) ^ ((j : ℕ) + 1)) •
        f (Fin.contractNth j (· * ·) g) =
    A.ρ (g 0) (f fun j => g j.succ) +
      ∑ j : Fin (i + 1), (-1 : S) ^ ((j : ℕ) + 1) •
        f (Fin.contractNth j (· * ·) g)
  apply congrArg (fun x => A.ρ (g 0) (f fun j => g j.succ) + x)
  apply Finset.sum_congr rfl
  intro j _hj
  rw [map_pow, map_neg, map_one]

/-- The complex comparison keeps each cochain unchanged. -/
theorem coefficientRingComplexIso_hom_f_apply (n : ℕ)
    (f : (Fin n → G) → A) :
    (coefficientRingComplexIso e A).hom.f n f = f := rfl

/-- The inverse complex comparison also keeps each cochain unchanged. -/
theorem coefficientRingComplexIso_inv_f_apply (n : ℕ)
    (f : (Fin n → G) → A) :
    (coefficientRingComplexIso e A).inv.f n f = f := rfl

/-- Coefficient restriction identifies the actual native cohomology objects.
For `u = 0`, this applies directly to the original integer-coefficient API
and to its lifted-integer version, in every degree. -/
def coefficientRingIso (n : ℕ) :
    (ModuleCat.restrictScalars e.toRingHom).obj (groupCohomology A n) ≅
      groupCohomology ((Rep.coefficientRingEquivalence e G).functor.obj A) n :=
  (((inhomogeneousCochains A).sc n).mapHomologyIso
      (ModuleCat.restrictScalars e.toRingHom)).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).mapIso
      (coefficientRingComplexIso e A)

end groupCohomology
