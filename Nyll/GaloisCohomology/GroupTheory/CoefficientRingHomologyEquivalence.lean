/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Finsupp.Ext
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingEquivalence
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Coefficient ring equivalences for homology and Tate cohomology

The comparisons use the original finitely supported chains, function-valued cochains,
representation action and norm. They identify the actual native Mathlib complexes;
no substitute homology object or comparison hypothesis is introduced.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace Rep

/-- The actual connecting Tate norm on a single chain is the representation norm. -/
theorem tateNorm_single_apply {R G : Type u} [CommRing R] [Group G] [Fintype G]
    (A : Rep.{u} R G) (g h : Fin 0 → G) (a : A) :
    A.tateNorm (Finsupp.single g a) h = A.ρ.norm a := by
  rw [Rep.tateNorm_eq]
  change (Finsupp.lsum R (fun _ : Fin 0 → G =>
    LinearMap.pi (fun _ : Fin 0 → G => A.ρ.norm))) (Finsupp.single g a) h = A.ρ.norm a
  exact congrArg (fun f : (Fin 0 → G) → A => f h)
    (Finsupp.lsum_single R (fun _ : Fin 0 → G =>
      LinearMap.pi (fun _ : Fin 0 → G => A.ρ.norm)) g a)

end Rep

namespace groupHomology

variable {R S G : Type u} [CommRing R] [CommRing S] [Group G]
  (e : R ≃+* S) (A : Rep.{u} S G)

/-- Pointwise identity on finitely supported chains after coefficient restriction. -/
def coefficientRingChainsIso (n : ℕ) :
    (ModuleCat.restrictScalars e.toRingHom).obj ((inhomogeneousChains A).X n) ≅
      (inhomogeneousChains ((Rep.coefficientRingEquivalence e G).functor.obj A)).X n :=
  LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.restrictScalars e.toRingHom).obj ((inhomogeneousChains A).X n))
    (X₂ := (inhomogeneousChains
      ((Rep.coefficientRingEquivalence e G).functor.obj A)).X n)
    (m₁ := ((ModuleCat.restrictScalars e.toRingHom).obj
      ((inhomogeneousChains A).X n)).isModule)
    (m₂ := ((inhomogeneousChains
      ((Rep.coefficientRingEquivalence e G).functor.obj A)).X n).isModule)
    { toFun := fun f => f
      invFun := fun f => f
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The native chain complexes agree under restriction along a ring equivalence. -/
def coefficientRingComplexIso :
    ((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (inhomogeneousChains A) ≅
        inhomogeneousChains ((Rep.coefficientRingEquivalence e G).functor.obj A) := by
  refine HomologicalComplex.Hom.isoOfComponents (coefficientRingChainsIso e A) ?_
  intro i j hij
  change j + 1 = i at hij
  subst i
  change (coefficientRingChainsIso e A (j + 1)).hom ≫
      (inhomogeneousChains
        ((Rep.coefficientRingEquivalence e G).functor.obj A)).d (j + 1) j =
    (ModuleCat.restrictScalars e.toRingHom).map
      ((inhomogeneousChains A).d (j + 1) j) ≫ (coefficientRingChainsIso e A j).hom
  rw [inhomogeneousChains.d_def, inhomogeneousChains.d_def]
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply Finsupp.addHom_ext
  intro g a
  change inhomogeneousChains.d ((Rep.coefficientRingEquivalence e G).functor.obj A) j
      (Finsupp.single g a) = inhomogeneousChains.d A j (Finsupp.single g a)
  refine (inhomogeneousChains.d_single
    (A := (Rep.coefficientRingEquivalence e G).functor.obj A) j g a).trans ?_
  refine Eq.trans ?_ (inhomogeneousChains.d_single (A := A) j g a).symm
  change Finsupp.single (fun i => g i.succ) (A.ρ (g 0)⁻¹ a) +
      ∑ i : Fin (j + 1), e ((-1 : R) ^ ((i : ℕ) + 1)) •
        Finsupp.single (Fin.contractNth i (· * ·) g) a =
    Finsupp.single (fun i => g i.succ) (A.ρ (g 0)⁻¹ a) +
      ∑ i : Fin (j + 1), (-1 : S) ^ ((i : ℕ) + 1) •
        Finsupp.single (Fin.contractNth i (· * ·) g) a
  apply congrArg (fun x : (Fin j → G) →₀ A =>
    Finsupp.single (fun i : Fin j => g i.succ) (A.ρ (g 0)⁻¹ a) + x)
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_pow, map_neg, map_one]

/-- Each chain remains the original finitely supported function. -/
theorem coefficientRingComplexIso_hom_f_apply (n : ℕ) (f : (Fin n → G) →₀ A) :
    (coefficientRingComplexIso e A).hom.f n f = f := rfl

/-- The inverse comparison also keeps every chain unchanged. -/
theorem coefficientRingComplexIso_inv_f_apply (n : ℕ) (f : (Fin n → G) →₀ A) :
    (coefficientRingComplexIso e A).inv.f n f = f := rfl

/-- Coefficient restriction identifies the actual group homology objects in every degree. -/
def coefficientRingIso (n : ℕ) :
    (ModuleCat.restrictScalars e.toRingHom).obj (groupHomology A n) ≅
      groupHomology ((Rep.coefficientRingEquivalence e G).functor.obj A) n :=
  (((inhomogeneousChains A).sc n).mapHomologyIso
      (ModuleCat.restrictScalars e.toRingHom)).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n).mapIso
      (coefficientRingComplexIso e A)

end groupHomology

namespace TateCohomology

variable {R S G : Type u} [CommRing R] [CommRing S] [Group G] [Fintype G]
  (e : R ≃+* S) (A : Rep.{u} S G)

/-- The connecting norm in the Tate complex is the original representation norm. -/
theorem coefficientRing_tateNorm :
    (groupHomology.coefficientRingChainsIso e A 0).hom ≫
        ((Rep.coefficientRingEquivalence e G).functor.obj A).tateNorm =
      (ModuleCat.restrictScalars e.toRingHom).map A.tateNorm ≫
        (groupCohomology.coefficientRingCochainsIso e A 0).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply Finsupp.addHom_ext
  intro g a
  apply funext
  intro h
  change ((Rep.coefficientRingEquivalence e G).functor.obj A).tateNorm
      (Finsupp.single g a) h = A.tateNorm (Finsupp.single g a) h
  exact (Rep.tateNorm_single_apply ((Rep.coefficientRingEquivalence e G).functor.obj A)
    g h a).trans ((Rep.coefficientRingEquivalence_obj_norm_apply e G A a).trans
      (Rep.tateNorm_single_apply A g h a).symm)

/-- The native Tate complexes agree in all degrees, including the connecting norm. -/
def coefficientRingComplexIso :
    ((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (tateComplex A) ≅
        tateComplex ((Rep.coefficientRingEquivalence e G).functor.obj A) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i => ?_) ?_
  · cases i with
    | ofNat n => exact groupCohomology.coefficientRingCochainsIso e A n
    | negSucc n => exact groupHomology.coefficientRingChainsIso e A n
  · rintro (n | (_ | n)) _ rfl
    · exact (groupCohomology.coefficientRingComplexIso e A).hom.comm n (n + 1)
    · exact coefficientRing_tateNorm e A
    · have hindex : Int.negSucc (n + 1) + 1 = Int.negSucc n := by
        rw [← Int.negSucc_sub_one n, sub_add_cancel]
      rw [hindex]
      exact (groupHomology.coefficientRingComplexIso e A).hom.comm (n + 1) n

/-- The nonnegative Tate comparison is identity on the original cochains. -/
theorem coefficientRingComplexIso_hom_f_ofNat_apply (n : ℕ) (f : (Fin n → G) → A) :
    (coefficientRingComplexIso e A).hom.f (.ofNat n) f = f := rfl

/-- The negative Tate comparison is identity on the original chains. -/
theorem coefficientRingComplexIso_hom_f_negSucc_apply (n : ℕ) (f : (Fin n → G) →₀ A) :
    (coefficientRingComplexIso e A).hom.f (.negSucc n) f = f := rfl

/-- Coefficient restriction identifies the actual Tate cohomology objects in every degree. -/
def coefficientRingIso (n : ℤ) :
    (ModuleCat.restrictScalars e.toRingHom).obj (tateCohomology A n) ≅
      tateCohomology ((Rep.coefficientRingEquivalence e G).functor.obj A) n :=
  (((tateComplex A).sc n).mapHomologyIso
      (ModuleCat.restrictScalars e.toRingHom)).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).mapIso
      (coefficientRingComplexIso e A)

end TateCohomology


namespace CategoryTheory.ShortComplex

/-- Restricting scalars and mapping homology preserves the class of the same cycle. -/
theorem restrictScalars_homologyClass
    {R S : Type} [CommRing R] [CommRing S] (r : R →+* S)
    (C : ShortComplex (ModuleCat S)) (D : ShortComplex (ModuleCat R))
    (f : C.map (ModuleCat.restrictScalars r) ⟶ D)
    (z : LinearMap.ker C.g.hom) (w : LinearMap.ker D.g.hom)
    (hzw : f.τ₂ z.val = w.val) :
    homologyMap f
        ((C.mapHomologyIso (ModuleCat.restrictScalars r)).inv
          (C.moduleCatHomologyIso.inv (Submodule.Quotient.mk z))) =
      D.moduleCatHomologyIso.inv (Submodule.Quotient.mk w) := by
  let F := ModuleCat.restrictScalars r
  let hC := C.moduleCatLeftHomologyData
  let hD := D.moduleCatLeftHomologyData
  let hM := hC.map F
  have hcycle : cyclesMap' f hM hD z = w := by
    apply Subtype.ext
    exact (congrArg (fun m => m z) (cyclesMap'_i f hM hD)).trans hzw
  have hroute :
      F.map hC.homologyIso.inv ≫ (C.mapHomologyIso F).inv ≫
          homologyMap f ≫ hD.homologyIso.hom =
        hM.homologyIso.inv ≫ homologyMap f ≫ hD.homologyIso.hom := by
    have heq := congrArg
      (fun e => F.map hC.homologyIso.inv ≫ e.inv ≫
        homologyMap f ≫ hD.homologyIso.hom) (hC.mapHomologyIso_eq F)
    refine heq.trans ?_
    let e := F.mapIso hC.homologyIso
    change e.inv ≫ (e.hom ≫ hM.homologyIso.inv) ≫
      homologyMap f ≫ hD.homologyIso.hom = _
    exact (congrArg (fun m => e.inv ≫ m)
      (Category.assoc e.hom hM.homologyIso.inv
        (homologyMap f ≫ hD.homologyIso.hom))).trans
      (e.inv_hom_id_assoc _)
  have hmap :
      hM.homologyIso.inv ≫ homologyMap f ≫ hD.homologyIso.hom =
        leftHomologyMap' f hM hD := by
    exact (hM.leftHomologyIso_inv_naturality_assoc f hD hD.homologyIso.hom).trans
      (by simp only [Iso.inv_hom_id, Category.comp_id])
  apply (ModuleCat.mono_iff_injective hD.homologyIso.hom).mp inferInstance
  have h :
      (F.map hC.homologyIso.inv ≫ (C.mapHomologyIso F).inv ≫
          homologyMap f ≫ hD.homologyIso.hom) (hC.π z) = hD.π w := by
    rw [hroute, hmap]
    exact (congrArg (fun m => m z) (leftHomologyπ_naturality' f hM hD)).trans
      (congrArg hD.π hcycle)
  exact h.trans (hD.homologyIso.inv_hom_id_apply (hD.π w)).symm

end CategoryTheory.ShortComplex
