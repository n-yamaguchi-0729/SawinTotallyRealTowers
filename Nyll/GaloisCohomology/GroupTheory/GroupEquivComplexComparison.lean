/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import Mathlib.Data.Finsupp.Ext
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingHomologyEquivalence

/-!
# The actual complexes under a group and coefficient equivalence

Cochains are reindexed along the inverse group equivalence; chains are reindexed along the
forward equivalence. Both use the supplied equivariant linear equivalence on coefficients.
The finite norm comparison joins these maps into a comparison of the entire Tate complex,
including the map from degree minus one to degree zero.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

variable {R G H : Type u} [CommRing R] [Group G] [Group H]
  {A : Rep.{u} R G} {B : Rep.{u} R H}
  (e : G ≃* H) (l : A.V ≃ₗ[R] B.V)
  (hl : ∀ g, l.toLinearMap ∘ₗ A.ρ g = B.ρ (e g) ∘ₗ l.toLinearMap)

namespace Rep

include hl in
/-- The inverse of the supplied equivariant coefficient equivalence has the inverse action. -/
theorem groupEquiv_inverse_comm (h : H) :
    l.symm.toLinearMap ∘ₗ B.ρ h = A.ρ (e.symm h) ∘ₗ l.symm.toLinearMap := by
  apply LinearMap.ext
  intro b
  apply l.injective
  change l (l.symm (B.ρ h b)) = l (A.ρ (e.symm h) (l.symm b))
  rw [l.apply_symm_apply]
  have hb := LinearMap.congr_fun (hl (e.symm h)) (l.symm b)
  change l (A.ρ (e.symm h) (l.symm b)) = B.ρ (e (e.symm h)) (l (l.symm b)) at hb
  rw [e.apply_symm_apply, l.apply_symm_apply] at hb
  exact hb.symm

include hl in
/-- The supplied equivalences identify the actual finite representation norms. -/
theorem groupEquiv_norm [Fintype G] [Fintype H] (a : A) :
    l (A.ρ.norm a) = B.ρ.norm (l a) := by
  unfold Representation.norm
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Fintype.sum_equiv e.toEquiv _ _ (fun g => LinearMap.congr_fun (hl g) a)

end Rep

namespace groupCohomology

/-- Actual cochain reindexing and coefficient equivalence, using the native cochain maps. -/
def groupEquivComplexIso : inhomogeneousCochains A ≅ inhomogeneousCochains B where
  hom := cochainsMap e.symm.toMonoidHom (Rep.ofHom ⟨l.toLinearMap, fun h => by
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.apply_symm_apply]
      using hl (e.symm h)⟩)
  inv := cochainsMap e.toMonoidHom (Rep.ofHom ⟨l.symm.toLinearMap, fun g => by
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using
      Rep.groupEquiv_inverse_comm e l hl (e g)⟩)
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply funext
    intro g
    change l.symm (l (f (fun i => e.symm (e (g i))))) = f g
    rw [l.symm_apply_apply]
    congr 1
    funext i
    exact e.symm_apply_apply (g i)
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply funext
    intro h
    change l (l.symm (f (fun i => e (e.symm (h i))))) = f h
    rw [l.apply_symm_apply]
    congr 1
    funext i
    exact e.apply_symm_apply (h i)

/-- The cochain comparison applies the original coefficient equivalence after reindexing. -/
theorem groupEquivComplexIso_hom_f_apply (n : ℕ) (f : (Fin n → G) → A)
    (h : Fin n → H) :
    (groupEquivComplexIso e l hl).hom.f n f h = l (f (e.symm ∘ h)) := rfl

/-- The inverse comparison reverses the same reindexing and coefficient map. -/
theorem groupEquivComplexIso_inv_f_apply (n : ℕ) (f : (Fin n → H) → B)
    (g : Fin n → G) :
    (groupEquivComplexIso e l hl).inv.f n f g = l.symm (f (e ∘ g)) := rfl

end groupCohomology

namespace groupHomology

/-- Actual chain reindexing and coefficient equivalence, using the native chain maps. -/
def groupEquivComplexIso : inhomogeneousChains A ≅ inhomogeneousChains B where
  hom := chainsMap e.toMonoidHom (Rep.ofHom ⟨l.toLinearMap, hl⟩)
  inv := chainsMap e.symm.toMonoidHom
    (Rep.ofHom ⟨l.symm.toLinearMap, Rep.groupEquiv_inverse_comm e l hl⟩)
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply Finsupp.addHom_ext
    intro g a
    change (chainsMap e.symm.toMonoidHom
        (Rep.ofHom ⟨l.symm.toLinearMap, Rep.groupEquiv_inverse_comm e l hl⟩)).f n
        ((chainsMap e.toMonoidHom (Rep.ofHom ⟨l.toLinearMap, hl⟩)).f n
          (Finsupp.single g a)) = Finsupp.single g a
    rw [chainsMap_f_single, chainsMap_f_single]
    change Finsupp.single (fun i => e.symm (e (g i))) (l.symm (l a)) =
      Finsupp.single g a
    rw [l.symm_apply_apply]
    congr 1
    funext i
    exact e.symm_apply_apply (g i)
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply Finsupp.addHom_ext
    intro h b
    change (chainsMap e.toMonoidHom (Rep.ofHom ⟨l.toLinearMap, hl⟩)).f n
        ((chainsMap e.symm.toMonoidHom
          (Rep.ofHom ⟨l.symm.toLinearMap, Rep.groupEquiv_inverse_comm e l hl⟩)).f n
          (Finsupp.single h b)) = Finsupp.single h b
    rw [chainsMap_f_single, chainsMap_f_single]
    change Finsupp.single (fun i => e (e.symm (h i))) (l (l.symm b)) =
      Finsupp.single h b
    rw [l.apply_symm_apply]
    congr 1
    funext i
    exact e.apply_symm_apply (h i)

/-- The chain comparison sends each actual generator to its reindexed coefficient image. -/
theorem groupEquivComplexIso_hom_f_single (n : ℕ) (g : Fin n → G) (a : A) :
    (groupEquivComplexIso e l hl).hom.f n (Finsupp.single g a) =
      Finsupp.single (e ∘ g) (l a) :=
  chainsMap_f_single e.toMonoidHom (Rep.ofHom ⟨l.toLinearMap, hl⟩) n g a

/-- The inverse chain comparison reverses that same generator map. -/
theorem groupEquivComplexIso_inv_f_single (n : ℕ) (h : Fin n → H) (b : B) :
    (groupEquivComplexIso e l hl).inv.f n (Finsupp.single h b) =
      Finsupp.single (e.symm ∘ h) (l.symm b) :=
  chainsMap_f_single e.symm.toMonoidHom
    (Rep.ofHom ⟨l.symm.toLinearMap, Rep.groupEquiv_inverse_comm e l hl⟩) n h b

end groupHomology

namespace TateCohomology

variable [Fintype G] [Fintype H]

/-- Chain and cochain reindexing commute with the actual connecting Tate norm. -/
theorem groupEquiv_tateNorm :
    (groupHomology.groupEquivComplexIso e l hl).hom.f 0 ≫ B.tateNorm =
      A.tateNorm ≫ (groupCohomology.groupEquivComplexIso e l hl).hom.f 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply Finsupp.addHom_ext
  intro g a
  apply funext
  intro h
  change B.tateNorm
      ((groupHomology.groupEquivComplexIso e l hl).hom.f 0 (Finsupp.single g a)) h =
    (groupCohomology.groupEquivComplexIso e l hl).hom.f 0
      (A.tateNorm (Finsupp.single g a)) h
  rw [groupHomology.groupEquivComplexIso_hom_f_single,
    groupCohomology.groupEquivComplexIso_hom_f_apply]
  exact (Rep.tateNorm_single_apply B (e ∘ g) h (l a)).trans
    ((Rep.groupEquiv_norm e l hl a).symm.trans
      (congrArg l (Rep.tateNorm_single_apply A g (e.symm ∘ h) a)).symm)

/-- The actual Tate complexes agree under the given group and coefficient equivalences. -/
def groupEquivComplexIso : tateComplex A ≅ tateComplex B := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i => ?_) ?_
  · cases i with
    | ofNat n =>
      exact HomologicalComplex.Hom.isoApp (groupCohomology.groupEquivComplexIso e l hl) n
    | negSucc n =>
      exact HomologicalComplex.Hom.isoApp (groupHomology.groupEquivComplexIso e l hl) n
  · rintro (n | (_ | n)) _ rfl
    · exact (groupCohomology.groupEquivComplexIso e l hl).hom.comm n (n + 1)
    · exact groupEquiv_tateNorm e l hl
    · have hindex : Int.negSucc (n + 1) + 1 = Int.negSucc n := by
        rw [← Int.negSucc_sub_one n, sub_add_cancel]
      rw [hindex]
      exact (groupHomology.groupEquivComplexIso e l hl).hom.comm (n + 1) n

/-- The Tate comparison is the original cochain map in nonnegative degrees. -/
theorem groupEquivComplexIso_hom_f_ofNat_apply (n : ℕ) (f : (Fin n → G) → A)
    (h : Fin n → H) :
    (groupEquivComplexIso e l hl).hom.f (.ofNat n) f h = l (f (e.symm ∘ h)) := rfl

/-- The Tate comparison is the original chain map on generators in negative degrees. -/
theorem groupEquivComplexIso_hom_f_negSucc_single (n : ℕ) (g : Fin n → G) (a : A) :
    (groupEquivComplexIso e l hl).hom.f (.negSucc n) (Finsupp.single g a) =
      Finsupp.single (e ∘ g) (l a) :=
  groupHomology.groupEquivComplexIso_hom_f_single e l hl n g a

/-- Actual group and coefficient equivalences induce the Tate comparison in every degree. -/
def groupEquivIso (n : ℤ) : tateCohomology A n ≅ tateCohomology B n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).mapIso
    (groupEquivComplexIso e l hl)

end TateCohomology
