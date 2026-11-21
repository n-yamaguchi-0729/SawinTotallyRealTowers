/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.OrderOfElement
public import Nyll.GaloisCohomology.GroupTheory.InductionCounit
public import Nyll.GaloisCohomology.GroupTheory.ShapiroEvaluation

/-!
# Subgroup index annihilates H² when restricted H² vanishes

The coefficient trace is the existing finite-index coinduction-induction isomorphism
followed by the induction counit. Its composite with the coinduction unit is the index.
Shapiro then supplies the vanishing intermediate cohomology object.
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators

namespace ClassFieldTower.Cohomology

noncomputable section

universe r u v

section Trace

variable {R : Type r} {G : Type u} [CommRing R] [Group G]
  (A : Rep.{max r u v} R G) (H : Subgroup G) [H.FiniteIndex]

/-- The actual coefficient trace from the coinduced restricted representation. -/
def finiteIndexCoefficientTrace :
    Rep.coind H.subtype (Rep.res H.subtype A) ⟶ A := by
  classical
  exact (Rep.indCoindIso.{max r u v} (Rep.res H.subtype A)).inv ≫
    (Rep.indResHomEquiv.{max r u v} H.subtype (Rep.res H.subtype A) A).symm (𝟙 _)

/-- The existing coefficient trace commutes with morphisms of representations. -/
theorem finiteIndexCoefficientTrace_natural {B : Rep.{max r u v} R G} (f : A ⟶ B) :
    (Rep.coindFunctor R H.subtype).map ((Rep.resFunctor H.subtype).map f) ≫
        finiteIndexCoefficientTrace.{r, u, v} B H =
      finiteIndexCoefficientTrace.{r, u, v} A H ≫ f := by
  classical
  exact (Rep.coindResAdjunction.{max r u v} R H).counit.naturality f

/-- Coinduction followed by the coefficient trace is multiplication by the subgroup index. -/
theorem coinductionUnit_comp_finiteIndexCoefficientTrace :
    Rep.resCoindHomEquiv.{max r u v} H.subtype A (Rep.res H.subtype A) (𝟙 _) ≫
      finiteIndexCoefficientTrace.{r, u, v} A H = H.index • 𝟙 A := by
  classical
  let : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  let : Module R (Rep.res H.subtype A).V := (Rep.res H.subtype A).hV2
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  change ((Rep.indResHomEquiv.{max r u v} H.subtype (Rep.res H.subtype A) A).symm (𝟙 _)).hom
    (Rep.coindToInd (Rep.res H.subtype A)
      ((Rep.resCoindHomEquiv.{max r u v} H.subtype A (Rep.res H.subtype A) (𝟙 _)).hom a)) =
        H.index • a
  rw [Rep.coindToInd_apply, map_sum]
  trans ∑ _ : Quotient (QuotientGroup.rightRel H), a
  · apply Finset.sum_congr rfl
    intro q _
    induction q using Quotient.inductionOn with
    | h g =>
      change ((Rep.indResHomEquiv.{max r u v} H.subtype (Rep.res H.subtype A) A).symm (𝟙 _)).hom
        (Representation.IndV.mk H.subtype (Rep.res H.subtype A).ρ g (A.ρ g a)) = a
      rw [Rep.indResHomEquiv_symm_apply_mk]
      change A.ρ g⁻¹ (A.ρ g a) = a
      rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
  · rw [Finset.sum_const, Finset.card_univ, QuotientGroup.card_quotient_rightRel,
      ← Nat.card_eq_fintype_card, ← H.index_eq_card]

/-- Trace of a morphism defined after restriction to a finite-index subgroup. -/
def finiteIndexHomTrace (T : Rep.{max r u v} R G)
    (f : Rep.res H.subtype T ⟶ Rep.res H.subtype A) : T ⟶ A :=
  Rep.resCoindHomEquiv.{max r u v} H.subtype T (Rep.res H.subtype A) f ≫
    finiteIndexCoefficientTrace.{r, u, v} A H

/-- Tracing a restricted morphism commutes with its target morphisms. -/
theorem finiteIndexHomTrace_comp {B : Rep.{max r u v} R G} (T : Rep.{max r u v} R G)
    (f : Rep.res H.subtype T ⟶ Rep.res H.subtype A) (g : A ⟶ B) :
    finiteIndexHomTrace.{r, u, v} A H T f ≫ g =
      finiteIndexHomTrace.{r, u, v} B H T (f ≫ (Rep.resFunctor H.subtype).map g) := by
  unfold finiteIndexHomTrace
  rw [Category.assoc, ← finiteIndexCoefficientTrace_natural.{r, u, v}, ← Category.assoc]
  congr 1

/-- The trace of an ambient morphism restricted to the subgroup is its
index multiple. -/
theorem finiteIndexHomTrace_restriction (T : Rep.{max r u v} R G) (f : T ⟶ A) :
    finiteIndexHomTrace.{r, u, v} A H T ((Rep.resFunctor H.subtype).map f) =
      H.index • f := by
  have hu :
      Rep.resCoindHomEquiv.{max r u v} H.subtype T (Rep.res H.subtype A)
          ((Rep.resFunctor H.subtype).map f) =
        f ≫ Rep.resCoindHomEquiv.{max r u v} H.subtype A (Rep.res H.subtype A) (𝟙 _) := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext h
    exact Rep.hom_comm_apply f h x
  unfold finiteIndexHomTrace
  rw [hu, Category.assoc, coinductionUnit_comp_finiteIndexCoefficientTrace.{r, u, v}]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rfl

/-- An invariant image with a subgroup-invariant preimage has an ambient
invariant preimage after multiplication by the subgroup index. The sum over
actual cosets permits independent scalar, group, and coefficient universes. -/
theorem exists_invariant_index_preimage (A : Rep.{v} R G)
    {B : Rep.{v} R G} (d : A ⟶ B)
    (v : A) (hv : ∀ h : H, A.ρ (h : G) v = v)
    (hdv : ∀ g : G, B.ρ g (d.hom v) = d.hom v) :
    ∃ w : A, (∀ g : G, A.ρ g w = w) ∧
      d.hom w = H.index • d.hom v := by
  classical
  let : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  let f : G ⧸ H → A := Quotient.lift (fun g => A.ρ g v) (by
    intro g k h
    have hh := hv ⟨g⁻¹ * k, QuotientGroup.leftRel_apply.mp h⟩
    have he : A.ρ k v = A.ρ g v := by
      calc
        A.ρ k v = A.ρ (g * (g⁻¹ * k)) v := by rw [mul_inv_cancel_left]
        _ = A.ρ g (A.ρ (g⁻¹ * k) v) :=
          congrArg (fun t : Module.End R A => t v) (map_mul A.ρ g (g⁻¹ * k))
        _ = A.ρ g v := congrArg (A.ρ g) hh
    exact he.symm)
  have hf (g : G) (q : G ⧸ H) : A.ρ g (f q) = f (g • q) := by
    induction q using Quotient.inductionOn with
    | h k =>
      change A.ρ g (A.ρ k v) = A.ρ (g * k) v
      exact (congrArg (fun t : Module.End R A => t v) (map_mul A.ρ g k)).symm
  refine ⟨∑ q, f q, ?_, ?_⟩
  · intro g
    rw [map_sum]
    exact (Finset.sum_congr rfl (fun q _ => hf g q)).trans
      (Equiv.sum_comp (MulAction.toPerm g : Equiv.Perm (G ⧸ H)) f)
  · rw [map_sum]
    trans ∑ _ : G ⧸ H, d.hom v
    · apply Finset.sum_congr rfl
      intro q _
      induction q using Quotient.inductionOn with
      | h g => exact (Rep.hom_comm_apply d g v).trans (hdv g)
    · rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
        ← H.index_eq_card]

end Trace

section NativeCohomology

variable {R G : Type u} [CommRing R] [Group G]
  (A : Rep.{u} R G) (H : Subgroup G) [H.FiniteIndex]

private theorem H2_map_nsmul_id (m : ℕ)
    (c : groupCohomology A 2) :
    groupCohomology.map (MonoidHom.id G) (m • 𝟙 A) 2 c = m • c := by
  induction c using groupCohomology.H2_induction_on with
  | h z =>
    rw [groupCohomology.H2π_comp_map_apply]
    have hz : groupCohomology.mapCocycles₂ (MonoidHom.id G) (m • 𝟙 A) z = m • z := by
      apply Subtype.ext
      funext st
      rfl
    rw [hz, map_nsmul]

/-- The finite-index trace on degree-two cohomology, obtained from
Shapiro's isomorphism and the trace on the coinduced coefficient module. -/
def finiteIndexH2Corestriction :
    groupCohomology (Rep.res H.subtype A) 2 ⟶ groupCohomology A 2 :=
  (groupCohomology.coindIso (Rep.res H.subtype A) 2).inv ≫
    groupCohomology.map (MonoidHom.id G) (finiteIndexCoefficientTrace.{u, u, u} A H) 2

/-- Degree-two corestriction after subgroup restriction multiplies by the index. -/
theorem finiteIndexH2Corestriction_restrict (c : groupCohomology A 2) :
    finiteIndexH2Corestriction A H (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) 2 c) =
      H.index • c := by
  let B := Rep.res H.subtype A
  let η := Rep.resCoindHomEquiv.{u} H.subtype A B (𝟙 B)
  let e := groupCohomology.coindIso B 2
  have hcoeff : (Rep.resFunctor H.subtype).map η ≫ Rep.coindEvaluation H.subtype B = 𝟙 B := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change A.ρ (1 : G) x = x
    rw [map_one, one_apply_eq_self]
  have hmap : groupCohomology.map (MonoidHom.id G) η 2 ≫ e.hom =
      groupCohomology.map H.subtype (𝟙 B) 2 := by
    change _ ≫ (groupCohomology.coindIso B 2).hom = _
    rw [groupCohomology.coindIso_hom_eq_map, ← groupCohomology.map_comp]
    apply groupCohomology.map_congr (MonoidHom.id_comp H.subtype)
    exact congrArg (fun f : B ⟶ B => f.hom.toLinearMap) hcoeff
  have hEval := ConcreteCategory.congr_hom hmap c
  change e.hom (groupCohomology.map (MonoidHom.id G) η 2 c) =
    groupCohomology.map H.subtype (𝟙 B) 2 c at hEval
  let trace := finiteIndexCoefficientTrace.{u, u, u} A H
  change groupCohomology.map (MonoidHom.id G) trace 2
      (e.inv (groupCohomology.map H.subtype (𝟙 B) 2 c)) = H.index • c
  rw [← hEval, Iso.hom_inv_id_apply, ← H2_map_nsmul_id,
    ← coinductionUnit_comp_finiteIndexCoefficientTrace.{u, u, u}, groupCohomology.map_id_comp]
  simp only [ConcreteCategory.comp_apply, trace, η, B]

/-- The subgroup index kills a class whose actual restriction is zero. -/
theorem index_nsmul_H2_eq_zero_of_restriction_eq_zero
    (c : groupCohomology A 2)
    (hc : groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) 2 c = 0) :
    H.index • c = 0 := by
  rw [← finiteIndexH2Corestriction_restrict A H, hc, map_zero]

/-- A class in degree two vanishes if its actual restrictions to all Sylow subgroups vanish. -/
theorem H2_eq_zero_of_sylow_restriction_eq_zero [Finite G]
    (c : groupCohomology A 2)
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      let S : Subgroup G := P
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2 c = 0) : c = 0 := by
  classical
  by_contra hc
  have ho : addOrderOf c ≠ 1 := fun h1 => hc (AddMonoid.addOrderOf_eq_one_iff.mp h1)
  obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd ho
  let : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := Classical.choice inferInstance
  have hkill : P.index • c = 0 := index_nsmul_H2_eq_zero_of_restriction_eq_zero A P c (h p P)
  exact P.not_dvd_index (hpc.trans (addOrderOf_dvd_of_nsmul_eq_zero hkill))

/-- Degree-two injectivity of an actual coefficient map can be checked on Sylow subgroups. -/
theorem H2_map_injective_of_sylow [Finite G] {B : Rep.{u} R G} (f : A ⟶ B)
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      let S : Subgroup G := P
      Function.Injective (groupCohomology.map (A := Rep.res S.subtype A)
        (B := Rep.res S.subtype B) (MonoidHom.id S)
        ((Rep.resFunctor S.subtype).map f) 2).hom) :
    Function.Injective (groupCohomology.map (MonoidHom.id G) f 2).hom := by
  let F := groupCohomology.map (MonoidHom.id G) f 2
  apply (injective_iff_map_eq_zero F.hom).mpr
  intro x hx
  apply H2_eq_zero_of_sylow_restriction_eq_zero A x
  intro p hp P
  let S : Subgroup G := P
  let rA := groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2
  let rB := groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype B)) 2
  let fS := groupCohomology.map (A := Rep.res S.subtype A) (B := Rep.res S.subtype B)
    (MonoidHom.id S) ((Rep.resFunctor S.subtype).map f) 2
  have hs : rA ≫ fS = F ≫ rB := by
    dsimp only [rA, rB, fS, F]
    rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
    apply groupCohomology.map_congr ((MonoidHom.comp_id S.subtype).trans
      (MonoidHom.id_comp S.subtype).symm)
    apply LinearMap.ext
    intro a
    rfl
  have hsx : fS (rA x) = rB (F x) := ConcreteCategory.congr_hom hs x
  apply h p P
  change fS (rA x) = fS 0
  simp only [hsx, show F x = 0 from hx, map_zero]

/-- If actual H² on a finite-index subgroup vanishes, its index kills every ambient H² class. -/
theorem index_nsmul_H2_eq_zero_of_restricted_isZero
    (hH : Limits.IsZero (groupCohomology (Rep.res H.subtype A) 2))
    (c : groupCohomology A 2) : H.index • c = 0 := by
  let : Subsingleton (groupCohomology (Rep.res H.subtype A) 2) :=
    ModuleCat.isZero_iff_subsingleton.mp hH
  exact index_nsmul_H2_eq_zero_of_restriction_eq_zero A H c (Subsingleton.elim _ _)

/-- Vanishing on every Sylow subgroup detects vanishing of actual H². -/
theorem H2_eq_zero_of_sylow_restrictions_isZero [Finite G]
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      Limits.IsZero (groupCohomology (Rep.res (P : Subgroup G).subtype A) 2))
    (c : groupCohomology A 2) : c = 0 := by
  classical
  by_contra hc
  have ho : addOrderOf c ≠ 1 := fun h1 => hc (AddMonoid.addOrderOf_eq_one_iff.mp h1)
  obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd ho
  have : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := Classical.choice inferInstance
  have hkill : P.index • c = 0 :=
    index_nsmul_H2_eq_zero_of_restricted_isZero A P (h p P) c
  exact P.not_dvd_index (hpc.trans (addOrderOf_dvd_of_nsmul_eq_zero hkill))

end NativeCohomology

end
end ClassFieldTower.Cohomology
