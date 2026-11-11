/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
public import Nyll.GaloisCohomology.Cyclic.IntegralCyclicNormComplexes

/-!
# Integral Tate cohomology and the original arithmetic Herbrand quotients

The group and multiplicative coefficients have independent universes. The original norm and
action-minus-identity complexes identify their cycles and boundaries with the actual fixed
subgroup, norm kernel, norm image and augmentation subgroup. The resulting quotient comparisons
connect the existing integral Tate owner to the original arithmetic Herbrand groups.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory IntegralGroupCohomology.Universe

namespace CyclicCohomology.ProfiniteCohomology.Herbrand

variable {G : Type u} {A : Type v} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]

omit [Fintype G] in
/-- The kernel of the original generator-minus-identity map consists of actual fixed points. -/
def cyclicFixedCyclesAddEquiv (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    LinearMap.ker ((Rep.ofMulDistribMulAction G A).ρ σ - LinearMap.id) ≃+
      Additive (fixedSubgroup G A) where
  toFun x := Additive.ofMul ⟨x.1.toMul, by
    have hx : (Rep.ofMulDistribMulAction G A).ρ σ x.1 = x.1 :=
      sub_eq_zero.mp x.2
    have hσ : sigmaMinusOne G A σ x.1.toMul = 1 := by
      unfold sigmaMinusOne
      exact mul_inv_eq_one.mpr (congrArg (@Additive.toMul A) hx)
    exact fixed_of_forall_mem_zpowers_of_sigmaMinusOne_eq_one hgen hσ⟩
  invFun x := ⟨Additive.ofMul x.toMul.1, by
    change Additive.ofMul (σ • x.toMul.1) - Additive.ofMul x.toMul.1 = 0
    rw [x.toMul.2 σ, sub_self]⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    rfl

/-- Homology of the original norm complex is the original fixed-point quotient by norms. -/
def normHomologyEquivHerbrandH0 (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    (normHomCompSub (Rep.ofMulDistribMulAction G A) σ).homology ≃+
      Additive (HerbrandH0 G A) := by
  let M := Rep.ofMulDistribMulAction G A
  let S := normHomCompSub M σ
  let eK : S.moduleCatLeftHomologyData.K ≃ₗ[ℤ] Additive (fixedSubgroup G A) :=
    (cyclicFixedCyclesAddEquiv (G := G) (A := A) σ hgen).toIntLinearEquiv
  have eK_boundary_value (a : Additive A) :
      (eK (S.moduleCatToCycles a)).toMul.1 = tateNorm G A a.toMul := by
    change Additive.toMul ((Rep.ofMulDistribMulAction G A).ρ.norm a) = _
    exact repNorm_toMul a
  let q : Additive (fixedSubgroup G A) →+ Additive (HerbrandH0 G A) :=
    MonoidHom.toAdditive (HerbrandH0.mk (G := G) (A := A))
  have hboundary :
      (LinearMap.range S.moduleCatToCycles).map eK.toLinearMap =
        q.ker.toIntSubmodule := by
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha⟩, rfl⟩
      subst y
      change Additive A at a
      change q (eK (S.moduleCatToCycles a)) = 0
      apply Additive.ofMul.injective
      change HerbrandH0.mk _ = 1
      apply (HerbrandH0.mk_eq_one_iff _).2
      exact ⟨a.toMul, (eK_boundary_value a).symm⟩
    · intro hx
      change q x = 0 at hx
      have hx' : HerbrandH0.mk x.toMul = 1 := by
        apply Additive.ofMul.injective
        exact hx
      rcases (HerbrandH0.mk_eq_one_iff x.toMul).1 hx' with ⟨a, ha⟩
      refine ⟨eK.symm x, ?_, eK.apply_symm_apply x⟩
      refine ⟨Additive.ofMul a, ?_⟩
      apply eK.injective
      rw [eK.apply_symm_apply]
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (eK_boundary_value (Additive.ofMul a)).trans ha
  let eQ :=
    (Submodule.Quotient.equiv (LinearMap.range S.moduleCatToCycles)
      q.ker.toIntSubmodule eK hboundary).trans
      ((QuotientAddGroup.quotientKerEquivOfSurjective q
        (HerbrandH0.mk_surjective (G := G) (A := A))).toIntLinearEquiv
          (modM₂ := inferInstance))
  exact (S.moduleCatHomologyIso ≪≫ eQ.toModuleIso).toLinearEquiv.toAddEquiv

/-- Homology of the original reverse norm complex is the arithmetic augmentation quotient. -/
def subNormHomologyEquivHerbrandHMinusOne (σ : G) :
    (subCompNormHom (Rep.ofMulDistribMulAction G A) σ).homology ≃+
      Additive (HerbrandHMinusOne G A σ) := by
  let M := Rep.ofMulDistribMulAction G A
  let S := subCompNormHom M σ
  let eK : S.moduleCatLeftHomologyData.K ≃ₗ[ℤ] Additive (normKernelSubgroup G A) :=
    (normKernelCyclesAddEquiv (G := G) (A := A)).toIntLinearEquiv
  have eK_boundary_value (a : Additive A) :
      (eK (S.moduleCatToCycles a)).toMul.1 = sigmaMinusOne G A σ a.toMul := by
    change Additive.toMul (Additive.ofMul (σ • a.toMul) - a) = _
    rw [toMul_sub]
    exact div_eq_mul_inv _ _
  let q : Additive (normKernelSubgroup G A) →+
      Additive (HerbrandHMinusOne G A σ) :=
    MonoidHom.toAdditive (HerbrandHMinusOne.mk (G := G) (A := A) σ)
  have hboundary :
      (LinearMap.range S.moduleCatToCycles).map eK.toLinearMap =
        q.ker.toIntSubmodule := by
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha⟩, rfl⟩
      subst y
      change Additive A at a
      change q (eK (S.moduleCatToCycles a)) = 0
      apply Additive.ofMul.injective
      change HerbrandHMinusOne.mk σ _ = 1
      apply (HerbrandHMinusOne.mk_eq_one_iff σ _).2
      exact ⟨a.toMul, (eK_boundary_value a).symm⟩
    · intro hx
      change q x = 0 at hx
      have hx' : HerbrandHMinusOne.mk σ x.toMul = 1 := by
        apply Additive.ofMul.injective
        exact hx
      rcases (HerbrandHMinusOne.mk_eq_one_iff σ x.toMul).1 hx' with ⟨a, ha⟩
      refine ⟨eK.symm x, ?_, eK.apply_symm_apply x⟩
      refine ⟨Additive.ofMul a, ?_⟩
      apply eK.injective
      rw [eK.apply_symm_apply]
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (eK_boundary_value (Additive.ofMul a)).trans ha
  let eQ :=
    (Submodule.Quotient.equiv (LinearMap.range S.moduleCatToCycles)
      q.ker.toIntSubmodule eK hboundary).trans
      ((QuotientAddGroup.quotientKerEquivOfSurjective q
        (HerbrandHMinusOne.mk_surjective (G := G) (A := A) σ)).toIntLinearEquiv
          (modM₂ := inferInstance))
  exact (S.moduleCatHomologyIso ≪≫ eQ.toModuleIso).toLinearEquiv.toAddEquiv

/-- Actual integral Tate degree zero computes the original multiplicative norm quotient. -/
def integralTateH0EquivHerbrandH0 (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    tate (Rep.ofMulDistribMulAction G A) 0 ≃+ Additive (HerbrandH0 G A) :=
  (normHomologyEquivTateZero (Rep.ofMulDistribMulAction G A) σ hgen).symm.trans
    (normHomologyEquivHerbrandH0 σ hgen)

/-- Actual integral Tate degree minus one computes the original augmentation quotient. -/
def integralTateHMinusOneEquivHerbrandHMinusOne
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    tate (Rep.ofMulDistribMulAction G A) (-1) ≃+ Additive (HerbrandHMinusOne G A σ) :=
  (subNormHomologyEquivTateMinusOne (Rep.ofMulDistribMulAction G A) σ hgen).symm.trans
    (subNormHomologyEquivHerbrandHMinusOne σ)

end CyclicCohomology.ProfiniteCohomology.Herbrand
