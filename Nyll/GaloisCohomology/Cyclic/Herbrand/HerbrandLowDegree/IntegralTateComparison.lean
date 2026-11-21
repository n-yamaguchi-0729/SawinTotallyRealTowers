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
public import Nyll.GaloisCohomology.Cyclic.IntegralTateFixedCycles

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

/-- The original invariant-vector quotient is the multiplicative Herbrand quotient. -/
def fixedQuotientEquivHerbrandH0 :
    let M := Rep.ofMulDistribMulAction G A
    (M.ρ.invariants ⧸ fixedNormSubmodule M) ≃+ Additive (HerbrandH0 G A) := by
  let M := Rep.ofMulDistribMulAction G A
  let e := (fixedSubgroupAddEquivInvariants (G₀ := G) (A₀ := A)).symm
  let q := MonoidHom.toAdditive (HerbrandH0.mk (G := G) (A := A))
  have hnorm : (fixedNormSubmodule M).toAddSubgroup.map e.toAddMonoidHom = q.ker := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      change (a : M) ∈ LinearMap.range M.ρ.norm at ha
      obtain ⟨b, hb⟩ := ha
      change q (e a) = 0
      apply Additive.ofMul.injective
      change HerbrandH0.mk (e a).toMul = 1
      apply (HerbrandH0.mk_eq_one_iff _).mpr
      exact ⟨b.toMul, (repNorm_toMul (G := G) (A := A) b).symm.trans
        (congrArg Additive.toMul hb)⟩
    · intro hx
      change q x = 0 at hx
      have hx' : HerbrandH0.mk x.toMul = 1 := Additive.ofMul.injective hx
      obtain ⟨b, hb⟩ := (HerbrandH0.mk_eq_one_iff _).mp hx'
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      change ((e.symm x : M.ρ.invariants) : M) ∈ LinearMap.range M.ρ.norm
      refine ⟨Additive.ofMul b, ?_⟩
      apply Additive.toMul.injective
      exact (repNorm_toMul (G := G) (A := A) (Additive.ofMul b)).trans hb
  exact (QuotientAddGroup.congr (fixedNormSubmodule M).toAddSubgroup q.ker e hnorm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective q (HerbrandH0.mk_surjective (G := G) (A := A)))

/-- Degree-zero integral Tate cohomology is the original Herbrand quotient
for any finite group and independently sized multiplicative coefficients. -/
def integralTateZeroEquivHerbrandH0 :
    tate (Rep.ofMulDistribMulAction G A) 0 ≃+ Additive (HerbrandH0 G A) :=
  (tateZeroEquivFixedQuotient (Rep.ofMulDistribMulAction G A)).trans fixedQuotientEquivHerbrandH0

/-- The generator-free comparison evaluates on the original fixed class. -/
theorem integralTateZeroEquivHerbrandH0_fixedClass (a : fixedSubgroup G A) :
    let M := Rep.ofMulDistribMulAction G A
    let b := fixedSubgroupAddEquivInvariants (Additive.ofMul a)
    integralTateZeroEquivHerbrandH0 (fixedClass M b) = Additive.ofMul (HerbrandH0.mk a) := by
  intro M b
  change fixedQuotientEquivHerbrandH0 (tateZeroEquivFixedQuotient M (fixedClass M b)) = _
  rw [tateZeroEquivFixedQuotient_fixedClass]
  exact Eq.refl (Additive.ofMul (HerbrandH0.mk a))

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

/-- The concrete norm-complex quotient represents the original fixed-point classes. -/
def normConcreteHomologyEquivHerbrandH0 (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    (normHomCompSub (Rep.ofMulDistribMulAction G A) σ).moduleCatLeftHomologyData.H ≃ₗ[ℤ]
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
  exact eQ

/-- Homology of the original norm complex is the original fixed-point quotient by norms. -/
def normHomologyEquivHerbrandH0 (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    (normHomCompSub (Rep.ofMulDistribMulAction G A) σ).homology ≃+
      Additive (HerbrandH0 G A) :=
  let S := normHomCompSub (Rep.ofMulDistribMulAction G A) σ
  let e := S.moduleCatHomologyIso ≪≫ (normConcreteHomologyEquivHerbrandH0 σ hgen).toModuleIso
  e.toLinearEquiv.toAddEquiv

/-- The concrete reverse norm-complex quotient represents the original augmentation classes. -/
def subNormConcreteHomologyEquivHerbrandHMinusOne (σ : G) :
    (subCompNormHom (Rep.ofMulDistribMulAction G A) σ).moduleCatLeftHomologyData.H ≃ₗ[ℤ]
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
  exact eQ

/-- Homology of the original reverse norm complex is the arithmetic augmentation quotient. -/
def subNormHomologyEquivHerbrandHMinusOne (σ : G) :
    (subCompNormHom (Rep.ofMulDistribMulAction G A) σ).homology ≃+
      Additive (HerbrandHMinusOne G A σ) :=
  let S := subCompNormHom (Rep.ofMulDistribMulAction G A) σ
  let e := S.moduleCatHomologyIso ≪≫ (subNormConcreteHomologyEquivHerbrandHMinusOne σ).toModuleIso
  e.toLinearEquiv.toAddEquiv

/-- Actual integral Tate degree zero computes the original multiplicative norm quotient. -/
def integralTateH0EquivHerbrandH0 (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    tate (Rep.ofMulDistribMulAction G A) 0 ≃+ Additive (HerbrandH0 G A) :=
  (normHomologyEquivTateZero (Rep.ofMulDistribMulAction G A) σ hgen).symm.trans
    (normHomologyEquivHerbrandH0 σ hgen)

/-- The integral comparison sends the actual Tate class of a fixed vector to
the Herbrand class of that same element, using the specified cyclic generator. -/
theorem integralTateH0EquivHerbrandH0_fixedClass (σ : G)
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (a : fixedSubgroup G A) :
    let M := Rep.ofMulDistribMulAction G A
    let b : M.ρ.invariants := ⟨Additive.ofMul a.val, fun g =>
      congrArg Additive.ofMul (a.property g)⟩
    integralTateH0EquivHerbrandH0 σ hgen (fixedClass M b) =
      Additive.ofMul (HerbrandH0.mk a) := by
  intro M b
  let S := normHomCompSub M σ
  let x : S.moduleCatLeftHomologyData.K := ⟨(b : M), sub_eq_zero.mpr (b.property σ)⟩
  let z := S.moduleCatCyclesIso.inv x
  have hT : normHomologyEquivTateZero M σ hgen (S.homologyπ z) = fixedClass M b :=
    normHomologyEquivTateZero_fixed M σ hgen b
  change normHomologyEquivHerbrandH0 σ hgen
    ((normHomologyEquivTateZero M σ hgen).symm (fixedClass M b)) = _
  rw [← hT, AddEquiv.symm_apply_apply]
  let e := normConcreteHomologyEquivHerbrandH0 (A := A) σ hgen
  change e (S.moduleCatHomologyIso.hom (S.homologyπ z)) = _
  have hz : S.moduleCatCyclesIso.hom z = x := Iso.inv_hom_id_apply S.moduleCatCyclesIso x
  have hc := (S.π_moduleCatCyclesIso_hom_apply z).trans
    (congrArg S.moduleCatLeftHomologyData.π hz)
  rw [hc]
  exact Eq.refl (Additive.ofMul (HerbrandH0.mk a))

/-- A cyclic presentation and the generator-free comparison are the same
map, since both evaluate identically on every actual fixed representative. -/
theorem integralTateH0EquivHerbrandH0_eq (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    integralTateH0EquivHerbrandH0 (A := A) σ hgen =
      integralTateZeroEquivHerbrandH0 (G := G) (A := A) := by
  apply AddEquiv.ext
  intro z
  let M := Rep.ofMulDistribMulAction G A
  let e := fixedSubgroupAddEquivInvariants (G₀ := G) (A₀ := A)
  obtain ⟨b, rfl⟩ := fixedClass_surjective M z
  let a := (e.symm b).toMul
  have hb : e (Additive.ofMul a) = b := e.apply_symm_apply b
  rw [← hb]
  exact (integralTateH0EquivHerbrandH0_fixedClass σ hgen a).trans
    (integralTateZeroEquivHerbrandH0_fixedClass a).symm

/-- Actual integral Tate degree minus one computes the original augmentation quotient. -/
def integralTateHMinusOneEquivHerbrandHMinusOne
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    tate (Rep.ofMulDistribMulAction G A) (-1) ≃+ Additive (HerbrandHMinusOne G A σ) :=
  (subNormHomologyEquivTateMinusOne (Rep.ofMulDistribMulAction G A) σ hgen).symm.trans
    (subNormHomologyEquivHerbrandHMinusOne σ)

/-- The integral comparison sends the actual class of a norm-kernel element to
its Herbrand class modulo the original specified generator-minus-one boundary. -/
theorem integralTateHMinusOneEquivHerbrandHMinusOne_normKernelClass (σ : G)
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (a : normKernelSubgroup G A) :
    let M := Rep.ofMulDistribMulAction G A
    let b : LinearMap.ker M.ρ.norm :=
      (normKernelCyclesAddEquiv (G := G) (A := A)).symm (Additive.ofMul a)
    integralTateHMinusOneEquivHerbrandHMinusOne σ hgen (normKernelClass M b) =
      Additive.ofMul (HerbrandHMinusOne.mk σ a) := by
  intro M b
  let S := subCompNormHom M σ
  let x : S.moduleCatLeftHomologyData.K := b
  let z := S.moduleCatCyclesIso.inv x
  have hT : subNormHomologyEquivTateMinusOne M σ hgen (S.homologyπ z) =
      normKernelClass M b := subNormHomologyEquivTateMinusOne_normKernel M σ hgen b
  change subNormHomologyEquivHerbrandHMinusOne σ
    ((subNormHomologyEquivTateMinusOne M σ hgen).symm (normKernelClass M b)) = _
  rw [← hT, AddEquiv.symm_apply_apply]
  let e := subNormConcreteHomologyEquivHerbrandHMinusOne (A := A) σ
  change e (S.moduleCatHomologyIso.hom (S.homologyπ z)) = _
  have hz : S.moduleCatCyclesIso.hom z = x := Iso.inv_hom_id_apply S.moduleCatCyclesIso x
  have hc := (S.π_moduleCatCyclesIso_hom_apply z).trans
    (congrArg S.moduleCatLeftHomologyData.π hz)
  rw [hc]
  exact Eq.refl (Additive.ofMul (HerbrandHMinusOne.mk σ a))

end CyclicCohomology.ProfiniteCohomology.Herbrand
