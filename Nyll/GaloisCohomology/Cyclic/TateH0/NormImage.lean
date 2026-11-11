/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Nyll.GaloisCohomology.Cyclic.TateComparison
public import Nyll.GaloisCohomology.Cyclic.TateH0.Invariants
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology

/-!
# Norm images in degree-zero Tate cohomology of units

The representation norm on the units of a field extension lands in the invariant units.
Its image defines the norm submodule, and the quotient of the invariant units by this
submodule realizes degree-zero Tate cohomology. The norm map is also compared with
the field norm on units.
-/

@[expose] public section

namespace CyclicCohomology

open LocalFieldTheory
open CategoryTheory

noncomputable section

universe u v w

/-- The group-cohomological norm endomorphism on the actual unit representation. -/
def unitsNormLinearMap (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Fintype Gal(L/K)] : Additive Lˣ →ₗ[ℤ] Additive Lˣ :=
  (Rep.ofAlgebraAutOnUnits K L).norm.asHom.hom.toLinearMap

/-- The additive unit norm is fixed by the Galois action. -/
lemma unitsNorm_mem_invariants (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Fintype Gal(L/K)] (x : Additive Lˣ) :
    unitsNormLinearMap K L x ∈ unitsInvariantSubmodule K L := by
  intro σ
  exact Representation.self_norm_apply (Rep.ofAlgebraAutOnUnits K L).ρ σ x

/-- The norm map, codomain-restricted to invariant units. -/
def unitsNormToInvariantsLinearMap (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Fintype Gal(L/K)] : Additive Lˣ →ₗ[ℤ] unitsInvariantSubmodule K L :=
  (unitsNormLinearMap K L).codRestrict (unitsInvariantSubmodule K L)
    (unitsNorm_mem_invariants K L)

/-- Norm image inside invariant units. -/
def unitsTateH0NormSubmodule (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Fintype Gal(L/K)] : Submodule ℤ (unitsInvariantSubmodule K L) :=
  LinearMap.range (unitsNormToInvariantsLinearMap K L)

/-- The standard degree-zero Tate object, expressed as the arithmetic quotient
of invariant units by the representation norm image. -/
def tateUnitsH0IsoInvariantsQuotient (K L : Type)
    [Field K] [Field L] [Algebra K L] [Fintype Gal(L/K)] :
    tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0 ≅
      ModuleCat.of ℤ
        (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) := by
  let A := Rep.ofAlgebraAutOnUnits K L
  let S : ShortComplex (ModuleCat ℤ) :=
    .mk A.norm.asHom.toModuleCatHom (groupCohomology.d₀₁ A)
      (Rep.norm_comp_d_eq_zero A)
  have hker :
      LinearMap.ker S.g.hom = unitsInvariantSubmodule K L := by
    exact groupCohomology.d₀₁_ker_eq_invariants A
  let eK : LinearMap.ker S.g.hom ≃ₗ[ℤ] unitsInvariantSubmodule K L :=
    LinearEquiv.ofEq _ _ hker
  have hboundary :
      (LinearMap.range S.moduleCatToCycles).map eK.toLinearMap =
        unitsTateH0NormSubmodule K L := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      rfl
    · rintro ⟨z, rfl⟩
      refine ⟨S.moduleCatToCycles z, ⟨z, rfl⟩, ?_⟩
      apply Subtype.ext
      rfl
  let eQ :
      S.moduleCatLeftHomologyData.H ≅
        ModuleCat.of ℤ
          (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) :=
    (Submodule.Quotient.equiv _ _ eK hboundary).toModuleIso
  exact TateCohomology.isoZeroBoundary A ≪≫
    S.moduleCatHomologyIso ≪≫ eQ

/-- The actual integral Tate object has the invariant-unit quotient in arbitrary
field universes. Scalar transport retains the unit carrier and its Galois action. -/
def integralTateUnitsH0AddEquivInvariantsQuotient (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [Fintype Gal(L/K)] :
    IntegralGroupCohomology.tate (Rep.ofAlgebraAutOnUnits K L) 0 ≃+
      (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) := by
  let A := Rep.ofAlgebraAutOnUnits K L
  let B := (IntegralGroupCohomology.coefficientFunctor Gal(L/K)).obj A
  let S : ShortComplex (ModuleCat (ULift.{v} ℤ)) :=
    .mk B.norm.asHom.toModuleCatHom (groupCohomology.d₀₁ B)
      (Rep.norm_comp_d_eq_zero B)
  let eI : B.ρ.invariants ≃+ unitsInvariantSubmodule K L :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let eK : LinearMap.ker S.g.hom ≃+ unitsInvariantSubmodule K L :=
    (LinearEquiv.ofEq _ _ (groupCohomology.d₀₁_ker_eq_invariants B)).toAddEquiv.trans eI
  have hboundary :
      (LinearMap.range S.moduleCatToCycles).toAddSubgroup.map eK.toAddMonoidHom =
        (unitsTateH0NormSubmodule K L).toAddSubgroup := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      exact (IntegralGroupCohomology.coefficientFunctor_norm_apply A z).symm
    · rintro ⟨z, rfl⟩
      refine ⟨S.moduleCatToCycles z, ⟨z, rfl⟩, ?_⟩
      apply Subtype.ext
      exact IntegralGroupCohomology.coefficientFunctor_norm_apply A z
  let eQ := QuotientAddGroup.congr
    (LinearMap.range S.moduleCatToCycles).toAddSubgroup
    (unitsTateH0NormSubmodule K L).toAddSubgroup eK hboundary
  exact
    (TateCohomology.isoZeroBoundary B ≪≫ S.moduleCatHomologyIso).toLinearEquiv.toAddEquiv.trans eQ

/-- The Tate class of an actual invariant unit, formed in the native
boundary short complex before passing to its homology object. -/
def integralUnitsTateClass (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [Fintype Gal(L/K)]
    (x : unitsInvariantSubmodule K L) :
    IntegralGroupCohomology.tate (Rep.ofAlgebraAutOnUnits K L) 0 := by
  let B := (IntegralGroupCohomology.coefficientFunctor Gal(L/K)).obj
    (Rep.ofAlgebraAutOnUnits K L)
  let S : ShortComplex (ModuleCat (ULift.{v} ℤ)) :=
    .mk B.norm.asHom.toModuleCatHom (groupCohomology.d₀₁ B)
      (Rep.norm_comp_d_eq_zero B)
  let z : LinearMap.ker S.g.hom := ⟨x.1, by
    change x.1 ∈ LinearMap.ker (groupCohomology.d₀₁ B).hom
    rw [groupCohomology.d₀₁_ker_eq_invariants]
    exact x.2⟩
  exact (TateCohomology.isoZeroBoundary B ≪≫ S.moduleCatHomologyIso).inv
    ((LinearMap.range S.moduleCatToCycles).mkQ z)

/-- The comparison sends the native invariant-unit class to its original
quotient representative. -/
theorem integralTateUnitsH0AddEquivInvariantsQuotient_class (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [Fintype Gal(L/K)]
    (x : unitsInvariantSubmodule K L) :
    integralTateUnitsH0AddEquivInvariantsQuotient K L (integralUnitsTateClass K L x) =
      (unitsTateH0NormSubmodule K L).mkQ x := by
  change integralTateUnitsH0AddEquivInvariantsQuotient K L
      ((integralTateUnitsH0AddEquivInvariantsQuotient K L).symm
        ((unitsTateH0NormSubmodule K L).mkQ x)) = _
  exact (integralTateUnitsH0AddEquivInvariantsQuotient K L).apply_symm_apply _

/-- Scalar transport sends the original invariant-unit class to the same integral class. -/
theorem integralUnitsTateClass_original (K L : Type)
    [Field K] [Field L] [Algebra K L] [Fintype Gal(L/K)]
    (x : unitsInvariantSubmodule K L) :
    (IntegralGroupCohomology.tateIsoOriginal (Rep.ofAlgebraAutOnUnits K L) 0).inv
        ((tateUnitsH0IsoInvariantsQuotient K L).inv (Submodule.Quotient.mk x)) =
      integralUnitsTateClass K L x := by
  let A := Rep.ofAlgebraAutOnUnits K L
  let e : ULift.{0} ℤ ≃+* ℤ := ULift.ringEquiv
  let F := ModuleCat.restrictScalars e.toRingHom
  let B := (IntegralGroupCohomology.coefficientFunctor Gal(L/K)).obj A
  let S : ShortComplex (ModuleCat ℤ) :=
    .mk A.norm.asHom.toModuleCatHom (groupCohomology.d₀₁ A) (Rep.norm_comp_d_eq_zero A)
  let T : ShortComplex (ModuleCat (ULift.{0} ℤ)) :=
    .mk B.norm.asHom.toModuleCatHom (groupCohomology.d₀₁ B) (Rep.norm_comp_d_eq_zero B)
  let z : LinearMap.ker S.g.hom := ⟨x.1, by
    change x.1 ∈ LinearMap.ker (groupCohomology.d₀₁ A).hom
    rw [groupCohomology.d₀₁_ker_eq_invariants]
    exact x.2⟩
  let w : LinearMap.ker T.g.hom := ⟨x.1, by
    change x.1 ∈ LinearMap.ker (groupCohomology.d₀₁ B).hom
    rw [groupCohomology.d₀₁_ker_eq_invariants]
    exact x.2⟩
  let a := TateCohomology.zeroBoundaryComplexIso A
  let b := TateCohomology.zeroBoundaryComplexIso B
  let c := (HomologicalComplex.shortComplexFunctor
    (ModuleCat (ULift.{0} ℤ)) (ComplexShape.up ℤ) 0).map
      (TateCohomology.coefficientRingComplexIso e A).hom
  let f : S.map F ⟶ T := F.mapShortComplex.map a.inv ≫ c ≫ b.hom
  have hzw : f.τ₂ z.val = w.val := rfl
  have hclass := ShortComplex.restrictScalars_homologyClass e.toRingHom S T f z w hzw
  have hroute :
      F.map (ShortComplex.homologyMap a.inv) ≫
          (TateCohomology.coefficientRingIso e A 0).hom ≫
          ShortComplex.homologyMap b.hom =
        (S.mapHomologyIso F).inv ≫ ShortComplex.homologyMap f := by
    change F.map (ShortComplex.homologyMap a.inv) ≫
        ((tateComplex A).sc 0 |>.mapHomologyIso F).inv ≫
          ShortComplex.homologyMap c ≫ ShortComplex.homologyMap b.hom = _
    rw [ShortComplex.mapHomologyIso_inv_naturality_assoc a.inv F]
    have hcomp : ShortComplex.homologyMap f =
        ShortComplex.homologyMap (F.mapShortComplex.map a.inv) ≫
          ShortComplex.homologyMap c ≫ ShortComplex.homologyMap b.hom :=
      (ShortComplex.homologyMap_comp (F.mapShortComplex.map a.inv) (c ≫ b.hom)).trans
        (congrArg (fun m => ShortComplex.homologyMap (F.mapShortComplex.map a.inv) ≫ m)
          (ShortComplex.homologyMap_comp c b.hom))
    exact congrArg (fun m => (S.mapHomologyIso F).inv ≫ m) hcomp.symm
  apply (ModuleCat.mono_iff_injective (TateCohomology.isoZeroBoundary B).hom).mp inferInstance
  change (F.map (ShortComplex.homologyMap a.inv) ≫
      (TateCohomology.coefficientRingIso e A 0).hom ≫
        ShortComplex.homologyMap b.hom)
      (S.moduleCatHomologyIso.inv (Submodule.Quotient.mk z)) =
    (TateCohomology.isoZeroBoundary B).hom
      (integralUnitsTateClass K L x)
  rw [hroute]
  exact hclass.trans
    ((TateCohomology.isoZeroBoundary B).inv_hom_id_apply
      (T.moduleCatHomologyIso.inv (Submodule.Quotient.mk w))).symm

/-- The independent-universe integral owner uses the same invariant quotient,
through its actual group and coefficient comparison. -/
def universeTateUnitsH0AddEquivInvariantsQuotient (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [Fintype Gal(L/K)] :
    IntegralGroupCohomology.Universe.tate (Rep.ofAlgebraAutOnUnits K L) 0 ≃+
      (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) :=
  (IntegralGroupCohomology.Universe.tateIsoCommon
      (Rep.ofAlgebraAutOnUnits K L) 0).toLinearEquiv.toAddEquiv.trans
    (integralTateUnitsH0AddEquivInvariantsQuotient K L)

/-- The value of the additive unit norm map is the field norm of the underlying unit. -/
theorem unitsNormLinearMap_apply_val (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (x : Lˣ) :
    (letI := AlgEquiv.fintype K L
     (Additive.toMul (unitsNormLinearMap K L (Additive.ofMul x)) : Lˣ).1) =
      algebraMap K L (Algebra.norm K (x : L)) := by
  let := AlgEquiv.fintype K L
  change (Additive.toMul
    ((Representation.ofMulDistribMulAction Gal(L/K) Lˣ).norm (Additive.ofMul x)) : Lˣ).1 =
      algebraMap K L (Algebra.norm K (x : L))
  rw [Representation.norm, LinearMap.sum_apply, toMul_sum, Units.coe_prod,
    Algebra.norm_eq_prod_automorphisms]
  rfl

/-- A finite sum of additive units corresponds to the product of their underlying units. -/
@[simp]
lemma additive_toMul_finset_sum_units {ι : Type*} (L : Type*) [Field L]
    (s : Finset ι) (f : ι → Additive Lˣ) :
    Additive.toMul (Finset.sum s f) =
      Finset.prod s (fun i => Additive.toMul (f i)) := by
  exact toMul_sum s f

/-- The additive subgroup of `Additive Kˣ` attached to the multiplicative norm subgroup. -/
def additiveNormSubgroup (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    AddSubgroup (Additive Kˣ) :=
  (localNormSubgroup K L).toAddSubgroup

/-- The additive norm subgroup is the kernel of the norm-quotient map. -/
lemma additiveNormSubgroup_eq_ker_quotient_map (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] :
    additiveNormSubgroup K L =
      (MonoidHom.toAdditive (normClass K L)).ker := by
  ext x
  change Additive.toMul x ∈ localNormSubgroup K L ↔
    Additive.ofMul (normClass K L (Additive.toMul x)) = 0
  constructor
  · intro hx
    exact congrArg Additive.ofMul
      ((normClass_eq_one_iff K L (Additive.toMul x)).mpr
        (MonoidHom.mem_range.mp hx))
  · intro hx
    exact MonoidHom.mem_range.mpr
      ((normClass_eq_one_iff K L (Additive.toMul x)).mp
        (Additive.ofMul.injective hx))

/-- The invariant-unit equivalence sends the additive unit norm to the field norm. -/
lemma invariantsUnitsAddEquivBaseUnits_unitsNorm_apply (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (x : Lˣ) :
    (letI := AlgEquiv.fintype K L
     invariantsUnitsAddEquivBaseUnits K L
        (unitsNormToInvariantsLinearMap K L (Additive.ofMul x))) =
      Additive.ofMul (normUnits K L x) := by
  let := AlgEquiv.fintype K L
  apply Additive.toMul.injective
  ext
  apply FaithfulSMul.algebraMap_injective K L
  rw [invariantsUnitsAddEquivBaseUnits_spec]
  exact (unitsNormLinearMap_apply_val K L x).trans (by rfl)

/-- Descending the two actual representation norms commutes with the
original field-unit norm in a tower. No alternate norm map is introduced. -/
theorem invariantsUnitsAddEquivBaseUnits_unitsNorm_tower
    (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K L] [FiniteDimensional M L]
    [IsGalois K L] [IsGalois M L] (x : Lˣ) :
    (letI := AlgEquiv.fintype M L
     normUnits K M (Additive.toMul (invariantsUnitsAddEquivBaseUnits M L
       (unitsNormToInvariantsLinearMap M L (Additive.ofMul x))))) =
      (letI := AlgEquiv.fintype K L
       Additive.toMul (invariantsUnitsAddEquivBaseUnits K L
         (unitsNormToInvariantsLinearMap K L (Additive.ofMul x)))) := by
  let := AlgEquiv.fintype K L
  let := AlgEquiv.fintype M L
  rw [invariantsUnitsAddEquivBaseUnits_unitsNorm_apply,
    invariantsUnitsAddEquivBaseUnits_unitsNorm_apply]
  exact normUnits_tower K M L x

/-- The invariant-unit equivalence maps the Tate norm submodule onto the additive norm subgroup. -/
lemma invariantsUnitsAddEquivBaseUnits_map_tateNormSubgroup (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    (letI := AlgEquiv.fintype K L
     (unitsTateH0NormSubmodule K L).toAddSubgroup.map
        (invariantsUnitsAddEquivBaseUnits K L).toAddMonoidHom) =
      additiveNormSubgroup K L := by
  let := AlgEquiv.fintype K L
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨z, rfl⟩
    change Additive.toMul
        (invariantsUnitsAddEquivBaseUnits K L
          (unitsNormToInvariantsLinearMap K L z)) ∈ localNormSubgroup K L
    let a : Lˣ := Additive.toMul z
    rw [show z = Additive.ofMul a by cases z; rfl]
    have hmap :=
      congrArg Additive.toMul
        (invariantsUnitsAddEquivBaseUnits_unitsNorm_apply K L a)
    rw [hmap]
    exact ⟨a, rfl⟩
  · intro hy
    change Additive.toMul y ∈ localNormSubgroup K L at hy
    rcases hy with ⟨x, hx⟩
    refine ⟨unitsNormToInvariantsLinearMap K L (Additive.ofMul x), ⟨Additive.ofMul x, rfl⟩, ?_⟩
    change
      invariantsUnitsAddEquivBaseUnits K L
          (unitsNormToInvariantsLinearMap K L (Additive.ofMul x)) = y
    calc
      invariantsUnitsAddEquivBaseUnits K L
          (unitsNormToInvariantsLinearMap K L (Additive.ofMul x))
          = Additive.ofMul (normUnits K L x) :=
            invariantsUnitsAddEquivBaseUnits_unitsNorm_apply K L x
      _ = Additive.ofMul (Additive.toMul y) := congrArg Additive.ofMul hx
      _ = y := by cases y; rfl

/-- The multiplicative invariant-unit equivalence maps Tate norms onto field norms. -/
lemma invariantsUnitsEquivBaseUnits_map_tateNormSubmodule (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    (letI := AlgEquiv.fintype K L
     (unitsTateH0NormSubmodule K L).map
        (invariantsUnitsEquivBaseUnits K L : unitsInvariantSubmodule K L →ₗ[ℤ] Additive Kˣ)) =
      (additiveNormSubgroup K L).toIntSubmodule := by
  let := AlgEquiv.fintype K L
  apply Submodule.toAddSubgroup_injective
  rw [Submodule.map_toAddSubgroup]
  exact invariantsUnitsAddEquivBaseUnits_map_tateNormSubgroup K L

end
end CyclicCohomology
