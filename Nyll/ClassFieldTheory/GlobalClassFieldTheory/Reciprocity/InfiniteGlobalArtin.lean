/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicZHatBaseChange
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtin
public import Mathlib.FieldTheory.Galois.Profinite
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.AbsoluteNormCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PositiveArchimedeanSection
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormCore

/-!
# The infinite global Artin homomorphism

This file assembles the finite global Artin homomorphisms in the
`FiniteGaloisIntermediateField` inverse limit supplied by mathlib.  The
first target is the actual `ZHat`-extension of `ℚ` constructed in
`CyclotomicZHatBaseChange`.

The positive archimedean section below is the cyclotomic normalization device:
multiplying an idele by the section of its absolute
norm produces a norm-one idele without changing its Artin symbol.
-/



@[expose] public section

open scoped IsMulCommutative NNReal NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

universe u v w x

namespace GlobalClassFieldTheory
namespace Reciprocity

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp

/-- Every positive archimedean section element has trivial finite global Artin symbol. -/
theorem globalArtinMonoidHom_positiveArchimedeanSection
    {K : Type u} [Field K] [NumberField K]
    {L : Type v}
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (r : ℝ≥0ˣ) :
    globalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.positiveArchimedeanSection K r) =
      1 := by
  rw [globalArtinMonoidHom_apply]
  have hinfinite :
      (∏ v : InfinitePlace K,
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.infiniteComponent v
            (IdeleGroup.positiveArchimedeanSection K r))) =
        1 := by
    apply Finset.prod_eq_one
    intro v _
    by_cases hv : v.IsReal
    · apply chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos (K := K) (L := L) v hv
      exact (RayClass.mem_infinitePositiveSubgroup_iff v _).1
        (IdeleGroup.positiveArchimedeanSection_infiniteComponent_mem_positive r v) hv
    · exact chosenInfinitePlaceArtinMonoidHom_eq_one_of_isComplex (K := K) (L := L)
        v (InfinitePlace.not_isReal_iff_isComplex.mp hv) _
  have hfinite :
      (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.finiteComponent v
            (IdeleGroup.positiveArchimedeanSection K r))) =
        1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [IdeleGroup.positiveArchimedeanSection_finiteComponent,
      map_one]
  rw [hinfinite, hfinite, mul_one]

/-!
## Assembly in the finite-Galois inverse limit

The following construction is the global analogue of LCFT's
`residueFrobeniusToLimit`: its coordinates are the actual finite global
Artin homomorphisms, and compatibility is restriction in a finite
abelian tower.
-/

/-- The compatible family of finite global Artin symbols attached to
an idele, regarded as a point of the finite-Galois inverse limit. -/
noncomputable def infiniteGlobalArtinLimitPoint
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) :
    limit
      (InfiniteGalois.asProfiniteGaloisGroupFunctor
        K Ω) := by
  letI (E :
      FiniteGaloisIntermediateField
        K Ω) :
      NumberField E :=
    NumberField.of_module_finite K E
  exact
    { val := fun E =>
        globalArtinMonoidHom
          (K := K) (L := E.unop) a
      property := by
        intro E F f
        algebraize [Subsemiring.inclusion <| leOfHom f.1]
        have : IsScalarTower K F.unop E.unop :=
          IsScalarTower.of_algebraMap_eq (congrFun rfl)
        change
          AlgEquiv.restrictNormalHom F.unop
              (globalArtinMonoidHom
                (K := K) (L := E.unop) a) =
            globalArtinMonoidHom
              (K := K) (L := F.unop) a
        exact
          DFunLike.congr_fun
            (globalArtinMonoidHom_restrict_tower
              (K := K) (E := F.unop) (L := E.unop)) a }

/-- The continuous global Artin homomorphism into the finite-Galois
inverse limit, before transport to the Krull-topological Galois group. -/
noncomputable def infiniteGlobalArtinToLimit
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    IdeleGroup K →ₜ*
      limit
        (InfiniteGalois.asProfiniteGaloisGroupFunctor
          K Ω) := by
  letI
      (E :
        FiniteGaloisIntermediateField
          K Ω) :
      NumberField E :=
    NumberField.of_module_finite K E
  exact
    { toFun := infiniteGlobalArtinLimitPoint K Ω
      map_one' := by
        apply Subtype.ext
        funext E
        exact
          (globalArtinMonoidHom
            (K := K) (L := E.unop)).map_one
      map_mul' := by
        intro x y
        apply Subtype.ext
        funext E
        exact
          (globalArtinMonoidHom
            (K := K) (L := E.unop)).map_mul x y
      continuous_toFun := by
        have hcontinuous
            (E :
              (FiniteGaloisIntermediateField
                K Ω)ᵒᵖ) :
            @Continuous
              (IdeleGroup K) (E.unop ≃ₐ[K] E.unop)
              inferInstance (krullTopology K E.unop)
              (globalArtinMonoidHom
                (K := K) (L := E.unop)) :=
          globalArtinMonoidHom_continuous
            (K := K) (L := E.unop)
        let
            (E :
              (FiniteGaloisIntermediateField
                K Ω)ᵒᵖ) :
            TopologicalSpace (E.unop ≃ₐ[K] E.unop) :=
          ((InfiniteGalois.asProfiniteGaloisGroupFunctor
            K Ω).obj E).toProfinite.toTop.str
        apply Continuous.subtype_mk
        exact continuous_pi fun E => by
          change
            @Continuous
              (IdeleGroup K) (E.unop ≃ₐ[K] E.unop)
              inferInstance inferInstance
              (globalArtinMonoidHom
                (K := K) (L := E.unop))
          rw [show
            (inferInstance :
              TopologicalSpace (E.unop ≃ₐ[K] E.unop)) =
                krullTopology K E.unop by
            change
              (⊥ : TopologicalSpace
                (E.unop ≃ₐ[K] E.unop)) =
                  krullTopology K E.unop
            exact
              (@DiscreteTopology.eq_bot _
                (krullTopology K E.unop)
                inferInstance).symm]
          exact hcontinuous E }

/-- The continuous global Artin homomorphism of an arbitrary abelian
Galois extension of a number field.  Its finite coordinates are the
finite global Artin homomorphisms. -/
noncomputable def infiniteGlobalArtinMonoidHom
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    IdeleGroup K →ₜ* (Ω ≃ₐ[K] Ω) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (InfiniteGalois.continuousMulEquivToLimit
      K Ω).symm).comp
    (infiniteGlobalArtinToLimit K Ω)

private theorem continuousMulEquivToLimit_infiniteGlobalArtinMonoidHom_apply'
    {K : Type u} {Ω : Type v}
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) :
    InfiniteGalois.continuousMulEquivToLimit K Ω
        (infiniteGlobalArtinMonoidHom K Ω a) =
      infiniteGlobalArtinToLimit K Ω a := by
  exact
    (InfiniteGalois.continuousMulEquivToLimit K Ω).apply_symm_apply _

/-- The infinite global Artin homomorphism kills the positive archimedean
section over every number field. -/
@[simp]
theorem infiniteGlobalArtinMonoidHom_positiveArchimedeanSection
    (K : Type u) (Ω : Type v)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (r : ℝ≥0ˣ) :
    infiniteGlobalArtinMonoidHom K Ω
        (IdeleGroup.positiveArchimedeanSection K r) =
      1 := by
  let
      (E : FiniteGaloisIntermediateField K Ω) :
      NumberField E :=
    NumberField.of_module_finite K E
  let
      (E : FiniteGaloisIntermediateField K Ω) :
      IsAbelianGalois K E :=
    IsAbelianGalois.of_algHom E.toIntermediateField.val
  apply
    (InfiniteGalois.continuousMulEquivToLimit K Ω).injective
  rw [
    continuousMulEquivToLimit_infiniteGlobalArtinMonoidHom_apply',
    map_one]
  apply Subtype.ext
  funext E
  exact
    globalArtinMonoidHom_positiveArchimedeanSection
      (K := K) (L := E.unop) r

/-- Every idele has the same infinite global Artin symbol as a norm-one
idele. -/
theorem exists_normOneIdele_same_infiniteGlobalArtin
    (K : Type u) (Ω : Type v)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) :
    ∃ b : IdeleGroup.normOneSubgroup (K := K),
      infiniteGlobalArtinMonoidHom K Ω b =
        infiniteGlobalArtinMonoidHom K Ω a := by
  refine
    ⟨IdeleGroup.positiveArchimedeanNormOneCorrection K a, ?_⟩
  rw [IdeleGroup.positiveArchimedeanNormOneCorrection_coe,
    map_mul,
    infiniteGlobalArtinMonoidHom_positiveArchimedeanSection,
    mul_one]

private theorem finiteGaloisLimit_proj_equiv_apply
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (E : FiniteGaloisIntermediateField K Ω) (sigma : Ω ≃ₐ[K] Ω) :
    InfiniteGalois.proj (k := K) (K := Ω) E
      (InfiniteGalois.continuousMulEquivToLimit K Ω sigma) =
      AlgEquiv.restrictNormalHom E sigma :=
  rfl

private theorem infiniteGlobalArtinToLimit_apply_component
    {K : Type u} {Ω : Type v} [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) (E : (FiniteGaloisIntermediateField K Ω)ᵒᵖ) :
    let : NumberField E.unop := NumberField.of_module_finite K E.unop
    (infiniteGlobalArtinToLimit K Ω a).val E =
      globalArtinMonoidHom (K := K) (L := E.unop) a := by
  intro numberFieldE
  rfl

private theorem infiniteGlobalArtinToLimit_proj_eq_finite
    {K : Type u} {Ω : Type v} [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) (E : FiniteGaloisIntermediateField K Ω) (hE : NumberField E) :
    let : NumberField E := hE
    InfiniteGalois.proj (k := K) (K := Ω) E (infiniteGlobalArtinToLimit K Ω a) =
      globalArtinMonoidHom (K := K) (L := E) a := by
  intro numberFieldE
  change (infiniteGlobalArtinToLimit K Ω a).val (op E) = _
  with_reducible exact infiniteGlobalArtinToLimit_apply_component a (op E)

/-- Projection of the infinite global Artin homomorphism to a finite
Galois intermediate field is exactly that field's finite global Artin
homomorphism, using a caller-supplied number-field witness. -/
@[simp]
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E) :
    let : NumberField E := hE
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom
        (K := K) (L := E) a := by
  intro numberFieldE
  let proj := InfiniteGalois.proj (k := K) (K := Ω) E
  let sigma := infiniteGlobalArtinMonoidHom K Ω a
  have h := continuousMulEquivToLimit_infiniteGlobalArtinMonoidHom_apply' (Ω := Ω) a
  exact (finiteGaloisLimit_proj_equiv_apply E sigma).symm.trans
    ((congrArg proj h).trans (infiniteGlobalArtinToLimit_proj_eq_finite a E hE))

/-- Finite projection with both finite-layer structures supplied explicitly.
This is useful when a concrete tower already has named canonical witnesses
and must not resynthesize them while checking the projected Artin endpoint. -/
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_of_structures
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    (hAbelian : IsAbelianGalois K E) :
    let : NumberField E := hE
    let : IsAbelianGalois K E := hAbelian
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom
        (K := K) (L := E) a := by
  intro sharedOwner1 sharedOwner2
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E hE

/-- Finite projection stated for a plain intermediate field with its finite
Galois structures supplied separately.  This avoids packaging a concrete
dependent field into `FiniteGaloisIntermediateField` at every call site. -/
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_of_intermediateField
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) (E : IntermediateField K Ω)
    [FiniteDimensional K E] [IsGalois K E]
    (hE : NumberField E)
    (hAbelian : IsAbelianGalois K E) :
    let : NumberField E := hE
    let : IsAbelianGalois K E := hAbelian
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom (K := K) (L := E) a := by
  intro numberFieldE abelianE
  let G : FiniteGaloisIntermediateField K Ω :=
    { toIntermediateField := E
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  have h := restrictNormalHom_infiniteGlobalArtinMonoidHom_of_structures
    K Ω a G hE hAbelian
  dsimp only [G] at h
  with_reducible exact h

/-- Finite projection for a plain intermediate field when its structures are
already installed as ambient instances. -/
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_intermediateField
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) (E : IntermediateField K Ω)
    [FiniteDimensional K E] [NumberField E] [IsAbelianGalois K E] :
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom (K := K) (L := E) a := by
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_intermediateField
      K Ω a E (inferInstance : NumberField E)
        (inferInstance : IsAbelianGalois K E)

/-- Pointwise form of finite projection of the infinite global Artin map.
This is the stable interface when a concrete finite layer carries algebra
instances propositionally, but not definitionally, equal to the canonical
intermediate-field instances. -/
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField_apply
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    (x : E) :
    let : NumberField E := hE
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) x =
      globalArtinMonoidHom
        (K := K) (L := E) a x := by
  intro sharedOwner1
  exact DFunLike.congr_fun
    (restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E hE) x

/-- Postcomposition of a finite projection of the infinite global Artin map.
Keeping `congrArg` at this generic level prevents large concrete towers from
being normalized merely to infer the endpoints of the mapped equality. -/
theorem map_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    {M : Type w} (f : (E ≃ₐ[K] E) → M) :
    let : NumberField E := hE
    f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)) =
      f (globalArtinMonoidHom
        (K := K) (L := E) a) := by
  intro sharedOwner1
  exact congrArg f
    (restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E hE)

/-- Postcomposition of a finite projection with both finite-layer structures
supplied explicitly.  This avoids resynthesizing proposition-valued instances
when the finite field is a concrete dependent intermediate field. -/
theorem map_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_structures
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    (hAbelian : IsAbelianGalois K E)
    {M : Type w} (f : (E ≃ₐ[K] E) → M) :
    let : NumberField E := hE
    let : IsAbelianGalois K E := hAbelian
    f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)) =
      f (globalArtinMonoidHom
        (K := K) (L := E) a) := by
  intro sharedOwner1 sharedOwner2
  exact congrArg f
    (restrictNormalHom_infiniteGlobalArtinMonoidHom_of_structures
      K Ω a E hE hAbelian)

/-- Postcomposition of the finite projection for a plain intermediate field.
The explicit structures keep concrete cyclotomic levels out of instance
normalization at the consumer. -/
theorem
    map_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_intermediateField
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) (E : IntermediateField K Ω)
    [FiniteDimensional K E] [IsGalois K E]
    (hE : NumberField E)
    (hAbelian : IsAbelianGalois K E)
    {M : Type w} (f : (E ≃ₐ[K] E) → M) :
    let : NumberField E := hE
    let : IsAbelianGalois K E := hAbelian
    f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)) =
      f (globalArtinMonoidHom (K := K) (L := E) a) := by
  intro sharedOwner1 sharedOwner2
  exact congrArg f
    (restrictNormalHom_infiniteGlobalArtinMonoidHom_of_intermediateField
      K Ω a E hE hAbelian)

/-- The finite global Artin homomorphism with its number-field witness fixed
as an explicit argument.  Concrete intermediate-field towers can share this
opaque hom without repeatedly comparing independently synthesized witnesses. -/
noncomputable def globalArtinMonoidHomOfNumberField
    (K : Type u) (L : Type v) [Field K] [NumberField K]
    [Field L] [Algebra K L] [IsAbelianGalois K L]
    (hL : NumberField L) :
    IdeleGroup K →* (L ≃ₐ[K] L) := by
  letI : NumberField L := hL
  exact globalArtinMonoidHom (K := K) (L := L)

/-- Norm-restriction naturality with the upper finite global Artin homomorphism
expressed through an explicit number-field witness. -/
theorem globalArtinMonoidHomOfNumberField_norm_restriction
    (K : Type u) (L : Type v) (K' : Type w) (L' : Type x)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    [Field K'] [NumberField K']
    [Field L'] [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (hL' : NumberField L') :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (globalArtinMonoidHomOfNumberField K' L' hL') =
      (globalArtinMonoidHom (K := K) (L := L)).comp
        (IdeleGroup.norm K K') := by
  let : NumberField L' := hL'
  exact globalArtinMonoidHom_norm_restriction

/-- Monoid-hom postcomposition of a finite projection, stated at the hom
application level.  This keeps concrete consumers from unfolding
`MonoidHom.comp` merely to join the projection and finite Artin endpoints. -/
theorem comp_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    {M : Type w} [Monoid M]
    (f : (E ≃ₐ[K] E) →* M) :
    let : NumberField E := hE
    f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)) =
      (f.comp (globalArtinMonoidHomOfNumberField K E hE)) a := by
  intro sharedOwner1
  exact
    (map_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E hE f).trans rfl

/-- The mapped finite projection and its finite Artin specification, with
both endpoints fixed while the ambient field instances are still generic.
Concrete towers can reuse the package without asking the elaborator to
normalize those instances while checking the equality again. -/
noncomputable def
    compRestrictNormalHomInfiniteGlobalArtinDataOfNumberField
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    {M : Type w} [Monoid M]
    (f : (E ≃ₐ[K] E) →* M) :
    let : NumberField E := hE
    {x : M //
      x = (f.comp
        (globalArtinMonoidHomOfNumberField K E hE)) a} := by
  intro sharedOwner1
  exact
    ⟨f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)),
      comp_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
        K Ω a E hE f⟩

/-- The mapped infinite projection transported through a supplied naturality
square.  The intermediate finite Artin hom is the explicit-witness version,
so the equality is composed once in this generic provider rather than by a
concrete dependent field tower. -/
noncomputable def
    compRestrictNormalHomInfiniteGlobalArtinNaturalityDataOfNumberField
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    {M : Type w} [Monoid M]
    (f : (E ≃ₐ[K] E) →* M)
    (g : IdeleGroup K →* M)
    (hnat :
      f.comp (globalArtinMonoidHomOfNumberField K E hE) = g) :
    let : NumberField E := hE
    {x : M // x = g a} := by
  intro sharedOwner1
  have hprojection :=
    comp_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E hE f
  exact
    ⟨f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)),
      hprojection.trans (DFunLike.congr_fun hnat a)⟩

/-- Postcomposition of a finite projection when the finite layer's number
field structure is already installed as the ambient instance. -/
theorem map_restrictNormalHom_infiniteGlobalArtinMonoidHom
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    [NumberField E]
    {M : Type w} (f : (E ≃ₐ[K] E) → M) :
    f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)) =
      f (globalArtinMonoidHom
        (K := K) (L := E) a) :=
  congrArg f
    (restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E (inferInstance : NumberField E))

/-- Projection of the infinite global Artin homomorphism to a finite
Galois intermediate field, with its canonical module-finite number-field
structure. -/
@[simp]
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω) :
    letI : NumberField E :=
      NumberField.of_module_finite K E
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom
        (K := K) (L := E) a := by
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E (NumberField.of_module_finite K E)

/-- Restriction of the infinite global Artin map along an abstract finite
abelian scalar tower.  Unlike the intermediate-field projection theorem, this
form allows the finite extension to be supplied through any chosen embedding
into the ambient infinite extension. -/
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_of_scalarTower
    (K : Type u) (E : Type w) (Ω : Type v) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E]
    [IsAbelianGalois K E]
    [Field Ω] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) :
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom (K := K) (L := E) a := by
  let j : E →ₐ[K] Ω := IsScalarTower.toAlgHom K E Ω
  let G : FiniteGaloisIntermediateField K Ω :=
    j.finiteGaloisFieldRange
  let _ : FiniteDimensional K G := G.finiteDimensional
  let _ : NumberField G :=
    NumberField.of_module_finite K G
  let _ : IsAbelianGalois K G :=
    IsAbelianGalois.of_algHom G.toIntermediateField.val
  let _ : Algebra E G :=
    j.equivFieldRange.toRingHom.toAlgebra
  let _ : SMul E G := Algebra.toSMul
  let _ : IsScalarTower K E G :=
    IsScalarTower.of_algHom j.equivFieldRange.toAlgHom
  let _ : IsScalarTower K G Ω :=
    IntermediateField.isScalarTower_mid G.toIntermediateField
  let _ : IsScalarTower E G Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hProjection :
      AlgEquiv.restrictNormalHom G
          (infiniteGlobalArtinMonoidHom K Ω a) =
        globalArtinMonoidHom (K := K) (L := G) a :=
    restrictNormalHom_infiniteGlobalArtinMonoidHom K Ω a G
  calc
    AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom K Ω a) =
        AlgEquiv.restrictNormalHom E
          (AlgEquiv.restrictNormalHom G
            (infiniteGlobalArtinMonoidHom K Ω a)) :=
      IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E G
        (infiniteGlobalArtinMonoidHom K Ω a)
    _ = AlgEquiv.restrictNormalHom E
          (globalArtinMonoidHom (K := K) (L := G) a) :=
      congrArg (AlgEquiv.restrictNormalHom E) hProjection
    _ = globalArtinMonoidHom (K := K) (L := E) a :=
      DFunLike.congr_fun
        (globalArtinMonoidHom_restrict_tower
          (K := K) (L := G) (E := E)) a

/-- Finite global reciprocity at every coordinate makes the infinite
global Artin homomorphism dense in the Krull topology. -/
theorem infiniteGlobalArtinMonoidHom_denseRange
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    DenseRange (infiniteGlobalArtinMonoidHom K Ω) := by
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨σ, hσU⟩
  let V : Set (Ω ≃ₐ[K] Ω) :=
    (Homeomorph.mulLeft σ) ⁻¹' U
  have hVopen : IsOpen V :=
    hU.preimage (Homeomorph.mulLeft σ).continuous
  have hVone : (1 : Ω ≃ₐ[K] Ω) ∈ V := by
    change σ * 1 ∈ U
    simpa using hσU
  have hVnhds :
      V ∈ 𝓝 (1 : Ω ≃ₐ[K] Ω) :=
    hVopen.mem_nhds hVone
  obtain ⟨E, hEV⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
        (k := K) (K := Ω) V).mp
      hVnhds
  let : NumberField E :=
    NumberField.of_module_finite K E
  obtain ⟨a, ha⟩ :=
    globalArtinMonoidHom_surjective
      (K := K) (L := E)
      (AlgEquiv.restrictNormalHom E σ)
  have hfix :
      σ⁻¹ * infiniteGlobalArtinMonoidHom K Ω a ∈
        E.fixingSubgroup := by
    rw [
      FiniteGaloisIntermediateField.mem_fixingSubgroup_iff,
      map_mul, map_inv,
      restrictNormalHom_infiniteGlobalArtinMonoidHom,
      ha, inv_mul_cancel]
  have hmemV :
      σ⁻¹ * infiniteGlobalArtinMonoidHom K Ω a ∈ V :=
    hEV hfix
  refine
    ⟨infiniteGlobalArtinMonoidHom K Ω a, ?_,
      ⟨a, rfl⟩⟩
  simpa [V, mul_assoc] using hmemV

/-- The actual continuous global Artin homomorphism from rational ideles
to the Galois group of the `ZHat`-extension of `ℚ`. -/
noncomputable def rationalCyclotomicZHatGlobalArtin :
    IdeleGroup ℚ →ₜ*
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :=
  infiniteGlobalArtinMonoidHom ℚ rationalCyclotomicZHatField

/-- Projection of the rational `ZHat` Artin homomorphism is the finite
global Artin homomorphism. -/
@[simp]
theorem restrictNormalHom_rationalCyclotomicZHatGlobalArtin
    (a : IdeleGroup ℚ)
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    letI : NumberField E :=
      NumberField.of_module_finite ℚ E
    letI : IsAbelianGalois ℚ E :=
      IsAbelianGalois.of_algHom E.toIntermediateField.val
    AlgEquiv.restrictNormalHom E
        (rationalCyclotomicZHatGlobalArtin a) =
      globalArtinMonoidHom
        (K := ℚ) (L := E) a :=
  restrictNormalHom_infiniteGlobalArtinMonoidHom
    ℚ rationalCyclotomicZHatField a E

/-- Rational cyclotomic projection with caller-supplied finite-layer
structures. -/
theorem restrictNormalHom_rationalCyclotomicZHatGlobalArtin_of_structures
    (a : IdeleGroup ℚ)
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (hE : NumberField E)
    (hAbelian : IsAbelianGalois ℚ E) :
    let : NumberField E := hE
    let : IsAbelianGalois ℚ E := hAbelian
    AlgEquiv.restrictNormalHom E
        (rationalCyclotomicZHatGlobalArtin a) =
      globalArtinMonoidHom
        (K := ℚ) (L := E) a := by
  intro sharedOwner1 sharedOwner2
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_structures
      ℚ rationalCyclotomicZHatField a E hE hAbelian

/-- A mapped relative infinite Artin projection, the corresponding rational
finite Artin value, and the rational infinite projection, packaged with both
comparison steps.  The common finite value is generated only once in this
generic provider, so concrete dependent towers never compare separately
elaborated finite-field structures. -/
noncomputable def
    compRestrictNormalHomInfiniteGlobalArtinRationalCyclotomicDataOfNumberField
    (K : Type u) (Ω : Type v) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E' : FiniteGaloisIntermediateField K Ω)
    (hE' : NumberField E')
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (hE : NumberField E)
    (hAbelian : IsAbelianGalois ℚ E)
    (f : (E' ≃ₐ[K] E') →* Gal(E/ℚ))
    (hnat :
      letI : NumberField E' := hE'
      letI : NumberField E := hE
      letI : IsAbelianGalois ℚ E := hAbelian
      f.comp (globalArtinMonoidHomOfNumberField K E' hE') =
        (globalArtinMonoidHom (K := ℚ) (L := E)).comp
          (IdeleGroup.norm ℚ K)) :
    let : NumberField E' := hE'
    let : NumberField E := hE
    let : IsAbelianGalois ℚ E := hAbelian
    {x : Gal(E / ℚ) × Gal(E / ℚ) × Gal(E / ℚ) //
      x.1 = x.2.1 ∧ x.2.1 = x.2.2} := by
  intro sharedOwner1 sharedOwner2 sharedOwner3
  let relativeData :=
    compRestrictNormalHomInfiniteGlobalArtinNaturalityDataOfNumberField
      K Ω a E' hE' f
      ((globalArtinMonoidHom (K := ℚ) (L := E)).comp
        (IdeleGroup.norm ℚ K))
      hnat
  have hcomp :
      ((globalArtinMonoidHom (K := ℚ) (L := E)).comp
        (IdeleGroup.norm ℚ K)) a =
        globalArtinMonoidHom (K := ℚ) (L := E)
          (IdeleGroup.norm ℚ K a) :=
    rfl
  exact
    ⟨(relativeData.1,
        ((globalArtinMonoidHom (K := ℚ) (L := E)).comp
          (IdeleGroup.norm ℚ K)) a,
        AlgEquiv.restrictNormalHom E
          (rationalCyclotomicZHatGlobalArtin
            (IdeleGroup.norm ℚ K a))),
      relativeData.2,
      hcomp.trans
        (restrictNormalHom_rationalCyclotomicZHatGlobalArtin_of_structures
          (IdeleGroup.norm ℚ K a) E hE hAbelian).symm⟩

/-- The rational `ZHat` specialization has dense Artin image. -/
theorem rationalCyclotomicZHatGlobalArtin_denseRange :
    DenseRange rationalCyclotomicZHatGlobalArtin :=
  infiniteGlobalArtinMonoidHom_denseRange
    ℚ rationalCyclotomicZHatField

/-- The norm-one rational ideles already have dense Artin image. -/
theorem rationalCyclotomicZHatGlobalArtin_normOne_denseRange :
    DenseRange
      (fun b : IdeleGroup.normOneSubgroup (K := ℚ) =>
        rationalCyclotomicZHatGlobalArtin b) := by
  apply rationalCyclotomicZHatGlobalArtin_denseRange.mono
  rintro σ ⟨a, rfl⟩
  obtain ⟨b, hb⟩ :=
    exists_normOneIdele_same_infiniteGlobalArtin ℚ rationalCyclotomicZHatField a
  exact ⟨b, hb⟩

end Reciprocity
end GlobalClassFieldTheory
