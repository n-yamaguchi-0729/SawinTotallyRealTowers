/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitNormContainment
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Principal
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormProperties
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Cardinality
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.FixedCycles
public import Nyll.GaloisCohomology.Cyclic.Herbrand.FieldUnits
public import Nyll.ProCGroups.GroupTheory.Exactness
public import Nyll.GaloisCohomology.Cyclic.TateH0.Main
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.LocalNormTransport
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
public import Nyll.ClassFieldTheory.Algebra.ShrinkFiniteExtension
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.GlobalNorm
public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.IsFieldNorm
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.CohomologyBridge
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.PrincipalSequence
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.EquivariantEquiv
public import Nyll.GaloisCohomology.Cyclic.TateComparison
public import Nyll.GaloisCohomology.Cyclic.TateH0.Invariants
public import Nyll.GaloisCohomology.Cyclic.TateH0.NormImage
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient

/-!
# The Hasse norm principle: the concrete local-global map

This file proves the Hasse norm principle on the actual idele and field norm
maps.  The local condition is expressed canonically:
at a place `v` it is the image of the determinant norm on
`K_v ⊗[K] L`.  At finite places this is the chosen completion norm
subgroup by
`_root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup`.

The resulting homomorphism

`Kˣ / N(Lˣ) ⟶ I_K / I_K,loc-norm`

is the concrete diagonal local-norm map.  Its injectivity is exactly the
Hasse norm principle.  The global-to-local inclusion and this equivalence
are independent of the global class-field axiom; the reverse inclusion
follows from degree-minus-one Tate-cohomology vanishing.
-/



@[expose] public section

open LocalFieldTheory (localNormSubgroup)

open scoped NumberField TensorProduct
open NumberField

noncomputable section

universe u v

namespace GlobalClassFieldTheory.ClassFieldAxiom

open CategoryTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand

/-- Ideles whose component at every infinite place lies in the image of
the determinant norm on the corresponding archimedean local tensor
algebra. -/
def allInfinitePlaceLocalNormCondition
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
  [FiniteDimensional K L] :
    Subgroup (IdeleGroup K) :=
  ⨅ v : InfinitePlace K,
    (Units.map
      (Algebra.norm v.Completion :
        (v.Completion ⊗[K] L) →* v.Completion)).range.comap
      (IdeleGroup.infiniteComponent v)

/-- The simultaneous determinant-norm condition at every finite and
infinite place. -/
def allPlaceLocalNormCondition
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Subgroup (IdeleGroup K) :=
  allFinitePlaceLocalNormCondition (K := K) (L := L) ⊓
    allInfinitePlaceLocalNormCondition (K := K) (L := L)

/-- Every global relative-idele norm is a local determinant norm at every
place. -/
theorem relativeIdeleNorm_range_le_allPlaceLocalNormCondition
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (RelativeIdeleGroup.norm K L).range ≤
      allPlaceLocalNormCondition (K := K) (L := L) := by
  intro a ha
  refine ⟨relativeIdeleNorm_range_le_allFinitePlaceLocalNormCondition
      (K := K) (L := L) ha, ?_⟩
  rcases ha with ⟨b, rfl⟩
  rw [allInfinitePlaceLocalNormCondition]
  apply Subgroup.mem_iInf.mpr
  intro v
  exact
    ⟨RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) v b,
      (RelativeIdeleGroup.infiniteComponent_norm
        (K := K) (L := L) v b).symm⟩

/-- An idele is a relative-idele norm exactly when every one of its
finite and infinite components is a determinant norm.  The nontrivial
reverse inclusion uses the restricted-product preimage construction:
integral local preimages are chosen at almost every finite place. -/
theorem relativeIdeleNorm_range_eq_allPlaceLocalNormCondition
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (RelativeIdeleGroup.norm K L).range =
      allPlaceLocalNormCondition (K := K) (L := L) := by
  apply le_antisymm
  · exact
      relativeIdeleNorm_range_le_allPlaceLocalNormCondition
        (K := K) (L := L)
  · intro a ha
    apply
      (_root_.mem_relativeIdeleNorm_range_iff_localTensorNorms
        (K := K) (L := L) a).2
    constructor
    · intro v
      have hv :
          IdeleGroup.infiniteComponent v a ∈
            (Units.map
              (Algebra.norm v.Completion :
                (v.Completion ⊗[K] L) →* v.Completion)).range := by
        exact
          Subgroup.mem_iInf.mp
            (show
              a ∈ allInfinitePlaceLocalNormCondition
                (K := K) (L := L) from ha.2) v
      simpa [_root_.infiniteTensorNormSubgroup,
        _root_.infiniteTensorDetNorm] using hv
    · intro v
      have hv :
          IdeleGroup.finiteComponent v a ∈
            _root_.chosenFinitePlaceLocalNormSubgroup
              (K := K) (L := L) v := by
        exact
          Subgroup.mem_iInf.mp
            (show
              a ∈ allFinitePlaceLocalNormCondition
                (K := K) (L := L) from ha.1) v
      rw [
        _root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup]
      exact hv

/-- Base-field units that are determinant norms at every completion. -/
def everywhereLocalFieldNormSubgroup
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Subgroup Kˣ :=
  (allPlaceLocalNormCondition (K := K) (L := L)).comap
    (IdeleGroup.principalIdele K)

theorem isFieldNorm_iff_mem_globalFieldNormSubgroup
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (x : Kˣ) :
    ClassFieldTheory.IsFieldNorm K L x ↔
      x ∈ localNormSubgroup K L :=
  Iff.rfl

theorem isNormAtFinitePlace_iff
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    ClassFieldTheory.IsNormAtFinitePlace K L w x ↔
      IdeleGroup.finiteComponent w (IdeleGroup.principalIdele K x) ∈
        chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) w := by
  rw [← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
    (K := K) (L := L) w]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply Units.ext
    calc
      Algebra.norm (w.adicCompletion K)
          (y : w.adicCompletion K ⊗[K] L) =
          algebraMap K (w.adicCompletion K) (x : K) := hy
      _ = (IdeleGroup.finiteComponent w
          (IdeleGroup.principalIdele K x) : w.adicCompletion K) :=
        (IdeleGroup.finiteComponent_principalIdele x w).symm
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    calc
      Algebra.norm (w.adicCompletion K)
          (y : w.adicCompletion K ⊗[K] L) =
          (IdeleGroup.finiteComponent w
            (IdeleGroup.principalIdele K x) : w.adicCompletion K) :=
        congrArg Units.val hy
      _ = algebraMap K (w.adicCompletion K) (x : K) :=
        IdeleGroup.finiteComponent_principalIdele x w

theorem isNormAtInfinitePlace_iff
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (w : InfinitePlace K) (x : Kˣ) :
    ClassFieldTheory.IsNormAtInfinitePlace K L w x ↔
      IdeleGroup.infiniteComponent w (IdeleGroup.principalIdele K x) ∈
        (Units.map
          (Algebra.norm w.Completion :
            (w.Completion ⊗[K] L) →* w.Completion)).range := by
  have hcast : algebraMap K w.Completion (x : K) = ((x : K) : w.Completion) := by
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      Algebra.algebraMap_self_apply]
  have hcomponent := (IdeleGroup.infiniteComponent_principalIdele x w).trans hcast.symm
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply Units.ext
    calc
      Algebra.norm w.Completion (y : w.Completion ⊗[K] L) =
          algebraMap K w.Completion (x : K) := hy
      _ = (IdeleGroup.infiniteComponent w
          (IdeleGroup.principalIdele K x) : w.Completion) :=
        hcomponent.symm
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    calc
      Algebra.norm w.Completion (y : w.Completion ⊗[K] L) =
          (IdeleGroup.infiniteComponent w
            (IdeleGroup.principalIdele K x) : w.Completion) :=
        congrArg Units.val hy
      _ = algebraMap K w.Completion (x : K) :=
        hcomponent

theorem isEverywhereLocalNorm_iff_mem_everywhereLocalFieldNormSubgroup
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (x : Kˣ) :
    ClassFieldTheory.IsEverywhereLocalNorm K L x ↔
      x ∈ GlobalClassFieldTheory.ClassFieldAxiom.everywhereLocalFieldNormSubgroup K L := by
  constructor
  · rintro ⟨hfinite, hinfinite⟩
    change IdeleGroup.principalIdele K x ∈
      GlobalClassFieldTheory.ClassFieldAxiom.allPlaceLocalNormCondition
        (K := K) (L := L)
    constructor
    · rw [GlobalClassFieldTheory.ClassFieldAxiom.allFinitePlaceLocalNormCondition]
      apply Subgroup.mem_iInf.mpr
      intro w
      exact (isNormAtFinitePlace_iff K L w x).mp (hfinite w)
    · rw [GlobalClassFieldTheory.ClassFieldAxiom.allInfinitePlaceLocalNormCondition]
      apply Subgroup.mem_iInf.mpr
      intro w
      exact (isNormAtInfinitePlace_iff K L w x).mp (hinfinite w)
  · intro hx
    change IdeleGroup.principalIdele K x ∈
      GlobalClassFieldTheory.ClassFieldAxiom.allPlaceLocalNormCondition
        (K := K) (L := L) at hx
    constructor
    · intro w
      apply (isNormAtFinitePlace_iff K L w x).mpr
      exact Subgroup.mem_iInf.mp
        (show IdeleGroup.principalIdele K x ∈
          GlobalClassFieldTheory.ClassFieldAxiom.allFinitePlaceLocalNormCondition
            (K := K) (L := L) from hx.1) w
    · intro w
      apply (isNormAtInfinitePlace_iff K L w x).mpr
      exact Subgroup.mem_iInf.mp
        (show IdeleGroup.principalIdele K x ∈
          GlobalClassFieldTheory.ClassFieldAxiom.allInfinitePlaceLocalNormCondition
            (K := K) (L := L) from hx.2) w

/-- A global field norm remains the same determinant norm at every completion. -/
theorem globalFieldNormSubgroup_le_everywhereLocalFieldNormSubgroup
    {K : Type u} {L : Type v}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    localNormSubgroup K L ≤ everywhereLocalFieldNormSubgroup K L := by
  intro x hx
  exact (isEverywhereLocalNorm_iff_mem_everywhereLocalFieldNormSubgroup K L x).mp
    (ClassFieldTheory.globalNorm_isEverywhereLocalNorm K L x
      ((isFieldNorm_iff_mem_globalFieldNormSubgroup K L x).mpr hx))

/-- The map
`H⁰(G, P_L) → H⁰(G, I_L)` induced by the actual inclusion of principal
relative ideles. -/
noncomputable def principalIdeleHerbrandH0Map_native
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let :=
      RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
    let :=
      RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
    HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L) →*
      HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup K L) := by
  intro sharedOwner1 sharedOwner2
  let f :=
    equivariantRepHom
      (RelativeIdeleGroup.principalSubgroup K L).subtype
      (RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant K L)
  let eP :=
    (tateH0IsoHerbrandH0
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.principalSubgroup K L)).toLinearEquiv
      |>.toAddEquiv.toMultiplicative
  let eI :=
    (tateH0IsoHerbrandH0
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup K L)).toLinearEquiv
      |>.toAddEquiv.toMultiplicative
  exact eI.toMonoidHom.comp <|
    ((tateCohomologyFunctor 0).map f).hom.toAddMonoidHom.toMultiplicative.comp
      eP.symm.toMonoidHom

private theorem principalIdeleHerbrandH0Map_native_mk
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let :=
      RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
    let :=
      RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
    ∀ a : fixedSubgroup (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L),
      principalIdeleHerbrandH0Map_native K L (HerbrandH0.mk a) =
        HerbrandH0.mk
          (⟨(RelativeIdeleGroup.principalSubgroup K L).subtype a,
            fun σ ↦ by
              rw [← RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant
                K L σ a, a.2 σ]⟩ :
            fixedSubgroup (L ≃ₐ[K] L) (RelativeIdeleGroup K L)) := by
  intro sharedOwner1 sharedOwner2 a
  exact congrArg Additive.toMul
    (tateH0IsoHerbrandH0_map_mk (G := L ≃ₐ[K] L)
      (RelativeIdeleGroup.principalSubgroup K L).subtype
      (RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant K L) a)

/-- Inclusion of the actual principal ideles induces a map on the fixed
point quotients in independent universes. -/
noncomputable def principalIdeleHerbrandH0Map
    (K : Type u) (L : Type v)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let := RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
    let := RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
    HerbrandH0 (L ≃ₐ[K] L) (RelativeIdeleGroup.principalSubgroup K L) →*
      HerbrandH0 (L ≃ₐ[K] L) (RelativeIdeleGroup K L) := by
  intro hI hP
  let P := RelativeIdeleGroup.principalSubgroup K L
  let f : fixedSubgroup (L ≃ₐ[K] L) P →*
      fixedSubgroup (L ≃ₐ[K] L) (RelativeIdeleGroup K L) :=
    { toFun := fun a => ⟨P.subtype a, fun σ => by
        rw [← RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant
          K L σ a, a.2 σ]⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  refine HerbrandH0.lift (HerbrandH0.mk.comp f) ?_
  intro a ha
  change HerbrandH0.mk (f a) = 1
  apply (HerbrandH0.mk_eq_one_iff (f a)).mpr
  obtain ⟨z, hz⟩ := ha
  refine ⟨P.subtype z, ?_⟩
  change tateNorm (L ≃ₐ[K] L) (RelativeIdeleGroup K L) (P.subtype z) = P.subtype a
  exact (map_tateNorm P.subtype
    (RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant K L) z).symm.trans
      (congrArg P.subtype hz)

/-- The quotient map retains the original principal-idele inclusion on every representative. -/
theorem principalIdeleHerbrandH0Map_mk
    (K : Type u) (L : Type v)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let := RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
    let := RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
    ∀ a : fixedSubgroup (L ≃ₐ[K] L) (RelativeIdeleGroup.principalSubgroup K L),
      principalIdeleHerbrandH0Map K L (HerbrandH0.mk a) =
        HerbrandH0.mk
          (⟨(RelativeIdeleGroup.principalSubgroup K L).subtype a, fun σ => by
            rw [← RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant
              K L σ a, a.2 σ]⟩ :
            fixedSubgroup (L ≃ₐ[K] L) (RelativeIdeleGroup K L)) := by
  intro hI hP a
  rfl

/-- The original native Tate map is precisely the map on actual fixed
point quotient classes, so its connecting-map exactness is retained. -/
theorem principalIdeleHerbrandH0Map_eq_native
    (K L : Type)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let := RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
    let := RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
    principalIdeleHerbrandH0Map K L = principalIdeleHerbrandH0Map_native K L := by
  intro hI hP
  apply MonoidHom.ext
  intro q
  obtain ⟨a, rfl⟩ := HerbrandH0.mk_surjective q
  exact (principalIdeleHerbrandH0Map_mk K L a).trans
    (principalIdeleHerbrandH0Map_native_mk K L a).symm

section IdeleClassConnecting

attribute [local instance]
  RelativeIdeleGroup.relativeIdeleMulDistribMulAction
  RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction
  RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction

/-- The low-degree connecting homomorphism
`H⁻¹(G, C_L) → H⁰(G, P_L)` attached to
`1 → P_L → I_L → C_L → 1`. -/
noncomputable def ideleClassToPrincipalConnecting
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    letI :=
      RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
    Multiplicative
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1)) →*
      HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L) := by
  let S := RelativeIdeleGroup.Cohomology.principalIdeleShortComplex K L
  have hS : S.ShortExact :=
    RelativeIdeleGroup.Cohomology.principalIdeleShortComplex_shortExact K L
  let eP :=
    (tateH0IsoHerbrandH0
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.principalSubgroup K L)).toLinearEquiv
      |>.toAddEquiv.toMultiplicative
  exact eP.toMonoidHom.comp <|
    (TateCohomology.δ hS (-1)).hom.toAddMonoidHom.toMultiplicative

/-- Exactness of the concrete low-degree sequence: the image of
`H⁻¹(G,C_L)` is precisely the kernel of
`H⁰(G,P_L) → H⁰(G,I_L)`. -/
theorem ideleClassToPrincipalConnecting_range_eq_ker
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    letI :=
      RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
    MonoidHom.range (ideleClassToPrincipalConnecting K L) =
      MonoidHom.ker (principalIdeleHerbrandH0Map K L) := by
  let S := RelativeIdeleGroup.Cohomology.principalIdeleShortComplex K L
  have hS : S.ShortExact :=
    RelativeIdeleGroup.Cohomology.principalIdeleShortComplex_shortExact K L
  let δm :=
    (TateCohomology.δ hS (-1)).hom.toAddMonoidHom.toMultiplicative
  let fm :=
    ((tateCohomologyFunctor 0).map S.f).hom.toAddMonoidHom.toMultiplicative
  let eP :=
    (tateH0IsoHerbrandH0
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.principalSubgroup K L)).toLinearEquiv
      |>.toAddEquiv.toMultiplicative
  let eI :=
    (tateH0IsoHerbrandH0
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup K L)).toLinearEquiv
      |>.toAddEquiv.toMultiplicative
  let connecting := eP.toMonoidHom.comp δm
  let principal :=
    eI.toMonoidHom.comp (fm.comp eP.symm.toMonoidHom)
  have hbase : Function.MulExact δm fm := by
    apply
      CyclicCohomology.ProfiniteCohomology.Herbrand.mulExact_of_moduleCat_shortComplex_exact
    · simpa using TateCohomology.exact₁ hS (-1)
  have htarget : Function.MulExact connecting principal := by
    exact
      Function.mulExact_transport_mulEquiv δm fm eP eI hbase
  rw [principalIdeleHerbrandH0Map_eq_native]
  change MonoidHom.range connecting = MonoidHom.ker principal
  exact htarget.monoidHom_ker_eq.symm

end IdeleClassConnecting

/-- Degree-zero Tate cohomology of the actual field-unit action is the
concrete global norm quotient `Kˣ / N_{L/K}(Lˣ)`. -/
noncomputable def fieldUnitsHerbrandH0EquivGlobalNormQuotient
    (K : Type u) (L : Type v)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let := LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    HerbrandH0 (L ≃ₐ[K] L) Lˣ ≃* Kˣ ⧸ localNormSubgroup K L := by
  intro sharedOwner
  exact (CyclicCohomology.herbrandH0UnitsEquivNormQuotient K L).trans
    (LocalFieldTheory.normQuotientConcreteEquiv K L)

/-- The comparison sends an actual fixed unit to the original norm class
of its descended base-field unit. -/
theorem fieldUnitsHerbrandH0EquivGlobalNormQuotient_mk
    (K : Type u) (L : Type v)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let := LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    ∀ a : fixedSubgroup (L ≃ₐ[K] L) Lˣ,
      fieldUnitsHerbrandH0EquivGlobalNormQuotient K L (HerbrandH0.mk a) =
        QuotientGroup.mk' (localNormSubgroup K L)
          (Additive.toMul (CyclicCohomology.invariantsUnitsAddEquivBaseUnits K L
            (LocalClassFieldTheory.additiveFixedUnitsEquivInvariants K L
              (Additive.ofMul a)))) := by
  intro hAction a
  rfl

/-- The map on degree-zero Tate cohomology induced by the actual diagonal
embedding `Lˣ → I_L`. -/
noncomputable def fieldUnitsToRelativeIdeleHerbrandH0
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let :=
      LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    let :=
      RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
    HerbrandH0 (L ≃ₐ[K] L) Lˣ →*
      HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup K L) := by
  intro sharedOwner1 sharedOwner2
  letI :=
    RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
  exact
    (principalIdeleHerbrandH0Map K L).comp
      (fieldUnitsHerbrandH0EquivPrincipalIdeles
        K L).toMonoidHom

/-- A base-field unit, regarded as a Galois-fixed unit of the extension
field. -/
noncomputable def baseFieldUnitAsFixedUnit
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (x : Kˣ) :
    let _ : MulDistribMulAction (L ≃ₐ[K] L) Lˣ :=
      LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    fixedSubgroup (L ≃ₐ[K] L) Lˣ := by
  intro unitAction
  refine
    ⟨Units.map (algebraMap K L) x, ?_⟩
  intro σ
  apply Units.ext
  change σ (algebraMap K L (x : K)) = algebraMap K L (x : K)
  exact σ.commutes (x : K)

/-- If the principal idele of a base-field unit is an actual relative
idele norm, its field-unit Tate class maps trivially to relative-idele
Tate cohomology. -/
theorem fieldUnitsHerbrandH0_map_baseFieldUnit_eq_one_of_mem_norm
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (x : Kˣ)
    (hx :
      IdeleGroup.principalIdele K x ∈
        (RelativeIdeleGroup.norm K L).range) :
    let :=
      LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    let :=
      RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
    fieldUnitsToRelativeIdeleHerbrandH0 K L
        (HerbrandH0.mk (baseFieldUnitAsFixedUnit K L x)) = 1 := by
  intro sharedOwner1 sharedOwner2
  let :=
    RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
  let aP :
      fixedSubgroup (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L) :=
    CyclicCohomology.fixedSubgroupEquivariantMulEquiv
      (fieldUnitsEquivPrincipalIdeles K L)
      (fieldUnitsEquivPrincipalIdeles_smul K L)
      (baseFieldUnitAsFixedUnit K L x)
  let aI :
      fixedSubgroup (L ≃ₐ[K] L) (RelativeIdeleGroup K L) :=
    ⟨(RelativeIdeleGroup.principalSubgroup K L).subtype aP, fun σ ↦ by
      rw [← RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant
        K L σ aP, aP.2 σ]⟩
  have hmk : HerbrandH0.mk aI = 1 := by
    apply (HerbrandH0.mk_eq_one_iff aI).2
    obtain ⟨z, hz⟩ := hx
    refine ⟨z, ?_⟩
    change
      tateNorm (L ≃ₐ[K] L) (RelativeIdeleGroup K L) z =
        (aI : RelativeIdeleGroup K L)
    dsimp only [aP,
      aI,
      CyclicCohomology.fixedSubgroupEquivariantMulEquiv,
      fieldUnitsEquivPrincipalIdeles]
    rw [RelativeIdeleGroup.Cohomology.relativeIdele_tateNorm_eq_inclusion_norm,
      hz, RelativeIdeleGroup.inclusion_principalIdele]
    rfl
  have hmap :
      fieldUnitsToRelativeIdeleHerbrandH0 K L
          (HerbrandH0.mk (baseFieldUnitAsFixedUnit K L x)) =
        HerbrandH0.mk aI := by
    have hfield :
        fieldUnitsHerbrandH0EquivPrincipalIdeles K L
            (HerbrandH0.mk (baseFieldUnitAsFixedUnit K L x)) =
          HerbrandH0.mk aP := by
      simpa only [fieldUnitsHerbrandH0EquivPrincipalIdeles, aP] using
        CyclicCohomology.herbrandH0EquivariantMulEquiv_mk
          (fieldUnitsEquivPrincipalIdeles K L)
          (fieldUnitsEquivPrincipalIdeles_smul K L)
          (baseFieldUnitAsFixedUnit K L x)
    change
      principalIdeleHerbrandH0Map K L
          (fieldUnitsHerbrandH0EquivPrincipalIdeles K L
            (HerbrandH0.mk (baseFieldUnitAsFixedUnit K L x))) =
        HerbrandH0.mk aI
    rw [hfield]
    simpa only [aI] using
      principalIdeleHerbrandH0Map_mk K L aP
  exact hmap.trans hmk

/-- The connecting map in the low-degree sequence, with its target
transported from principal ideles back to the actual field-unit
cohomology. -/
noncomputable def ideleClassToFieldUnitsConnecting
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let :=
      LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    let :=
      RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
    Multiplicative
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1)) →*
      HerbrandH0 (L ≃ₐ[K] L) Lˣ := by
  intro sharedOwner1 sharedOwner2
  letI :=
    RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
  letI :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  exact
    (fieldUnitsHerbrandH0EquivPrincipalIdeles
      K L).symm.toMonoidHom.comp
        (ideleClassToPrincipalConnecting K L)

/-- Exactness after replacing `H⁰(G,P_L)` by the canonically equivalent
field-unit cohomology `H⁰(G,Lˣ)`. -/
theorem ideleClassToFieldUnitsConnecting_range_eq_ker
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let :=
      LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    let :=
      RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
    MonoidHom.range
        (ideleClassToFieldUnitsConnecting K L) =
      MonoidHom.ker
        (fieldUnitsToRelativeIdeleHerbrandH0 K L) := by
  intro sharedOwner1 sharedOwner2
  let :=
    RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  let e :=
    fieldUnitsHerbrandH0EquivPrincipalIdeles K L
  ext q
  constructor
  · rintro ⟨c, rfl⟩
    change
      principalIdeleHerbrandH0Map K L
          (e (e.symm
            (ideleClassToPrincipalConnecting K L c))) = 1
    rw [e.apply_symm_apply]
    exact
      (ideleClassToPrincipalConnecting_range_eq_ker
        K L).le
        ⟨c, rfl⟩
  · intro hq
    change
      principalIdeleHerbrandH0Map K L (e q) = 1 at hq
    have heq :
        e q ∈
          MonoidHom.range
            (ideleClassToPrincipalConnecting K L) := by
      rw [ideleClassToPrincipalConnecting_range_eq_ker K L]
      exact hq
    obtain ⟨c, hc⟩ := heq
    refine ⟨c, ?_⟩
    change e.symm
        (ideleClassToPrincipalConnecting K L c) = q
    rw [hc, e.symm_apply_apply]

/-- Vanishing of `H⁻¹(G,C_L)` makes the diagonal map from field-unit
cohomology to idele cohomology injective. -/
theorem fieldUnitsToRelativeIdeleHerbrandH0_injective_of_subsingleton
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Subsingleton
      (letI :=
        RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
      Multiplicative
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1)))] :
    let :=
      LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    let :=
      RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
    Function.Injective
      (fieldUnitsToRelativeIdeleHerbrandH0 K L) := by
  intro sharedOwner1 sharedOwner2
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [← ideleClassToFieldUnitsConnecting_range_eq_ker K L]
  ext q
  constructor
  · rintro ⟨c, rfl⟩
    have hc : c = 1 := Subsingleton.elim c 1
    subst c
    exact Subgroup.mem_bot.mpr (map_one _)
  · intro hq
    have hqOne : q = 1 := Subgroup.mem_bot.mp hq
    subst q
    exact ⟨1, map_one _⟩

/-- Vanishing of `H⁻¹(G,C_L)` gives the reverse inclusion in the Hasse norm
principle through the concrete low-degree sequence. -/
theorem everywhereLocalFieldNormSubgroup_le_global_of_subsingleton
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Subsingleton
      (letI :=
        RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
      Multiplicative
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1)))] :
    everywhereLocalFieldNormSubgroup K L ≤
      localNormSubgroup K L := by
  let :=
    LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  intro x hx
  have hxNorm :
      IdeleGroup.principalIdele K x ∈
        (RelativeIdeleGroup.norm K L).range := by
    rw [
      relativeIdeleNorm_range_eq_allPlaceLocalNormCondition
        (K := K) (L := L)]
    exact hx
  let q : HerbrandH0 (L ≃ₐ[K] L) Lˣ :=
    HerbrandH0.mk (baseFieldUnitAsFixedUnit K L x)
  have hqMap :
      fieldUnitsToRelativeIdeleHerbrandH0 K L q = 1 :=
    fieldUnitsHerbrandH0_map_baseFieldUnit_eq_one_of_mem_norm
      K L x hxNorm
  have hq : q = 1 := by
    apply
      fieldUnitsToRelativeIdeleHerbrandH0_injective_of_subsingleton
        K L
    simpa using hqMap
  have hxTate :
      (baseFieldUnitAsFixedUnit K L x : Lˣ) ∈
        tateNormSubgroup (L ≃ₐ[K] L) Lˣ :=
    (HerbrandH0.mk_eq_one_iff
      (baseFieldUnitAsFixedUnit K L x)).1 hq
  obtain ⟨y, hy⟩ := hxTate
  refine ⟨y, ?_⟩
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective K L
  change
    algebraMap K L
        ((Units.map (Algebra.norm K : L →* K) y : Kˣ) : K) =
      algebraMap K L (x : K)
  have hUnits :
      Units.map (algebraMap K L).toMonoidHom
          (Units.map (Algebra.norm K : L →* K) y) =
        Units.map (algebraMap K L).toMonoidHom x := by
    calc
      Units.map (algebraMap K L).toMonoidHom
          (Units.map (Algebra.norm K : L →* K) y) =
          ∏ τ : L ≃ₐ[K] L,
            Units.map τ.toRingEquiv.toMonoidHom y :=
        RelativeIdeleGroup.fieldNormUnits_eq_prod_conjugates K L y
      _ = tateNorm (L ≃ₐ[K] L) Lˣ y := rfl
      _ = (baseFieldUnitAsFixedUnit K L x : Lˣ) := hy
      _ = Units.map (algebraMap K L).toMonoidHom x := rfl
  exact congrArg Units.val hUnits

/-- The concrete diagonal local-norm map.  Its source is the global norm
quotient, while its target kills precisely those ideles satisfying every
local norm condition. -/
noncomputable def hasseNormDiagonal
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Kˣ ⧸ localNormSubgroup K L →*
      IdeleGroup K ⧸ allPlaceLocalNormCondition (K := K) (L := L) :=
  QuotientGroup.map
    (localNormSubgroup K L)
    (allPlaceLocalNormCondition (K := K) (L := L))
    (IdeleGroup.principalIdele K)
    globalFieldNormSubgroup_le_everywhereLocalFieldNormSubgroup

/-- The Hasse norm diagonal sends the class of a field unit to the class
of its principal idele. -/
@[simp]
theorem hasseNormDiagonal_mk
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (x : Kˣ) :
    hasseNormDiagonal K L
        (QuotientGroup.mk' (localNormSubgroup K L) x) =
      QuotientGroup.mk'
        (allPlaceLocalNormCondition (K := K) (L := L))
        (IdeleGroup.principalIdele K x) :=
  rfl

/-- Injectivity of the concrete diagonal is exactly the missing
local-to-global inclusion. -/
theorem hasseNormDiagonal_injective_iff
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Function.Injective (hasseNormDiagonal K L) ↔
      everywhereLocalFieldNormSubgroup K L ≤
        localNormSubgroup K L := by
  constructor
  · intro hinj x hx
    have hdiag :
        hasseNormDiagonal K L
            (QuotientGroup.mk'
              (localNormSubgroup K L) x) =
          hasseNormDiagonal K L 1 := by
      rw [map_one, hasseNormDiagonal_mk]
      exact
        (QuotientGroup.eq_one_iff
          (IdeleGroup.principalIdele K x)).2 hx
    have hq :
        QuotientGroup.mk' (localNormSubgroup K L) x = 1 :=
      hinj hdiag
    exact (QuotientGroup.eq_one_iff x).1 hq
  · intro hlocal
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro q hq
      refine QuotientGroup.induction_on q ?_ hq
      intro x hx
      have hxlocal :
          x ∈ everywhereLocalFieldNormSubgroup K L := by
        exact
          (QuotientGroup.eq_one_iff
            (IdeleGroup.principalIdele K x)).1 hx
      change
        QuotientGroup.mk'
            (localNormSubgroup K L) x = 1
      exact (QuotientGroup.eq_one_iff x).2 (hlocal hxlocal)
    · exact bot_le

/-- Equivalent subgroup formulation of the Hasse norm principle. -/
theorem hasseNormDiagonal_injective_iff_subgroup_eq
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Function.Injective (hasseNormDiagonal K L) ↔
      localNormSubgroup K L =
        everywhereLocalFieldNormSubgroup K L := by
  rw [hasseNormDiagonal_injective_iff]
  exact
    ⟨fun h => le_antisymm
        globalFieldNormSubgroup_le_everywhereLocalFieldNormSubgroup h,
      fun h => h ▸ le_rfl⟩

/-- Degree-minus-one Tate-cohomology vanishing makes the concrete diagonal
local-norm map injective. -/
theorem hasseNormDiagonal_injective_of_subsingleton
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Subsingleton
      (letI :=
        RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
      Multiplicative
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1)))] :
    Function.Injective (hasseNormDiagonal K L) :=
  hasseNormDiagonal_injective_iff.mpr
    (everywhereLocalFieldNormSubgroup_le_global_of_subsingleton
      K L)

/-- Hasse's norm theorem as equality of the actual global norm subgroup
and the subgroup of elements that are norms at every place. -/
theorem hasseNormPrinciple_of_subsingleton
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Subsingleton
      (letI :=
        RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
      Multiplicative
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1)))] :
    localNormSubgroup K L =
      everywhereLocalFieldNormSubgroup K L :=
  (hasseNormDiagonal_injective_iff_subgroup_eq.mp
    (hasseNormDiagonal_injective_of_subsingleton K L))

/-- For a finite cyclic extension, the concrete diagonal from the global
field-norm quotient to the simultaneous local norm quotient is injective.
The cyclic idele-class calculation supplies the required degree-minus-one
Tate-cohomology vanishing. -/
theorem hasseNormDiagonal_injective_cyclic_native
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    Function.Injective (hasseNormDiagonal K L) := by
  obtain ⟨sigma, hsigma⟩ :=
    IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  let :
      Subsingleton
        (Multiplicative
          (tateCohomology
            (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
              (RelativeIdeleGroup.ClassGroup K L)) (-1))) :=
    ideleClass_tateHMinusOne_subsingleton_cyclic
      K L sigma hsigma
  exact hasseNormDiagonal_injective_of_subsingleton K L

/-- Hasse's norm theorem for a finite cyclic extension: an element of
`Kˣ` is a global norm from `L` exactly when it is a norm at every place. -/
theorem hasseNormPrinciple_cyclic_native
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    localNormSubgroup K L =
      everywhereLocalFieldNormSubgroup K L :=
  hasseNormDiagonal_injective_iff_subgroup_eq.mp
    (hasseNormDiagonal_injective_cyclic_native K L)

/-- The native Tate proof applies to the actual extension in independent
universes: compatible small models transport every completion tensor norm
and the original global norm witness. -/
theorem hasseNormPrinciple_cyclic
    (K : Type u) (L : Type v)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    localNormSubgroup K L = everywhereLocalFieldNormSubgroup K L := by
  let : Small.{0} K := ClassFieldTheory.numberField_small K
  let : Small.{0} L := ClassFieldTheory.numberField_small L
  let : NumberField (Shrink.{0} K) := ClassFieldTheory.numberField_shrink K
  let : NumberField (Shrink.{0} L) := ClassFieldTheory.numberField_shrink L
  let : Algebra (Shrink.{0} K) (Shrink.{0} L) := HasseArf.shrinkAlgebra K L
  let : FiniteDimensional (Shrink.{0} K) (Shrink.{0} L) :=
    HasseArf.shrink_finiteDimensional K L
  let : IsGalois (Shrink.{0} K) (Shrink.{0} L) :=
    IsGalois.of_equiv_equiv (f := (Shrink.ringEquiv K).symm)
      (g := (Shrink.ringEquiv L).symm) (HasseArf.shrinkAlgebra_commutes K L)
  let : IsCyclic (Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L) :=
    (HasseArf.shrinkGalMulEquiv K L).isCyclic.mpr inferInstance
  let eK : K ≃ₐ[ℚ] Shrink.{0} K := (Shrink.ringEquiv K).symm.toRatAlgEquiv
  let eL : L ≃+* Shrink.{0} L := (Shrink.ringEquiv L).symm
  have hcomm (a : K) : eL (algebraMap K L a) =
      algebraMap (Shrink.{0} K) (Shrink.{0} L) (eK a) :=
    (DFunLike.congr_fun (HasseArf.shrinkAlgebra_commutes K L) a).symm
  ext x
  rw [← isFieldNorm_iff_mem_globalFieldNormSubgroup,
    ← isEverywhereLocalNorm_iff_mem_everywhereLocalFieldNormSubgroup]
  rw [ClassFieldTheory.isFieldNorm_congr eK.toRingEquiv eL hcomm x,
    ClassFieldTheory.isEverywhereLocalNorm_congr eK eL hcomm x]
  rw [isFieldNorm_iff_mem_globalFieldNormSubgroup,
    isEverywhereLocalNorm_iff_mem_everywhereLocalFieldNormSubgroup,
    hasseNormPrinciple_cyclic_native (Shrink.{0} K) (Shrink.{0} L)]

/-- The original principal-idele diagonal is injective in independent universes. -/
theorem hasseNormDiagonal_injective_cyclic
    (K : Type u) (L : Type v)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    Function.Injective (hasseNormDiagonal K L) :=
  hasseNormDiagonal_injective_iff_subgroup_eq.mpr (hasseNormPrinciple_cyclic K L)

end GlobalClassFieldTheory.ClassFieldAxiom
