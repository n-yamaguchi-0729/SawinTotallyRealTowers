/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
The cited pi1 file has no copyright notice; its holder requires review.

Based on pi1 source (comparison revision; exact copied commit unverified):
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/Geometric.lean
-/

module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# Irreducibility after separable field extension

Finite separable intermediate fields control tensor-product elements and minimal primes.
The resulting irreducibility statements compare separable and algebraic closures.
-/

@[expose] public section

universe u v w

variable {k : Type u} {R : Type*} [Field k] [CommRing R] [Algebra k R]

open TensorProduct

lemma Ideal.under_mono {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {I J : Ideal S} (hIJ : I ≤ J) : I.under R ≤ J.under R :=
  Ideal.comap_mono hIJ

lemma Ideal.under_mem_minimalPrimes (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.HasGoingDown R S] (p : Ideal S) (hp : p ∈ minimalPrimes S) :
    p.under R ∈ minimalPrimes R := by
  rw [minimalPrimes_eq_minimals, Set.mem_ofPred_eq]
  have : p.IsPrime := hp.1.1
  refine ⟨inferInstance, fun q hq hle ↦ ?_⟩
  obtain ⟨Q, hQle, hQ, ho⟩ := Ideal.exists_ideal_le_liesOver_of_le p hle
  obtain rfl : p = Q := le_antisymm (hp.2 ⟨hQ, bot_le⟩ hQle) hQle
  rw [ho.1]

lemma Algebra.TensorProduct.exists_intermediateField_isSeparable_and_mem_range
    (Ω : Type*) [Field Ω] [Algebra k Ω] [Algebra.IsSeparable k Ω] (x : Ω ⊗[k] R) :
    ∃ (K : IntermediateField k Ω), Algebra.IsSeparable k K ∧ Module.Finite k K ∧
        x ∈ Set.range
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K Ω) (AlgHom.id k R)) := by
  induction x with
  | add x y hx hy =>
    obtain ⟨K, hK₁, hK₂, ⟨x, rfl⟩⟩ := hx
    obtain ⟨L, hL₁, hL₂, ⟨y, rfl⟩⟩ := hy
    let instK : Algebra ↥K ↥(K ⊔ L) :=
      (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
    let _ : Module ↥K ↥(K ⊔ L) := instK.toModule
    let instL : Algebra ↥L ↥(K ⊔ L) :=
      (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
    let _ : Module ↥L ↥(K ⊔ L) := instL.toModule
    let gK : K ⊗[k] R →ₐ[k] ↥(K ⊔ L) ⊗[k] R :=
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K _) (AlgHom.id k R)
    let gL : L ⊗[k] R →ₐ[k] ↥(K ⊔ L) ⊗[k] R :=
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom k L _) (AlgHom.id k R)
    let f (K : IntermediateField k Ω) : K ⊗[k] R →ₐ[k] Ω ⊗[k] R :=
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom _ _ _) (AlgHom.id k R)
    have hK : (f (K ⊔ L)).comp gK = f K := by ext <;> rfl
    have hL : (f (K ⊔ L)).comp gL = f L := by ext <;> rfl
    refine ⟨K ⊔ L, inferInstance, inferInstance, gK x + gL y, ?_⟩
    trans (f (K ⊔ L)) (gK x) + (f (K ⊔ L)) (gL y)
    · exact (f (K ⊔ L)).map_add (gK x) (gL y)
    · exact congr($(DFunLike.congr_fun hK x) + $(DFunLike.congr_fun hL y))
  | tmul x y =>
    refine ⟨IntermediateField.adjoin k {x}, ?_, ?_,
        ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ ⊗ₜ y, rfl⟩
    · rw [IntermediateField.isSeparable_adjoin_simple_iff_isSeparable]
      exact Algebra.IsSeparable.isSeparable k x
    · apply IntermediateField.adjoin.finiteDimensional
      exact Algebra.IsIntegral.isIntegral x

lemma Algebra.TensorProduct.exists_field_isSeparable_and_mem_range (Ω : Type v) [Field Ω]
    [Algebra k Ω] [Algebra.IsSeparable k Ω] (x : Ω ⊗[k] R) :
    ∃ (K : Type v) (_ : Field K) (_ : Algebra k K) (_ : Algebra K Ω) (_ : IsScalarTower k K Ω),
      Algebra.IsSeparable k K ∧ Module.Finite k K ∧
        x ∈ Set.range
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K Ω) (AlgHom.id k R)) := by
  obtain ⟨K, _, _, hK⟩ :=
    Algebra.TensorProduct.exists_intermediateField_isSeparable_and_mem_range _ x
  use K, inferInstance, inferInstance, inferInstance, inferInstance

/-- If `K ⊗[k] R` has up to one minimal prime for every finite, separable extension `K` of `k`,
the same holds for `Ω ⊗[k] R` for every separable extension `Ω` of `k`. -/
lemma subsingleton_minimalPrimes_of_isSeparable
    (H : ∀ (K : Type v) [Field K] [Algebra k K] [Module.Finite k K] [Algebra.IsSeparable k K],
      (minimalPrimes (K ⊗[k] R)).Subsingleton) (Ω : Type v) [Field Ω] [Algebra k Ω]
      [Algebra.IsSeparable k Ω] :
    (minimalPrimes (Ω ⊗[k] R)).Subsingleton := by
  refine fun p hp q hq ↦ ?_
  ext x
  obtain ⟨K, _, _, _, _, _, _, ⟨x, hx, rfl⟩⟩ :=
    Algebra.TensorProduct.exists_field_isSeparable_and_mem_range _ x
  let f : K ⊗[k] R →ₐ[k] Ω ⊗[k] R :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom _ _ _) (AlgHom.id k R)
  let _ : Algebra (K ⊗[k] R) (Ω ⊗[k] R) := f.toRingHom.toAlgebra
  have : f.toRingHom.Flat := by
    refine .tensorProductMap ?_ (.of_bijective <| Function.Involutive.bijective (congrFun rfl))
    simp only [AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom, RingHom.flat_algebraMap_iff]
    infer_instance
  have : Module.Flat (K ⊗[k] R) (Ω ⊗[k] R) := this
  have : p.under (K ⊗[k] R) = q.under (K ⊗[k] R) :=
    (H K) (p.under_mem_minimalPrimes (K ⊗[k] R) hp) (q.under_mem_minimalPrimes (K ⊗[k] R) hq)
  exact SetLike.ext_iff.mp this x

instance (priority := 100) PreirreducibleSpace.of_isEmpty (X : Type*) [TopologicalSpace X]
    [IsEmpty X] : PreirreducibleSpace X := by
  constructor
  convert isPreirreducible_empty
  exact Set.eq_empty_of_isEmpty Set.univ

lemma irreducibleSpace_iff_subsingleton_and_nonempty {X : Type*} [TopologicalSpace X] :
    IrreducibleSpace X ↔
      (irreducibleComponents X).Subsingleton ∧ (irreducibleComponents X).Nonempty := by
  refine ⟨fun hX ↦ irreducibleComponents_eq_singleton (X := X) ▸ by simp, fun ⟨hS, hN⟩ ↦ ?_⟩
  · obtain ⟨s, hs⟩ := hN
    have : s = Set.univ := by
      rw [← Set.univ_subset_iff]
      rintro x -
      convert mem_irreducibleComponent
      exact hS hs (irreducibleComponent_mem_irreducibleComponents x)
    have : PreirreducibleSpace X := ⟨this ▸ hs.1.2⟩
    exact ⟨⟨hs.1.1.some⟩⟩

lemma preirreducibleSpace_iff_subsingleton_irreducibleComponents {X : Type*} [TopologicalSpace X] :
    PreirreducibleSpace X ↔ (irreducibleComponents X).Subsingleton := by
  obtain (h|hN) := isEmpty_or_nonempty X
  · simp only [PreirreducibleSpace.of_isEmpty, true_iff]
    intro s _ t _
    rw [s.eq_empty_of_isEmpty, t.eq_empty_of_isEmpty]
  · exact ⟨fun h ↦ (irreducibleSpace_iff_subsingleton_and_nonempty.mp <| .mk ‹_›).1, fun h ↦
      (irreducibleSpace_iff_subsingleton_and_nonempty.mpr
        ⟨h, irreducibleComponent hN.some, irreducibleComponent_mem_irreducibleComponents _⟩).1⟩

lemma PrimeSpectrum.preirreducibleSpace_iff {R : Type*} [CommSemiring R] :
    PreirreducibleSpace (PrimeSpectrum R) ↔ (minimalPrimes R).Subsingleton := by
  rw [preirreducibleSpace_iff_subsingleton_irreducibleComponents]
  simpa [Set.subsingleton_coe, OrderDual] using
    (minimalPrimes.equivIrreducibleComponents R).symm.subsingleton_congr

lemma PrimeSpectrum.irreducibleSpace_iff {R : Type*} [CommSemiring R] :
    IrreducibleSpace (PrimeSpectrum R) ↔
      (minimalPrimes R).Subsingleton ∧ (minimalPrimes R).Nonempty := by
  rw [irreducibleSpace_iff_subsingleton_and_nonempty]
  have h1 := (minimalPrimes.equivIrreducibleComponents R).symm.subsingleton_congr
  simp only [OrderDual, Set.subsingleton_coe] at h1
  have h2 := (minimalPrimes.equivIrreducibleComponents R).symm.nonempty_congr
  simp only [Set.nonempty_coe_sort, OrderDual] at h2
  rw [h1, h2]

lemma Ideal.IsPrime.nontrivial {R : Type*} [Semiring R]
    {I : Ideal R} (hI : I.IsPrime) : Nontrivial R :=
  nontrivial_of_ne 1 0 (fun h ↦ hI.1 <| (eq_top_iff_one I).mpr (h ▸ I.zero_mem))

lemma RingHom.isIntegral_algebraMap_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).IsIntegral ↔ Algebra.IsIntegral R S := by
  simp_rw [Algebra.isIntegral_def, RingHom.IsIntegral, _root_.IsIntegral]

lemma Algebra.TensorProduct.isIntegral_includeRight (R S T : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [CommRing T] [Algebra R T] [Algebra.IsIntegral R T] :
    (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S).IsIntegral :=
  have : (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S) =
      (Algebra.TensorProduct.comm ..).toAlgHom.comp (IsScalarTower.toAlgHom R S _) := rfl
  this ▸ RingHom.IsIntegral.trans _ _
    (RingHom.isIntegral_algebraMap_iff.mpr <| Algebra.IsIntegral.tensorProduct R S T)
    (RingHom.isIntegral_of_surjective _ (AlgEquiv.surjective _))

/-- If `Spec (K ⊗[k] R)` is irreducible for every finite, separable extension `K` of `k`,
the same holds for `Spec (Ω ⊗[k] R)` for every separable extension `Ω` of `k`. -/
lemma PrimeSpectrum.irreducibleSpace_of_isSeparable
    (H : ∀ (K : Type u) [Field K] [Algebra k K] [Module.Finite k K] [Algebra.IsSeparable k K],
      IrreducibleSpace (PrimeSpectrum (K ⊗[k] R))) (Ω : Type u) [Field Ω] [Algebra k Ω]
      [Algebra.IsSeparable k Ω] :
    IrreducibleSpace (PrimeSpectrum (Ω ⊗[k] R)) :=
  have : Nontrivial R := by
    convert (Algebra.TensorProduct.lid k R).symm.toRingHom.domain_nontrivial
    rw [← PrimeSpectrum.nonempty_iff_nontrivial]
    exact (H k).2
  have : PreirreducibleSpace (PrimeSpectrum (Ω ⊗[k] R)) := by
    rw [PrimeSpectrum.preirreducibleSpace_iff]
    simp_rw [PrimeSpectrum.irreducibleSpace_iff] at H
    apply subsingleton_minimalPrimes_of_isSeparable
    intro K _ _ _ _
    exact (H K).1
  ⟨((Algebra.TensorProduct.isIntegral_includeRight k R Ω).comap_surjective <|
    Algebra.TensorProduct.includeRight_injective (algebraMap k Ω).injective).nonempty⟩

lemma PrimeSpectrum.comap_quotientMk_surjective_of_le_nilradical {R : Type*} [CommRing R]
    (I : Ideal R) (hle : I ≤ nilradical R) :
    Function.Surjective (PrimeSpectrum.comap <| Ideal.Quotient.mk I) := by
  rwa [← Set.range_eq_univ, range_comap_of_surjective, zeroLocus_eq_univ_iff,
    Ideal.mk_ker, SetLike.coe_subset_coe]
  exact Ideal.Quotient.mk_surjective

open Algebra

instance Subsingleton.charP (R : Type*) [AddMonoidWithOne R] [Subsingleton R] : CharP R 1 :=
  ⟨fun x ↦ by simpa using eq_zero (x : R)⟩

/-- If `R` has an exponential characteristic, it is nontrivial. -/
lemma nontrivial_of_expChar (R : Type*) [AddMonoidWithOne R] (q : ℕ) [hq : ExpChar R q] :
    Nontrivial R := by
  cases hq with
  | zero => infer_instance
  | prime hq =>
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hq.ne_one (CharP.eq R ‹_› h.charP)

lemma IsHomeomorph.irreducibleSpace {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) (hf : IsHomeomorph f)
    [IrreducibleSpace X] : IrreducibleSpace Y := by
  have := hf.surjective.preirreducibleSpace hf.continuous
  exact ⟨(hf.homeomorph).symm.surjective.nonempty⟩

lemma IsPurelyInseparable.of_surjective {F E : Type*} [CommRing F] [CommRing E] [Algebra F E]
    (h : Function.Surjective (algebraMap F E)) :
    IsPurelyInseparable F E where
  isIntegral := Algebra.isIntegral_of_surjective h
  inseparable' _ _ := h _

lemma PrimeSpectrum.irreducibleSpace_of_isAlgClosure_of_irreducibleSpace_of_isSepClosure
    (k R : Type*) [CommRing R] [Field k] [Algebra k R]
    (K : Type*) [Field K] [Algebra k K] [IsSepClosure k K]
    (L : Type*) [Field L] [Algebra k L] [IsAlgClosure k L] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[k] R)) ↔ IrreducibleSpace (PrimeSpectrum (L ⊗[k] R)) := by
  let eK := IsSepClosure.equiv k (SeparableClosure k) K
  let _ : Algebra K (SeparableClosure k) := eK.symm.toAlgHom.toAlgebra
  let eL := IsAlgClosure.equiv k (AlgebraicClosure k) L
  have : IsPurelyInseparable K (SeparableClosure k) := .of_surjective eK.symm.surjective
  let _ : Algebra (AlgebraicClosure k) L := eL.toAlgHom.toAlgebra
  have : IsPurelyInseparable (SeparableClosure k) (AlgebraicClosure k) := inferInstance
  have : IsPurelyInseparable (AlgebraicClosure k) L := .of_surjective eL.surjective
  let _ : Algebra K L :=
    (eL.toAlgHom.comp <| (IsScalarTower.toAlgHom k _ _).comp eK.symm.toAlgHom).toAlgebra
  have : IsScalarTower K (SeparableClosure k) L := .of_algebraMap_eq' rfl
  have : IsPurelyInseparable (SeparableClosure k) L :=
    IsPurelyInseparable.trans (SeparableClosure k) (AlgebraicClosure k) L
  have : IsPurelyInseparable K L :=
    IsPurelyInseparable.trans K (SeparableClosure k) L
  have e := isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable K k R L
  refine ⟨fun h ↦ (e.homeomorph).symm.isHomeomorph.irreducibleSpace, fun h ↦ e.irreducibleSpace⟩
