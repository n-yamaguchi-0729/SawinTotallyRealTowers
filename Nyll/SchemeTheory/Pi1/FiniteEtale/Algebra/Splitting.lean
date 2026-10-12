/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
The cited pi1 file has no copyright notice; its holder requires review.

Adapted from the pinned pi1 source:
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/KerTensor.lean
-/

/-
Nyll-maintained port: imports and proofs have been adapted for the Nyll toolchain.
Upstream notices are preserved; local changes are documented in
Nyll/EtaleFundamentalGroups/Pi1/ATTRIBUTION.md and UPSTREAM.json.
-/

module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.RingHom.Bijective
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.TotallySplit
public import Nyll.SchemeTheory.Pi1.Morphisms.Flat
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Algebra.Equalizer
public import Nyll.SchemeTheory.Pi1.Descent.FlatEqualizer
public import Nyll.SchemeTheory.FiniteEtale.Algebra.EtaleSplitting

/-!
# Split presentations and tensor equalizers

Finite étale algebras admit split presentations on étale neighborhoods. These
presentations and faithfully flat descent compare tensor products with algebra
equalizers.
-/

@[expose] public section

attribute [local instance] Module.FinitePresentation.of_finite_of_finitePresentation

open TensorProduct

universe u

@[simp]
lemma AlgHom.equalizerCompRightEquiv_symm_apply (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] {E F : Type*} (σ τ : E → F) (x : Function.Coequalizer σ τ → S) (i : F) :
    ((equalizerCompRightEquiv R S σ τ).symm x).val i = x (.mk _ _ i) :=
  rfl

@[simp]
lemma AlgHom.equalizerCompRightEquiv_apply (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] {E F : Type*} (σ τ : E → F) (x : equalizer (compRight R S σ) (compRight R S τ))
    (i : F) :
    (AlgHom.equalizerCompRightEquiv R S σ τ) x (Function.Coequalizer.mk σ τ i) =
      x.val i :=
  rfl

namespace RingHom

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

variable {P} in
lemma OfLocalizationSpan.pi (hP : OfLocalizationSpan P)
    (hPi : RespectsIso P)
    {ι : Type u} [_root_.Finite ι]
    (R : ι → Type u) (S : ι → Type u) [∀ i, CommRing (R i)]
    [∀ i, CommRing (S i)] (f : ∀ i, R i →+* S i)
    (hf : ∀ i, P (f i)) :
    P (RingHom.pi <| fun i ↦ (f i).comp <| Pi.evalRingHom R i) := by
  classical
  have := Ideal.span_single_eq_top R
  apply hP.ofIsLocalization hPi _ _ this
  rintro ⟨r, i, rfl⟩
  let i₁ : Algebra (∀ i, R i) (R i) := (Pi.evalRingHom R i).toAlgebra
  let i₂ : Algebra (∀ i, S i) (S i) := (Pi.evalRingHom S i).toAlgebra
  refine ⟨R i, S i, inferInstance, inferInstance, i₁, i₂, ?_, ?_, f i, ?_, hf i⟩
  · refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom _ _)
      ((Pi.evalRingHom R i).surjective)
    simp [IsIdempotentElem, ← Pi.single_mul_left]
  · have : (RingHom.pi fun i ↦ (f i).comp <| Pi.evalRingHom R i)
        (Pi.single i 1) = Pi.single i 1 := by
      ext j
      simp only [Pi.single, RingHom.pi_apply, coe_comp, Function.comp_apply, Pi.evalRingHom_apply,
        Function.update, Pi.zero_apply]
      by_cases h : j = i
      · subst h
        simp
      · simp [h]
    change IsLocalization.Away
      ((RingHom.pi fun i ↦ (f i).comp <| Pi.evalRingHom R i) (Pi.single i 1)) (S i)
    rw [this]
    refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom _ _)
      ((Pi.evalRingHom S i).surjective)
    simp [IsIdempotentElem, ← Pi.single_mul_left]
  · ext j x
    simp [RingHom.algebraMap_toAlgebra]

lemma _root_.Pi.algebraMap_instAlgebraForall_apply {ι : Type*} (A : ι → Type*)
    [∀ i, Semiring (A i)] (S : ι → Type*) [∀ i, CommSemiring (S i)]
    [∀ i, Algebra (S i) (A i)] (x : ∀ i, S i) :
    algebraMap (∀ i, S i) (∀ i, A i) x = fun i ↦ algebraMap (S i) (A i) (x i) :=
  rfl

instance (R M N : Type*) [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Flat R M] [Module.Flat R N] :
    Module.Flat R (M × N) := by
  refine ⟨fun P _ _ _ Q _ ↦ ?_⟩
  have heq :
      LinearMap.rTensor (M × N) Q.subtype =
        (TensorProduct.prodRight _ _ _ _ _).symm.toLinearMap ∘ₗ
          LinearMap.prodMap (Q.subtype.rTensor M) (Q.subtype.rTensor N) ∘ₗ
          (TensorProduct.prodRight _ _ _ _ _).toLinearMap := by
    ext <;>
    · apply (TensorProduct.prodRight R R P M N).injective
      simp
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp, heq]
  apply Function.Injective.prodMap <;>
    exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

instance {ι : Type*} (R : Type*) [CommRing R] [_root_.Finite ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Flat R (M i)] :
    Module.Flat R (∀ i, M i) := by
  refine Module.pi_induction' (ι := ι) R (motive := fun N _ _ ↦ Module.Flat R N)
    (motive' := fun N _ _ ↦ Module.Flat R N)
      ?_ ?_ ?_ ?_ M inferInstance
  · intro N N' _ _ _ _ e _
    exact Module.Flat.of_linearEquiv e.symm
  · intro N N' _ _ _ _ e _
    exact Module.Flat.of_linearEquiv e.symm
  · infer_instance
  · intros
    infer_instance

lemma CodescendsAlong.of_forall_flat {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hPi : RespectsIso P) (hPl : OfLocalizationSpan P) (hP : CodescendsAlong P FaithfullyFlat)
    {ι : Type u} (T : ι → Type u) [∀ i, CommRing (T i)]
    [∀ i, Algebra R (T i)] [∀ i, Module.Flat R (T i)]
    (ho : ∀ i, IsOpen <| Set.range <| PrimeSpectrum.comap (algebraMap R (T i)))
    (hunion : ⋃ i, Set.range (PrimeSpectrum.comap (algebraMap R (T i))) = Set.univ)
    (H : ∀ i, P (algebraMap (T i) (T i ⊗[R] S))) :
    P (algebraMap R S) := by
  classical
  let U (i : ι) : Set (PrimeSpectrum R) :=
    Set.range <| PrimeSpectrum.comap (algebraMap R (T i))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U (fun p ↦ ho _) (hunion ▸ le_rfl)
  let A : Type u := ∀ (p : t), T p.1
  have : Module.FaithfullyFlat R A := by
    apply Module.FaithfullyFlat.of_comap_surjective
    intro p
    obtain ⟨i, hi, q, rfl⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
    use (PrimeSpectrum.comap <| Pi.evalRingHom (fun p : t ↦ T p.1) ⟨i, hi⟩) q
    rfl
  apply hP.algebraMap_tensorProduct (R := R) (S := A) (T := S)
  · rwa [faithfullyFlat_algebraMap_iff]
  · let e : A ⊗[R] S ≃ₐ[R] ∀ i : t, T i.val ⊗[R] S :=
      (Algebra.TensorProduct.comm ..).trans <|
        (Algebra.TensorProduct.piRight R R S (fun i : t ↦ T i)).trans <|
          .piCongrRight fun i ↦ Algebra.TensorProduct.comm ..
    have : algebraMap A (A ⊗[R] S) = e.symm.toRingHom.comp
        (algebraMap A <| ∀ p : t, T p.1 ⊗[R] S) := by
      ext i x
      apply e.injective
      change e ((algebraMap A (A ⊗[R] S)) (Pi.single i x)) =
        e (e.symm ((algebraMap A (∀ p : t, T p.1 ⊗[R] S)) (Pi.single i x)))
      rw [e.apply_symm_apply]
      ext j
      rw [Pi.algebraMap_instAlgebraForall_apply]
      change
        (Algebra.TensorProduct.comm R S (T j.val))
          (((Algebra.TensorProduct.piRight R R S (fun k : t ↦ T k.val))
            ((Algebra.TensorProduct.comm R A S)
              ((algebraMap A (A ⊗[R] S)) (Pi.single i x)))) j) =
          (algebraMap (T j.val) (T j.val ⊗[R] S))
            ((Pi.single i x : ∀ k : t, T k.val) j)
      simp only [Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self_apply, Algebra.TensorProduct.comm_tmul]
      exact (congrArg
        (fun z : ∀ k : t, S ⊗[R] T k.val =>
          (Algebra.TensorProduct.comm R S (T j.val)) (z j))
        (Algebra.TensorProduct.piRight_tmul R R S
          (fun k : t => T k.val) (1 : S)
          (Pi.single i x : ∀ k : t, T k.val))).trans
        (Algebra.TensorProduct.comm_tmul R (1 : S)
          ((Pi.single i x : ∀ k : t, T k.val) j))
    rw [this]
    apply hPi.1
    exact hPl.pi hPi _ _ _ (fun i ↦ H i.1)

lemma CodescendsAlong.of_forall_exists_flat {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hPi : RespectsIso P) (hPl : OfLocalizationSpan P)
    (hP : CodescendsAlong P FaithfullyFlat)
    (H : ∀ (p : PrimeSpectrum R), ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R T)) ∧ Module.Flat R T ∧
      IsOpen (Set.range <| PrimeSpectrum.comap (algebraMap R T)) ∧
      P (algebraMap T (T ⊗[R] S))) :
    P (algebraMap R S) := by
  choose T h1 h2 hmem _ ho hT using H
  exact hP.of_forall_flat _ hPi hPl T ho (Set.iUnion_eq_univ_iff.mpr fun p ↦ ⟨p, hmem p⟩) hT

open AlgebraicGeometry CategoryTheory Limits in
lemma PrimeSpectrum.range_comap_tensorProduct (R S T : Type u) [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    Set.range (PrimeSpectrum.comap <| algebraMap S (S ⊗[R] T)) =
      (PrimeSpectrum.comap (algebraMap R S)) ⁻¹'
        (Set.range <| PrimeSpectrum.comap (algebraMap R T)) := by
  ext p
  refine ⟨?_, ?_⟩
  · rintro ⟨p, rfl⟩
    use PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom p
    have : (algebraMap S (S ⊗[R] T)).comp (algebraMap R S) =
        Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap R T) := by ext; simp
    exact congr(PrimeSpectrum.comap $(this) p).symm
  · rintro ⟨q, hp⟩
    obtain ⟨z, hz⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
      (X := Spec <| .of S) (Y := Spec <| .of T) (S := Spec <| .of R)
        (f := Spec.map <| CommRingCat.ofHom (algebraMap R S))
        (g := Spec.map <| CommRingCat.ofHom (algebraMap R T)) p q hp.symm
    let e : pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) ≅ Spec (.of <| S ⊗[R] T) :=
      pullbackSpecIso R S T
    use e.hom.base z
    rw [← hz.1, ← pullbackSpecIso_hom_fst]
    rfl

lemma CodescendsAlong.algHom_of_forall_exists_flat {R A B : Type u} [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (hPi : RespectsIso P) (hPl : OfLocalizationSpan P)
    (hP : CodescendsAlong P FaithfullyFlat)
    (f : A →ₐ[R] B)
    (H : ∀ (p : PrimeSpectrum R), ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R T)) ∧ Module.Flat R T ∧
      IsOpen (Set.range <| PrimeSpectrum.comap (algebraMap R T)) ∧
      P (Algebra.TensorProduct.map (.id T T) f).toRingHom) :
    P f.toRingHom := by
  algebraize [f.toRingHom]
  apply hP.of_forall_exists_flat _ hPi hPl
  intro p
  obtain ⟨T, _, _, ⟨q, hq⟩, hflat, ho, hp⟩ :=
    H (PrimeSpectrum.comap (algebraMap R A) p)
  have heq : Set.range (PrimeSpectrum.comap (algebraMap A (A ⊗[R] T))) =
      (PrimeSpectrum.comap (algebraMap R A)) ⁻¹'
        (Set.range <| PrimeSpectrum.comap (algebraMap R T)) :=
    PrimeSpectrum.range_comap_tensorProduct R A T
  let e : T ⊗[R] B ≃ₐ[R] (A ⊗[R] T) ⊗[A] B :=
    .trans ((Algebra.TensorProduct.comm _ _ _).restrictScalars R)
      (.trans
        ((Algebra.TensorProduct.cancelBaseChange R A A B T).symm.restrictScalars R)
        ((Algebra.TensorProduct.comm _ _ _).restrictScalars R))
  have hdiag' :
    IsScalarTower.toAlgHom R (A ⊗[R] T) ((A ⊗[R] T) ⊗[A] B) =
      (AlgHom.comp e.toAlgHom
        ((Algebra.TensorProduct.map (AlgHom.id T T) f).restrictScalars R)).comp
        (Algebra.TensorProduct.comm _ _ _).toAlgHom := by
    ext a
    · suffices h : (a ⊗ₜ[R] (1 : T)) ⊗ₜ[A] (1 : B) = (1 ⊗ₜ[R] 1) ⊗ₜ[A] f a by
        simp [e, h]
      rw [← mul_one a, ← smul_eq_mul, ← TensorProduct.smul_tmul', TensorProduct.smul_tmul,
        Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra, smul_eq_mul, mul_one,
        AlgHom.toRingHom_eq_coe, coe_coe]
    · simp [e]
  replace hdiag' := congr($(hdiag').toRingHom)
  simp only [AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom, AlgHom.comp_toRingHom] at hdiag'
  refine ⟨A ⊗[R] T, inferInstance, inferInstance, ?_, inferInstance, ?_, ?_⟩
  · rw [heq]
    use q
  · rw [heq]
    exact ho.preimage (PrimeSpectrum.continuous_comap _)
  · rw [hdiag']
    exact hPi.2 _ (Algebra.TensorProduct.comm R A T).toRingEquiv (hPi.1 _ _ hp)

end RingHom

section

variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R S] [Algebra R B]

/-- An algebra homomorphism is split if algebra equivalences with finite powers of `R`
identify it with precomposition by a map of finite indexing sets. -/
def AlgHom.IsSplit (f : A →ₐ[R] B) : Prop :=
  ∃ (n m : ℕ) (eA : A ≃ₐ[R] (Fin n → R)) (eB : B ≃ₐ[R] (Fin m → R))
    (σ : Fin m → Fin n),
    f = eB.symm.toAlgHom.comp ((AlgHom.compRight R R σ).comp eA)

lemma AlgHom.IsSplit.mk (f : A →ₐ[R] B) {E F : Type*} [_root_.Finite E] [_root_.Finite F]
    (eA : A ≃ₐ[R] (E → R)) (eB : B ≃ₐ[R] (F → R)) (σ : F → E)
    (h : eB.toAlgHom.comp f = (AlgHom.compRight R R σ).comp eA.toAlgHom) :
    f.IsSplit := by
  cases nonempty_fintype E
  cases nonempty_fintype F
  let eE := Fintype.equivFin E
  let eF := Fintype.equivFin F
  refine ⟨Fintype.card E, Fintype.card F, eA.trans ?_, eB.trans ?_, eE ∘ σ ∘ eF.symm, ?_⟩
  · exact AlgEquiv.piCongrLeft R (fun _ ↦ R) eE
  · exact AlgEquiv.piCongrLeft R (fun _ ↦ R) eF
  · ext x
    apply eB.injective
    have := DFunLike.congr_fun h x
    simp only [coe_comp, AlgEquiv.coe_toAlgHom, Function.comp_apply] at this
    ext i
    simp [this, AlgHom.compRight]

lemma AlgHom.compRight_apply' {E F : Type*} (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (σ : E → F) (x : F → S) :
    AlgHom.compRight R S σ x = fun i ↦ x (σ i) :=
  rfl

variable (S) in
lemma AlgHom.IsSplit.tensorProductMap {f : A →ₐ[R] B} (hf : f.IsSplit) :
    (Algebra.TensorProduct.map (.id S S) f).IsSplit := by
  obtain ⟨n, m, eA, eB, σ, hf⟩ := hf
  refine AlgHom.IsSplit.mk (E := Fin n) (F := Fin m) _
    ((Algebra.TensorProduct.congr .refl eA).trans (Algebra.TensorProduct.piScalarRight ..))
    ((Algebra.TensorProduct.congr .refl eB).trans (Algebra.TensorProduct.piScalarRight ..)) σ ?_
  ext a
  simp [hf]

variable (S) in
lemma AlgHom.IsSplit.iff_of_isScalarTower
    (T : Type u) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] (f : A →ₐ[R] B) :
    (Algebra.TensorProduct.map (.id T T) f).IsSplit ↔
      (Algebra.TensorProduct.map (.id T T)
        (Algebra.TensorProduct.map (.id S S) f)).IsSplit := by
  refine ⟨?_, ?_⟩
  · rintro ⟨n, m, eA, eB, σ, hf⟩
    refine AlgHom.IsSplit.mk (E := Fin n) (F := Fin m) _ ?_ ?_ σ ?_
    · exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans eA
    · exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans eB
    · ext a i
      have := DFunLike.congr_fun hf (1 ⊗ₜ a)
      simp only [Algebra.TensorProduct.map_tmul, coe_id, id_eq, coe_comp,
        Function.comp_apply] at this
      simp [this]
  · rintro ⟨n, m, eA, eB, σ, hf⟩
    refine AlgHom.IsSplit.mk (E := Fin n) (F := Fin m) _ ?_ ?_ σ ?_
    · exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm.trans eA
    · exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm.trans eB
    · ext a i
      have := DFunLike.congr_fun hf (1 ⊗ₜ (1 ⊗ₜ a))
      simp only [Algebra.TensorProduct.map_tmul, coe_id, id_eq, coe_comp,
        Function.comp_apply] at this
      simp [this]

namespace Algebra

lemma exists_isFiniteSplit [Module.Finite R A] [Algebra.Etale R A]
    (p : PrimeSpectrum R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Module.Flat R S ∧
      IsOpenMap (PrimeSpectrum.comap (algebraMap R S)) ∧
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) ∧
      Algebra.IsFiniteSplit S (S ⊗[R] A) := by
  obtain ⟨S, _, _, _, hp, hS⟩ := exists_etale_isFiniteSplit (A := A) p
  exact ⟨S, inferInstance, inferInstance, inferInstance,
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation, hp, hS⟩

lemma exists_isSplit [Module.Finite R A] [Algebra.Etale R A]
    [Module.Finite R B] [Algebra.Etale R B] (f : A →ₐ[R] B)
    (p : PrimeSpectrum R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Module.Flat R S ∧
      IsOpenMap (PrimeSpectrum.comap (algebraMap R S)) ∧
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) ∧
      (TensorProduct.map (AlgHom.id S S) f).IsSplit := by
  classical
  wlog hA : IsFiniteSplit R A
  · obtain ⟨S, _, _, _, ho₁, ⟨p, rfl⟩, hS⟩ := exists_isFiniteSplit p (A := A)
    obtain ⟨S', _, _, _, ho₂, ⟨q, rfl⟩, hS'⟩ := this (TensorProduct.map (.id S S) f) p hS
    let _ : Algebra R S' := Algebra.compHom S' (algebraMap R S)
    have : IsScalarTower R S S' := .of_algebraMap_eq' rfl
    refine ⟨S', inferInstance, inferInstance, Module.Flat.trans R S S', ?_, ⟨q, rfl⟩, ?_⟩
    · rw [IsScalarTower.algebraMap_eq R S S', PrimeSpectrum.comap_comp]
      exact ho₁.comp ho₂
    · rwa [AlgHom.IsSplit.iff_of_isScalarTower S]
  wlog hB : IsFiniteSplit R B
  · obtain ⟨S, _, _, _, ho₁, ⟨p, rfl⟩, hS⟩ := exists_isFiniteSplit p (A := B)
    obtain ⟨S', _, _, _, ho₂, ⟨q, rfl⟩, hS'⟩ := this
      (A := S ⊗[R] A) (B := S ⊗[R] B) (R := S)
      (TensorProduct.map (.id S S) f) p inferInstance hS
    let _ : Algebra R S' := Algebra.compHom S' (algebraMap R S)
    have : IsScalarTower R S S' := .of_algebraMap_eq' rfl
    refine ⟨S', inferInstance, inferInstance, Module.Flat.trans R S S', ?_, ⟨q, rfl⟩, ?_⟩
    · rw [IsScalarTower.algebraMap_eq R S S', PrimeSpectrum.comap_comp]
      exact ho₁.comp ho₂
    · rwa [AlgHom.IsSplit.iff_of_isScalarTower S]
  obtain ⟨n, ⟨eA⟩⟩ := hA
  obtain ⟨m, ⟨eB⟩⟩ := hB
  let f' : (Fin n → R) →ₐ[R] Fin m → R := eB.toAlgHom.comp (f.comp eA.symm.toAlgHom)
  obtain ⟨r, hr, σ, hσ⟩ := AlgHom.exists_cover_eq_compRight'' f' p.asIdeal
  refine ⟨Localization.Away r, inferInstance, inferInstance, inferInstance,
      ?_, ?_, ?_⟩
  · exact (PrimeSpectrum.localization_away_isOpenEmbedding _ r).isOpenMap
  · change p ∈ Set.range (PrimeSpectrum.comap <| algebraMap R (Localization.Away r))
    rwa [PrimeSpectrum.localization_away_comap_range _ r]
  · let e := TensorProduct.piScalarRight R (Localization.Away r) (Localization.Away r) (Fin m)
    apply AlgHom.IsSplit.mk (E := Fin n) (F := Fin m) _
      (TensorProduct.congr .refl eA |>.trans (TensorProduct.piScalarRight ..))
      (TensorProduct.congr .refl eB |>.trans (TensorProduct.piScalarRight ..)) σ
    ext a i : 3
    simpa [TensorProduct.piScalarRight_tmul, f', e] using
      congrFun (congr(e ($(hσ) (1 ⊗ₜ eA a)))) i

local notation f " ≟ₐ " g => AlgHom.equalizer f g
local notation S " ⊗ₘ " f => Algebra.TensorProduct.map (AlgHom.id S S) f

lemma tensorEqualizer_compRight_bijective {E F : Type*} [Finite E] [Finite F]
    (σ τ : E → F) :
    Function.Bijective ((AlgHom.compRight R R σ).tensorEqualizer S S (.compRight R R τ)) := by
  classical
  cases nonempty_fintype E
  cases nonempty_fintype F
  cases nonempty_fintype (Function.Coequalizer σ τ)
  set f : (F → R) →ₐ[R] E → R := AlgHom.compRight R R σ
  set g : (F → R) →ₐ[R] E → R := AlgHom.compRight R R τ
  let eL : S ⊗[R] (F → R) ≃ₐ[S] F → S :=
    Algebra.TensorProduct.piScalarRight R S S F
  let eR : S ⊗[R] (E → R) ≃ₐ[S] E → S :=
    Algebra.TensorProduct.piScalarRight R S S E
  let eq₂ : S ⊗[R] (Function.Coequalizer σ τ → R) ≃ₐ[S] Function.Coequalizer σ τ → S :=
    Algebra.TensorProduct.piScalarRight R S S (Function.Coequalizer σ τ)
  let e₁ := AlgHom.equalizerCompRightEquiv R R σ τ
  let e₂ := AlgHom.equalizerCompRightEquiv S S σ τ
  let _ : AddCommMonoid ↥(f ≟ₐ g) := AddCommGroup.toAddCommMonoid
  let eq₁ : S ⊗[R] (f ≟ₐ g) ≃ₐ[S] S ⊗[R] (Function.Coequalizer σ τ → R) :=
    TensorProduct.congr AlgEquiv.refl e₁
  let eq₃ : ↥(TensorProduct.map (AlgHom.id S S) f ≟ₐ TensorProduct.map (AlgHom.id S S) g) ≃ₐ[S]
      (AlgHom.compRight S S σ) ≟ₐ (AlgHom.compRight S S τ) :=
    AlgHom.equalizerCongr eL eR (by ext; simp [eL, eR, f]) (by ext; simp [eL, eR, g])
  have : AlgHom.tensorEqualizer S S f g =
      AlgHom.comp (.comp (.comp eq₃.symm.toAlgHom e₂.symm.toAlgHom)
        eq₂.toAlgHom) eq₁.toAlgHom := by
    ext x
    apply (TensorProduct.piScalarRight R S S F).injective
    simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      TensorProduct.includeRight_apply, AlgHom.coe_tensorEqualizer, TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, Subalgebra.coe_val, TensorProduct.piScalarRight_tmul, smul_def, mul_one,
      AlgEquiv.coe_toAlgHom, TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom,
      AlgHom.equalizerCongr_symm_apply, AlgEquiv.apply_symm_apply, eq₃, eL, e₂, eq₂, eq₁, e₁]
    ext i
    rw [AlgHom.equalizerCompRightEquiv_symm_apply, AlgHom.equalizerCompRightEquiv_apply]
  rw [this]
  dsimp
  exact eq₃.symm.bijective.comp (e₂.symm.bijective.comp <| eq₂.bijective.comp eq₁.bijective)

lemma TensorProduct.map_bijective_of_bijective {R S A B C D : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S]
    [Semiring A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C] [Algebra S C]
    [IsScalarTower R S C] [Semiring D] [Algebra R D] {f : A →ₐ[S] C} {g : B →ₐ[R] D}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (TensorProduct.map f g) :=
  TensorProduct.congr (.ofBijective f hf) (.ofBijective g hg) |>.bijective

lemma tensorEqualizer_comp_comp {R : Type*} (S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {A A' : Type*} {B B' : Type*} [CommRing A] [CommRing A']
    [CommRing B] [CommRing B'] [Algebra R A] [Algebra R A']
    [Algebra R B] [Algebra R B'] (f g : A' →ₐ[R] B')
    (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B') :
    AlgHom.tensorEqualizer S T
      (eB.symm.toAlgHom.comp (f.comp eA.toAlgHom))
      (eB.symm.toAlgHom.comp (g.comp eA.toAlgHom)) =
        AlgHom.comp
          (AlgHom.equalizerCongr
            (TensorProduct.congr .refl eA.symm)
            (TensorProduct.congr .refl eB.symm)
            (by ext <;> simp) (by ext <;> simp)).toAlgHom
          (AlgHom.comp (AlgHom.tensorEqualizer S T f g)
          (TensorProduct.congr .refl
            (AlgHom.equalizerCongr eA eB (by ext; simp) (by ext; simp))).toAlgHom) := by
  ext t
  · simp [AlgHom.tensorEqualizer_tmul_one', AlgHom.equalizerCongr_apply]
  · simp [AlgHom.tensorEqualizer_one_tmul, AlgHom.equalizerCongr_apply]

/-- The natural map `S ⊗[R] eq(f, g) →ₐ[S] eq(S ⊗ f, S ⊗ g)` is an isomorphism for
arbitrary `S` if `A` and `B` are finite étale over `R`. -/
nonrec theorem tensorEqualizer_bijective_of_finite_of_etale (f g : A →ₐ[R] B)
    [Module.Finite R A] [Algebra.Etale R A] [Module.Finite R B] [Algebra.Etale R B] :
    Function.Bijective (f.tensorEqualizer R S g) := by
  wlog hf : f.IsSplit
  · apply RingHom.FaithfullyFlat.codescendsAlong_bijective.algHom_of_forall_exists_flat
    · exact RingHom.Bijective.respectsIso
    · exact RingHom.Bijective.ofLocalizationSpan
    · intro p
      obtain ⟨T, _, _, _, ho, hmem, hf⟩ := exists_isSplit f p
      refine ⟨T, inferInstance, inferInstance, hmem, inferInstance, ho.isOpen_range, ?_⟩
      apply (TensorProduct.map_tensorEqualizer_bijective_iff_tensorEqualizer_map_bijective ..).mpr
      apply this
      exact hf
  obtain ⟨n, m, eA, eB, σ, rfl⟩ := hf
  let g' : (Fin n → R) →ₐ[R] (Fin m → R) :=
    eB.toAlgHom.comp (g.comp eA.symm.toAlgHom)
  have : g = eB.symm.toAlgHom.comp (g'.comp eA.toAlgHom) := by ext; simp [g']
  rw [this]
  have : Function.Bijective (AlgHom.tensorEqualizer R S (.compRight R R σ) g') := by
    let _ : AddCommMonoid ↥(AlgHom.compRight R R σ ≟ₐ g') := AddCommGroup.toAddCommMonoid
    let _ : CommRing (S ⊗[R] ↥(AlgHom.compRight R R σ ≟ₐ g')) := inferInstance
    apply RingHom.FaithfullyFlat.codescendsAlong_bijective.algHom_of_forall_exists_flat
      (B := TensorProduct.map (AlgHom.id R S) (.compRight R R σ) ≟ₐ TensorProduct.map (.id R S) g')
    · exact RingHom.Bijective.respectsIso
    · exact RingHom.Bijective.ofLocalizationSpan
    · intro p
      obtain ⟨r, hr, τ, h⟩ := AlgHom.exists_cover_eq_compRight'' g' p.asIdeal
      refine ⟨Localization.Away r, inferInstance, inferInstance, ?_, inferInstance, ?_, ?_⟩
      · change p ∈ Set.range (PrimeSpectrum.comap <| algebraMap R (Localization.Away r))
        rw [PrimeSpectrum.localization_away_comap_range _ r]
        exact hr
      · change IsOpen <| Set.range (PrimeSpectrum.comap <| algebraMap R (Localization.Away r))
        rw [PrimeSpectrum.localization_away_comap_range _ r]
        exact PrimeSpectrum.isOpen_basicOpen
      · apply (TensorProduct.map_tensorEqualizer_bijective_iff_tensorEqualizer_map_bijective ..).mpr
        rw [h]
        apply (TensorProduct.map_tensorEqualizer_bijective_iff_tensorEqualizer_map_bijective ..).mp
        apply TensorProduct.map_bijective_of_bijective
        · exact Function.bijective_id
        · apply tensorEqualizer_compRight_bijective
  erw [tensorEqualizer_comp_comp]
  dsimp
  apply Function.Bijective.comp
  · apply AlgEquiv.bijective
  · apply Function.Bijective.comp
    · exact this
    · apply AlgEquiv.bijective

end Algebra

end
