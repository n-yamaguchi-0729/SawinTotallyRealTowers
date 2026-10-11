/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Adic completion at a finite product of coprime ideals

The Chinese remainder theorem decomposes every finite quotient by a power of
a product of pairwise coprime ideals.  This file proves that these finite-level
decompositions are compatible with the transition maps, and hence split the
adic completion itself as the product of the individual completions.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uR uI

open Function

variable {R : Type uR} [CommRing R]
variable {ι : Type uI} [Fintype ι]

/-- The finite-level Chinese-remainder equivalence for powers of a product of
pairwise coprime ideals. -/
private noncomputable def quotientProdPowEquiv
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J)) (n : ℕ) :
    R ⧸ (∏ i, J i) ^ n ≃+* ∀ i, R ⧸ J i ^ n := by
  classical
  refine (Ideal.quotEquivOfEq ?_).trans
    (Ideal.quotientInfRingEquivPiQuotient (fun i => J i ^ n) ?_)
  · simpa [Finset.prod_pow] using
      (Ideal.prod_eq_iInf_of_pairwise_isCoprime
        (s := Finset.univ) (J := fun i => J i ^ n)
        (fun i _ j _ hij => (hJ hij).pow))
  · exact fun i j hij => (hJ hij).pow

@[simp]
private theorem quotientProdPowEquiv_mk
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J)) (n : ℕ) (x : R) :
    quotientProdPowEquiv J hJ n (Ideal.Quotient.mk _ x) =
      fun _ => Ideal.Quotient.mk _ x := by
  rfl

private theorem quotientProdPowEquiv_factorPow
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J))
    {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ (∏ i, J i) ^ n) (i : ι) :
    Ideal.Quotient.factorPow (J i) hmn (quotientProdPowEquiv J hJ n x i) =
      quotientProdPowEquiv J hJ m
        (Ideal.Quotient.factorPow (∏ i, J i) hmn x) i := by
  induction x using Quotient.inductionOn' with
  | _ x => rfl

private theorem quotientProdPowEquiv_symm_factorPow
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J))
    {m n : ℕ} (hmn : m ≤ n) (x : ∀ i, R ⧸ J i ^ n) :
    Ideal.Quotient.factorPow (∏ i, J i) hmn
        ((quotientProdPowEquiv J hJ n).symm x) =
      (quotientProdPowEquiv J hJ m).symm
        (fun i => Ideal.Quotient.factorPow (J i) hmn (x i)) := by
  apply (quotientProdPowEquiv J hJ m).injective
  funext i
  rw [RingEquiv.apply_symm_apply,
    ← quotientProdPowEquiv_factorPow J hJ hmn
      ((quotientProdPowEquiv J hJ n).symm x) i,
    RingEquiv.apply_symm_apply]

private theorem factorPow_evalₐ
    (K : Ideal R) {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion K R) :
    Ideal.Quotient.factorPow K hmn (AdicCompletion.evalₐ K n x) =
      AdicCompletion.evalₐ K m x := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ K n x)
  have hn : AdicCompletion.eval K R n x =
      Ideal.Quotient.mk (K ^ n • ⊤ : Ideal R) a := by
    rw [← AdicCompletion.factor_evalₐ_eq_eval K x (by simp), ← ha,
      Ideal.Quotient.factor_mk]
  have hm : AdicCompletion.eval K R m x =
      Ideal.Quotient.mk (K ^ m • ⊤ : Ideal R) a := by
    calc
      AdicCompletion.eval K R m x =
          AdicCompletion.transitionMap K R hmn
            (AdicCompletion.eval K R n x) :=
        (AdicCompletion.transitionMap_comp_eval_apply K R hmn x).symm
      _ = Ideal.Quotient.mk (K ^ m • ⊤ : Ideal R) a := by
        rw [hn]
        rfl
  calc
    Ideal.Quotient.factorPow K hmn (AdicCompletion.evalₐ K n x) =
        Ideal.Quotient.mk (K ^ m) a := by
      rw [← ha, Ideal.Quotient.factor_mk]
    _ = AdicCompletion.evalₐ K m x := by
      rw [← AdicCompletion.factor_eval_eq_evalₐ K x (by simp), hm]
      rfl

private noncomputable def quotientProjectionRingHom
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J)) (i : ι) (n : ℕ) :
    AdicCompletion (∏ j, J j) R →+* R ⧸ J i ^ n :=
  (Pi.evalRingHom (fun i => R ⧸ J i ^ n) i).comp
    ((quotientProdPowEquiv J hJ n).toRingHom.comp
      (AdicCompletion.evalₐ (∏ j, J j) n).toRingHom)

private theorem quotientProjectionRingHom_compatible
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J)) (i : ι) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow (J i) hmn).comp
          (quotientProjectionRingHom J hJ i n) =
        quotientProjectionRingHom J hJ i m := by
  intro m n hmn
  ext x
  change Ideal.Quotient.factorPow (J i) hmn
      (quotientProdPowEquiv J hJ n
        (AdicCompletion.evalₐ (∏ j, J j) n x) i) =
    quotientProdPowEquiv J hJ m
      (AdicCompletion.evalₐ (∏ j, J j) m x) i
  rw [quotientProdPowEquiv_factorPow J hJ hmn,
    factorPow_evalₐ (∏ j, J j) hmn]

/-- Projection from the completion at the product to one of the individual
adic completions. -/
private noncomputable def adicCompletionToComponent
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J)) (i : ι) :
    AdicCompletion (∏ j, J j) R →+* AdicCompletion (J i) R :=
  AdicCompletion.liftRingHom (J i)
    (quotientProjectionRingHom J hJ i)
    (quotientProjectionRingHom_compatible J hJ i)

@[simp]
private theorem evalₐ_adicCompletionToComponent
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J)) (i : ι)
    (n : ℕ) (x : AdicCompletion (∏ j, J j) R) :
    AdicCompletion.evalₐ (J i) n (adicCompletionToComponent J hJ i x) =
      quotientProdPowEquiv J hJ n
        (AdicCompletion.evalₐ (∏ j, J j) n x) i := by
  unfold adicCompletionToComponent
  rw [AdicCompletion.evalₐ_liftRingHom]
  rfl

private noncomputable def quotientAssemblyRingHom
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J)) (n : ℕ) :
    (∀ i, AdicCompletion (J i) R) →+* R ⧸ (∏ i, J i) ^ n :=
  (quotientProdPowEquiv J hJ n).symm.toRingHom.comp
    (RingHom.pi fun i =>
      (AdicCompletion.evalₐ (J i) n).toRingHom.comp
        (Pi.evalRingHom (fun i => AdicCompletion (J i) R) i))

private theorem quotientAssemblyRingHom_compatible
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J)) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow (∏ i, J i) hmn).comp
          (quotientAssemblyRingHom J hJ n) =
        quotientAssemblyRingHom J hJ m := by
  intro m n hmn
  ext x
  change Ideal.Quotient.factorPow (∏ i, J i) hmn
      ((quotientProdPowEquiv J hJ n).symm
        (fun i => AdicCompletion.evalₐ (J i) n (x i))) =
    (quotientProdPowEquiv J hJ m).symm
      (fun i => AdicCompletion.evalₐ (J i) m (x i))
  rw [quotientProdPowEquiv_symm_factorPow J hJ hmn]
  congr 1
  funext i
  exact factorPow_evalₐ (J i) hmn (x i)

/-- Reassemble a tuple of individual adic completions using the inverse
finite-level Chinese-remainder maps. -/
private noncomputable def adicCompletionFromPi
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J)) :
    (∀ i, AdicCompletion (J i) R) →+* AdicCompletion (∏ i, J i) R :=
  AdicCompletion.liftRingHom (∏ i, J i)
    (quotientAssemblyRingHom J hJ)
    (quotientAssemblyRingHom_compatible J hJ)

@[simp]
private theorem evalₐ_adicCompletionFromPi
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J))
    (n : ℕ) (x : ∀ i, AdicCompletion (J i) R) :
    AdicCompletion.evalₐ (∏ i, J i) n (adicCompletionFromPi J hJ x) =
      (quotientProdPowEquiv J hJ n).symm
        (fun i => AdicCompletion.evalₐ (J i) n (x i)) := by
  unfold adicCompletionFromPi
  rw [AdicCompletion.evalₐ_liftRingHom]
  rfl

private noncomputable def adicCompletionToPi
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J)) :
    AdicCompletion (∏ i, J i) R →+* ∀ i, AdicCompletion (J i) R :=
  RingHom.pi fun i => adicCompletionToComponent J hJ i

private theorem adicCompletionToPi_comp_fromPi
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J)) :
    (adicCompletionToPi J hJ).comp (adicCompletionFromPi J hJ) =
      RingHom.id (∀ i, AdicCompletion (J i) R) := by
  apply RingHom.ext
  intro x
  apply funext
  intro i
  apply AdicCompletion.ext_evalₐ
  intro n
  simp [adicCompletionToPi]

private theorem adicCompletionFromPi_comp_toPi
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J)) :
    (adicCompletionFromPi J hJ).comp (adicCompletionToPi J hJ) =
      RingHom.id (AdicCompletion (∏ i, J i) R) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  simp [adicCompletionToPi]

/-- Adic completion at a finite product of pairwise coprime ideals is the
product of the individual adic completions.  The equivalence is induced at
every finite level by the Chinese remainder theorem. -/
noncomputable def adicCompletionProdEquivPi
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J)) :
    AdicCompletion (∏ i, J i) R ≃+* ∀ i, AdicCompletion (J i) R :=
  RingEquiv.ofRingHom
    (adicCompletionToPi J hJ)
    (adicCompletionFromPi J hJ)
    (adicCompletionToPi_comp_fromPi J hJ)
    (adicCompletionFromPi_comp_toPi J hJ)

@[simp]
theorem adicCompletionProdEquivPi_apply
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J))
    (x : AdicCompletion (∏ i, J i) R) (i : ι) :
    adicCompletionProdEquivPi J hJ x i =
      adicCompletionToComponent J hJ i x :=
  rfl

/-- The product decomposition sends the canonical completion image of an
element to its canonical image in every component completion. -/
@[simp]
theorem adicCompletionProdEquivPi_of
    (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J))
    (x : R) (i : ι) :
    adicCompletionProdEquivPi J hJ
        (AdicCompletion.of (∏ j, J j) R x) i =
      AdicCompletion.of (J i) R x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [adicCompletionProdEquivPi_apply,
    evalₐ_adicCompletionToComponent,
    AdicCompletion.evalₐ_of,
    quotientProdPowEquiv_mk,
    AdicCompletion.evalₐ_of]

/-- Equality of ideals induces the canonical equivalence of their adic
completions. -/
noncomputable def adicCompletionIdealCongr
    {I J : Ideal R} (h : I = J) :
    AdicCompletion I R ≃+* AdicCompletion J R := by
  subst J
  exact RingEquiv.refl _

@[simp]
theorem adicCompletionIdealCongr_of
    {I J : Ideal R} (h : I = J) (x : R) :
    adicCompletionIdealCongr h (AdicCompletion.of I R x) =
      AdicCompletion.of J R x := by
  subst J
  rfl

@[reducible]
private noncomputable def integralExtensionPrimesOverFintype
    {A : Type*} [CommRing A] [IsDomain A]
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.Finite A B]
    (p : Ideal A) : Fintype (p.primesOver B) :=
  (Algebra.QuasiFinite.finite_primesOver p).fintype

/-- The prime-power ideals occurring in the factorization of an extended
maximal ideal. -/
def integralExtensionPrimePowerFamily
    {A : Type*} [CommRing A] [IsDomain A]
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B]
    (p : Ideal A) (Q : p.primesOver B) : Ideal B :=
  Q.1 ^ Q.1.ramificationIdx A

@[simp]
theorem integralExtensionPrimePowerFamily_apply
    {A : Type*} [CommRing A] [IsDomain A]
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B]
    (p : Ideal A) (Q : p.primesOver B) :
    integralExtensionPrimePowerFamily p Q =
      Q.1 ^ Q.1.ramificationIdx A :=
  rfl

private theorem integralExtensionPrimePowerFamily_pairwise
    {A : Type*} [CommRing A] [IsDomain A]
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B]
    (p : Ideal A) [p.IsMaximal] :
    Pairwise (IsCoprime on integralExtensionPrimePowerFamily (B := B) p) := by
  intro Q Q' hQQ'
  exact (Ideal.isCoprime_iff_sup_eq.mpr
    (Ideal.IsMaximal.coprime_of_ne
      (Ideal.primesOver.isMaximal Q)
      (Ideal.primesOver.isMaximal Q')
      (Subtype.coe_injective.ne hQQ'))).pow

private theorem integralExtension_map_eq_prod_primePowerFamily
    {A : Type*} [CommRing A] [IsDomain A]
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Module.Finite A B]
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥) :
    letI : Fintype (p.primesOver B) :=
      integralExtensionPrimesOverFintype p
    p.map (algebraMap A B) =
      ∏ Q, integralExtensionPrimePowerFamily (B := B) p Q := by
  let : Fintype (p.primesOver B) :=
    integralExtensionPrimesOverFintype p
  rw [Ideal.map_algebraMap_eq_finsetProd_pow hp]
  simpa [integralExtensionPrimePowerFamily] using
    (Finset.prod_set_coe (s := p.primesOver B)
      (f := fun P => P ^ P.ramificationIdx A)).symm

/-- For a finite integral extension of a Dedekind domain, completion along the
extension of a nonzero maximal ideal splits over the primes above it.  The
factor at `Q` is completed along `Q` to its ramification index; replacing this
power-adic completion by the `Q`-adic completion is the remaining cofinality
step. -/
noncomputable def adicCompletionIntegralExtensionEquivPi
    {A : Type*} [CommRing A] [IsDomain A]
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Module.Finite A B] (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥) :
    AdicCompletion (p.map (algebraMap A B)) B ≃+*
      ∀ Q : p.primesOver B,
        AdicCompletion (Q.1 ^ Q.1.ramificationIdx A) B := by
  classical
  letI : Fintype (p.primesOver B) :=
    integralExtensionPrimesOverFintype p
  let J : p.primesOver B → Ideal B :=
    integralExtensionPrimePowerFamily p
  exact (adicCompletionIdealCongr
      (integralExtension_map_eq_prod_primePowerFamily p hp)).trans
    (adicCompletionProdEquivPi J
      (integralExtensionPrimePowerFamily_pairwise p))

/-- The integral-extension decomposition sends the canonical completion image
of an element to its canonical image in every prime-power factor. -/
@[simp]
theorem adicCompletionIntegralExtensionEquivPi_of
    {A : Type*} [CommRing A] [IsDomain A]
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Module.Finite A B] (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (x : B) (Q : p.primesOver B) :
    adicCompletionIntegralExtensionEquivPi p hp
        (AdicCompletion.of (p.map (algebraMap A B)) B x) Q =
      AdicCompletion.of (Q.1 ^ Q.1.ramificationIdx A) B x := by
  classical
  let : Fintype (p.primesOver B) :=
    integralExtensionPrimesOverFintype p
  let J : p.primesOver B → Ideal B :=
    integralExtensionPrimePowerFamily p
  change (((adicCompletionIdealCongr
      (integralExtension_map_eq_prod_primePowerFamily p hp)).trans
        (adicCompletionProdEquivPi J
          (integralExtensionPrimePowerFamily_pairwise p)))
      (AdicCompletion.of (p.map (algebraMap A B)) B x)) Q = _
  rw [RingEquiv.trans_apply, adicCompletionIdealCongr_of]
  change adicCompletionProdEquivPi J _
      (AdicCompletion.of (∏ j, J j) B x) Q = _
  rw [adicCompletionProdEquivPi_of]
  rfl

end EtaleFundamentalGroups

end
