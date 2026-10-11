/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.Naturality
import Nyll.ProCGroups.FoxDifferential.Completed.Comparison.FiniteStage
import Nyll.ProCGroups.Completion.ProCIntegerPrimePower

/-!
# Fox differential: completed — comparison — discrete completion

The principal declarations in this module are:

- `foxAlgebraicStageGroupRingReduction`
  Coefficient reduction from the integral group ring \(\mathbb{Z}[F/N]\) to the finite-stage target
  group algebra \((\mathbb{Z}/n\mathbb{Z})[F/N]\).
- `foxAlgebraicStageGroupRingReduction_of`
  The finite-stage group-ring reduction sends a group-like basis element to the same quotient basis
  element with reduced coefficient.
- `foxAlgebraicStageGroupRingReduction_apply`
  Coefficients of the finite-stage group-ring reduction are ordinary reduction modulo \(n\).
- `int_eq_zero_of_forall_zmod_cast_eq_zero`
  An integer whose image in every positive residue ring is zero is zero.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u

section DiscreteCompletion

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/--
Coefficient reduction from the integral group ring \(\mathbb{Z}[F/N]\) to the finite-stage
target group algebra \((\mathbb{Z}/n\mathbb{Z})[F/N]\).
-/
def foxAlgebraicStageGroupRingReduction :
    GroupRing (foxAlgebraicStageTargetQuotient (X := X) N) →+*
      foxAlgebraicStageTargetGroupAlgebra (X := X) N n :=
  MonoidAlgebra.mapRingHom
    (foxAlgebraicStageTargetQuotient (X := X) N)
    (Int.castRingHom (ModNCompletedCoeff n))

omit [DecidableEq X] in
/--
The finite-stage group-ring reduction sends a group-like basis element to the same quotient
basis element with reduced coefficient.
-/
@[simp]
theorem foxAlgebraicStageGroupRingReduction_of
    (q : foxAlgebraicStageTargetQuotient (X := X) N) :
    foxAlgebraicStageGroupRingReduction (X := X) N n
        (MonoidAlgebra.of ℤ (foxAlgebraicStageTargetQuotient (X := X) N) q) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N) q := by
  simp only [foxAlgebraicStageGroupRingReduction, MonoidAlgebra.of_apply,
    MonoidAlgebra.mapRingHom_single, map_one]

omit [DecidableEq X] in
/-- Coefficients of the finite-stage group-ring reduction are ordinary reduction modulo \(n\). -/
@[simp]
theorem foxAlgebraicStageGroupRingReduction_apply
    (x : GroupRing (foxAlgebraicStageTargetQuotient (X := X) N))
    (q : foxAlgebraicStageTargetQuotient (X := X) N) :
    (foxAlgebraicStageGroupRingReduction (X := X) N n x).coeff q =
      (x.coeff q : ModNCompletedCoeff n) := by
  rw [foxAlgebraicStageGroupRingReduction]
  exact MonoidAlgebra.coeff_mapRingHom
    (Int.castRingHom (ModNCompletedCoeff n)) x q

/-- An integer whose image in every positive residue ring is zero is zero. -/
theorem int_eq_zero_of_forall_zmod_cast_eq_zero
    (z : ℤ) (hz : ∀ n : ℕ, 0 < n → (z : ZMod n) = 0) :
    z = 0 := by
  by_contra hzne
  let n : ℕ := z.natAbs + 1
  have hn : 0 < n := Nat.succ_pos z.natAbs
  have hzmod : (z : ZMod n) = 0 := hz n hn
  have hdvdInt : (n : ℤ) ∣ z := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd z n).mp hzmod
  have hdvdNat : n ∣ z.natAbs := (Int.natCast_dvd).1 hdvdInt
  have hzabs_pos : 0 < z.natAbs := Int.natAbs_pos.mpr hzne
  have hle : n ≤ z.natAbs := Nat.le_of_dvd hzabs_pos hdvdNat
  exact Nat.not_succ_le_self z.natAbs hle

/-- An integer whose image in every \(p^k\) residue ring is zero is zero. -/
theorem int_eq_zero_of_forall_zmod_prime_pow_cast_eq_zero
    (p : ℕ) [Fact (Nat.Prime p)] (z : ℤ)
    (hz : ∀ k : ℕ, (z : ZMod (p ^ k)) = 0) :
    z = 0 := by
  by_contra hzne
  let k : ℕ := Nat.log p z.natAbs + 1
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hlt : z.natAbs < p ^ k := by
    simpa [k, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self hp1 z.natAbs
  have hzmod : (z : ZMod (p ^ k)) = 0 := hz k
  have hdvdInt : ((p ^ k : ℕ) : ℤ) ∣ z := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd z (p ^ k)).mp hzmod
  have hdvdNat : p ^ k ∣ z.natAbs := (Int.natCast_dvd).1 hdvdInt
  have hzabs_pos : 0 < z.natAbs := Int.natAbs_pos.mpr hzne
  have hle : p ^ k ≤ z.natAbs := Nat.le_of_dvd hzabs_pos hdvdNat
  exact (not_lt_of_ge hle) hlt

omit [DecidableEq X] in
/-- Integral group rings are torsion-free for positive natural scalar multiplication. -/
theorem groupRing_eq_zero_of_nsmul_eq_zero
    {M : Type*} [Monoid M] {n : ℕ} (hn : 0 < n) (x : GroupRing M)
    (hx : n • x = 0) :
    x = 0 := by
  ext m
  have hcoeff : n • x.coeff m = 0 := by
    exact congrArg (fun y : GroupRing M => y.coeff m) hx
  have hmul : (n : ℤ) * x.coeff m = 0 := by
    rw [← nsmul_eq_mul]
    exact hcoeff
  exact (Int.mul_eq_zero.mp hmul).resolve_left (by exact_mod_cast (Nat.ne_of_gt hn))

omit [DecidableEq X] in
/--
A finite-support integral group-ring element is zero if all of its positive residue reductions
are zero.
-/
theorem groupRing_eq_zero_of_forall_foxAlgebraicStageGroupRingReduction_eq_zero
    (x : GroupRing (foxAlgebraicStageTargetQuotient (X := X) N))
    (hx : ∀ n : ℕ, 0 < n →
      foxAlgebraicStageGroupRingReduction (X := X) N n x = 0) :
    x = 0 := by
  ext q
  apply int_eq_zero_of_forall_zmod_cast_eq_zero
  intro n hn
  have hcoeff := congrArg (fun y => y.coeff q) (hx n hn)
  simpa using hcoeff

omit [DecidableEq X] in
/--
A finite-support integral group-ring element is zero if all of its \(p^k\) residue reductions
are zero.
-/
theorem groupRing_eq_zero_of_forall_foxAlgebraicStageGroupRingReduction_primePow_eq_zero
    (p : ℕ) [Fact (Nat.Prime p)]
    (x : GroupRing (foxAlgebraicStageTargetQuotient (X := X) N))
    (hx : ∀ k : ℕ,
      foxAlgebraicStageGroupRingReduction (X := X) N (p ^ k) x = 0) :
    x = 0 := by
  ext q
  apply int_eq_zero_of_forall_zmod_prime_pow_cast_eq_zero p
  intro k
  have hcoeff := congrArg (fun y => y.coeff q) (hx k)
  simpa using hcoeff

omit [DecidableEq X] in
/--
A finite-stage residue-zero integral group-ring element is divisible by the chosen coefficient
modulus.
-/
theorem exists_eq_nsmul_of_foxAlgebraicStageGroupRingReduction_eq_zero
    {n : ℕ}
    (x : GroupRing (foxAlgebraicStageTargetQuotient (X := X) N))
    (hx : foxAlgebraicStageGroupRingReduction (X := X) N n x = 0) :
    ∃ y : GroupRing (foxAlgebraicStageTargetQuotient (X := X) N), x = n • y := by
  classical
  let Q := foxAlgebraicStageTargetQuotient (X := X) N
  have hdvd : ∀ q : Q, (n : ℤ) ∣ x.coeff q := by
    intro q
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (x.coeff q) n).mp (by
      have hcoeff :=
        congrArg
          (fun y : foxAlgebraicStageTargetGroupAlgebra (X := X) N n =>
            y.coeff q) hx
      simpa using hcoeff)
  let coeff : Q → ℤ := fun q =>
    if x.coeff q = 0 then 0 else Classical.choose (hdvd q)
  have hcoeff_support : ∀ q : Q, coeff q ≠ 0 → q ∈ x.coeff.support := by
    intro q hq
    rw [Finsupp.mem_support_iff]
    intro hxq
    have hzero : coeff q = 0 := by
      dsimp [coeff]
      rw [ite_eq_left hxq]
    exact hq hzero
  let y : GroupRing Q :=
    MonoidAlgebra.ofCoeff
      (Finsupp.onFinset x.coeff.support coeff hcoeff_support)
  refine ⟨y, ?_⟩
  ext q
  change x.coeff q = n • coeff q
  by_cases hxq : x.coeff q = 0
  · simp only [hxq, ↓reduceIte, nsmul_zero, coeff]
  · have hchoose := Classical.choose_spec (hdvd q)
    simpa [coeff, hxq, nsmul_eq_mul] using hchoose

/--
The finite-stage derivative vector is the image of the ordinary relative Fox derivative under
coefficient reduction from \(\mathbb{Z}[F/N]\) to \((\mathbb{Z}/n\mathbb{Z})[F/N]\).
-/
theorem foxAlgebraicStageDerivativeVector_eq_discreteReduction
    (w : FreeGroup X) :
    foxAlgebraicStageDerivativeVector (X := X) N n w =
      fun i : X =>
        foxAlgebraicStageGroupRingReduction (X := X) N n
          (FoxCalculus.relativeFreeGroupFoxDerivative
            (H := foxAlgebraicStageTargetQuotient (X := X) N)
            X (QuotientGroup.mk' N) w i) := by
  let delta : ScalarCrossedHom
      (foxAlgebraicStageCoefficient (X := X) N n)
      (foxAlgebraicStageCoordinateVector (X := X) N n) :=
    { toFun := fun w i =>
        foxAlgebraicStageGroupRingReduction (X := X) N n
          (FoxCalculus.relativeFreeGroupFoxDerivative
            (H := foxAlgebraicStageTargetQuotient (X := X) N)
            X (QuotientGroup.mk' N) w i)
      map_mul' := by
        intro u v
        rw [scalarCrossedAction_apply]
        funext i
        change foxAlgebraicStageGroupRingReduction (X := X) N n
            (FoxCalculus.relativeFreeGroupFoxDerivative
              (H := foxAlgebraicStageTargetQuotient (X := X) N)
              X (QuotientGroup.mk' N) (u * v) i) =
          foxAlgebraicStageGroupRingReduction (X := X) N n
            (FoxCalculus.relativeFreeGroupFoxDerivative
              (H := foxAlgebraicStageTargetQuotient (X := X) N)
              X (QuotientGroup.mk' N) u i) +
            foxAlgebraicStageCoefficient (X := X) N n u *
              foxAlgebraicStageGroupRingReduction (X := X) N n
                (FoxCalculus.relativeFreeGroupFoxDerivative
                  (H := foxAlgebraicStageTargetQuotient (X := X) N)
                  X (QuotientGroup.mk' N) v i)
        rw [show
          FoxCalculus.relativeFreeGroupFoxDerivative
              (H := foxAlgebraicStageTargetQuotient (X := X) N)
              X (QuotientGroup.mk' N) (u * v) i =
            FoxCalculus.relativeFreeGroupFoxDerivative
              (H := foxAlgebraicStageTargetQuotient (X := X) N)
              X (QuotientGroup.mk' N) u i +
            (MonoidAlgebra.of ℤ (foxAlgebraicStageTargetQuotient (X := X) N)
                (QuotientGroup.mk' N u) :
                FoxDifferential.GroupRing (foxAlgebraicStageTargetQuotient (X := X) N)) *
              FoxCalculus.relativeFreeGroupFoxDerivative
                (H := foxAlgebraicStageTargetQuotient (X := X) N)
                X (QuotientGroup.mk' N) v i by
          simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
            congrFun
              (FoxCalculus.relativeFreeGroupFoxDerivative_mul
                (H := foxAlgebraicStageTargetQuotient (X := X) N)
                X (QuotientGroup.mk' N) u v) i]
        rw [map_add, map_mul, foxAlgebraicStageGroupRingReduction_of]
        rfl }
  have hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n) := by
    intro x
    change (fun i : X =>
      foxAlgebraicStageGroupRingReduction (X := X) N n
        (FoxCalculus.relativeFreeGroupFoxDerivative
          (H := foxAlgebraicStageTargetQuotient (X := X) N)
          X (QuotientGroup.mk' N) (FreeGroup.of x) i)) =
      Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
    funext i
    by_cases hix : i = x
    · subst i
      simp only [FoxCalculus.relativeFreeGroupFoxDerivative_of,
        Pi.single_eq_same, map_one]
    · simp only [FoxCalculus.relativeFreeGroupFoxDerivative_of,
        Pi.single_eq_of_ne hix, map_zero]
  have hdelta_eq :
      delta = foxAlgebraicStageDerivativeVectorCrossedHom (X := X) N n :=
    foxAlgebraicStageDerivativeVector_unique (X := X) N n delta hbasis
  have hw := congrArg (fun d => d w) hdelta_eq
  change
    foxAlgebraicStageDerivativeVectorCrossedHom (X := X) N n w = delta w
  exact hw.symm

/--
The comparison between the finite-stage derivative and the ordinary relative Fox derivative
holds componentwise.
-/
theorem foxAlgebraicStageDerivative_eq_discreteReduction
    (i : X) (w : FreeGroup X) :
    foxAlgebraicStageDerivative (X := X) N n i w =
      foxAlgebraicStageGroupRingReduction (X := X) N n
        (FoxCalculus.relativeFreeGroupFoxDerivative
          (H := foxAlgebraicStageTargetQuotient (X := X) N)
          X (QuotientGroup.mk' N) w i) := by
  have h := congrFun
    (foxAlgebraicStageDerivativeVector_eq_discreteReduction (X := X) N n w) i
  simpa [foxAlgebraicStageDerivative] using h

/--
One finite-stage derivative-vector vanishing says that the ordinary integral relative Fox
derivative vector is divisible by the coefficient modulus.
-/
theorem exists_eq_nsmul_relFreeFoxDeriv_of_foxAlgebraicStageDerivativeVector_eq_zero
    {n : ℕ} (w : FreeGroup X)
    (hder : foxAlgebraicStageDerivativeVector (X := X) N n w = 0) :
    ∃ y : X → GroupRing (foxAlgebraicStageTargetQuotient (X := X) N),
      FoxCalculus.relativeFreeGroupFoxDerivative
        (H := foxAlgebraicStageTargetQuotient (X := X) N)
        X (QuotientGroup.mk' N) w = n • y := by
  classical
  have hred :
      ∀ i : X,
        foxAlgebraicStageGroupRingReduction (X := X) N n
          (FoxCalculus.relativeFreeGroupFoxDerivative
            (H := foxAlgebraicStageTargetQuotient (X := X) N)
            X (QuotientGroup.mk' N) w i) = 0 := by
    intro i
    have hcomp :=
      congrFun (foxAlgebraicStageDerivativeVector_eq_discreteReduction (X := X) N n w) i
    have hzero := congrFun hder i
    exact hcomp.symm.trans hzero
  choose y hy using fun i =>
    exists_eq_nsmul_of_foxAlgebraicStageGroupRingReduction_eq_zero (X := X) N
      (FoxCalculus.relativeFreeGroupFoxDerivative
        (H := foxAlgebraicStageTargetQuotient (X := X) N)
        X (QuotientGroup.mk' N) w i)
      (hred i)
  refine ⟨y, ?_⟩
  funext i
  exact hy i

/--
Residue-universal version of one-modulus divisibility for the ordinary integral relative Fox
derivative vector.
-/
theorem exists_eq_nsmul_relFreeFoxDeriv_of_residueUnivDiff_eq_zero
    [Finite X]
    {n : ℕ} (w : FreeGroup X)
    (hres : residueUniversalDifferential n (QuotientGroup.mk' N) w = 0) :
    ∃ y : X → GroupRing (foxAlgebraicStageTargetQuotient (X := X) N),
      FoxCalculus.relativeFreeGroupFoxDerivative
        (H := foxAlgebraicStageTargetQuotient (X := X) N)
        X (QuotientGroup.mk' N) w = n • y := by
  classical
  let : Fintype X := Fintype.ofFinite X
  exact
    exists_eq_nsmul_relFreeFoxDeriv_of_foxAlgebraicStageDerivativeVector_eq_zero
      (X := X) N w
      ((foxAlgebraicStageDerivativeVector_eq_zero_iff_residueUniversalDifferential_eq_zero
        (X := X) (N := N) (n := n) (w := w)).2 hres)

/--
If every positive finite-stage derivative vanishes, then the ordinary integral relative Fox
derivative vanishes.
-/
theorem relFreeFoxDeriv_eq_zero_of_forall_foxAlgebraicStageDerivative_eq_zero
    (w : FreeGroup X)
    (hder :
      ∀ n : ℕ, 0 < n →
        ∀ i : X, foxAlgebraicStageDerivative (X := X) N n i w = 0) :
    FoxCalculus.relativeFreeGroupFoxDerivative
      (H := foxAlgebraicStageTargetQuotient (X := X) N)
      X (QuotientGroup.mk' N) w = 0 := by
  funext i
  apply groupRing_eq_zero_of_forall_foxAlgebraicStageGroupRingReduction_eq_zero
    (X := X) N
  intro n hn
  exact
    (foxAlgebraicStageDerivative_eq_discreteReduction (X := X) N n i w).symm.trans
      (hder n hn i)

/--
If every \(p^k\) finite-stage derivative vanishes, then the ordinary integral relative Fox
derivative vanishes.
-/
theorem relFreeFoxDeriv_eq_zero_of_forall_foxAlgebraicStageDerivative_primePow_eq_zero
    (p : ℕ) [Fact (Nat.Prime p)] (w : FreeGroup X)
    (hder :
      ∀ k : ℕ,
        ∀ i : X, foxAlgebraicStageDerivative (X := X) N (p ^ k) i w = 0) :
    FoxCalculus.relativeFreeGroupFoxDerivative
      (H := foxAlgebraicStageTargetQuotient (X := X) N)
      X (QuotientGroup.mk' N) w = 0 := by
  funext i
  apply groupRing_eq_zero_of_forall_foxAlgebraicStageGroupRingReduction_primePow_eq_zero
    (X := X) N p
  intro k
  exact
    (foxAlgebraicStageDerivative_eq_discreteReduction (X := X) N (p ^ k) i w).symm.trans
      (hder k i)

section CompletedProjection

variable (C : ProCGroups.FiniteGroupClass.{u})
variable [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
variable [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]

/--
Projecting the completed \(\mathbb{Z}_C\) derivative to a finite pro-\(C\) target stage gives
the stage map applied to the reduced ordinary relative Fox derivative.
-/
theorem zcFreeGroupFoxDerivative_finiteStageProjection_discreteReduction
    (i : X) (w : FreeGroup X)
    (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N)) :
    zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
        (zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i w) =
      (letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
       modNCompletedGroupAlgebraStageMapInClass j.1.modulus
        (zcFiniteStageTarget X N) C j.2
        (foxAlgebraicStageGroupRingReduction (X := X) N j.1.modulus
          (FoxCalculus.relativeFreeGroupFoxDerivative
            (H := zcFiniteStageTarget X N) X (QuotientGroup.mk' N) w i))) := by
  let : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  rw [zcFreeGroupFoxDerivative_finiteStageProjection C N j i w]
  rw [foxAlgebraicStageDerivative_eq_discreteReduction (X := X) N j.1.modulus i w]

/-- Vector-valued form of the discrete-to-completed projection comparison. -/
theorem zcFreeGroupFoxDerivativeVector_finiteStageProjection_discreteReduction
    (w : FreeGroup X)
    (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N)) :
    (fun i : X =>
      zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
        (zcFreeGroupFoxDerivativeVector C (QuotientGroup.mk' N) w i)) =
      fun i : X =>
        letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
        modNCompletedGroupAlgebraStageMapInClass j.1.modulus
          (zcFiniteStageTarget X N) C j.2
          (foxAlgebraicStageGroupRingReduction (X := X) N j.1.modulus
            (FoxCalculus.relativeFreeGroupFoxDerivative
              (H := zcFiniteStageTarget X N) X (QuotientGroup.mk' N) w i)) := by
  funext i
  exact zcFreeGroupFoxDerivative_finiteStageProjection_discreteReduction
    (C := C) (X := X) N i w j

/--
The completed \(\mathbb{Z}_C\) component derivative is uniquely determined by the finite-stage
projections of the ordinary relative Fox derivative after coefficient reduction.
-/
theorem zcFreeGroupFoxDerivative_unique_finiteStageProjection_discreteReduction
    (i : X)
    (delta : FreeGroup X →
      ZCCompletedGroupAlgebra C (zcFiniteStageTarget X N))
    (hprojection : ∀ w
      (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N)),
      zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j (delta w) =
        (letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
         modNCompletedGroupAlgebraStageMapInClass j.1.modulus
          (zcFiniteStageTarget X N) C j.2
            (foxAlgebraicStageGroupRingReduction (X := X) N j.1.modulus
            (FoxCalculus.relativeFreeGroupFoxDerivative
              (H := zcFiniteStageTarget X N) X (QuotientGroup.mk' N) w i)))) :
    delta = zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i := by
  refine zcFreeGroupFoxDerivative_unique_finiteStageProjection
    (C := C) (X := X) N i delta ?_
  intro w j
  let : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  rw [hprojection w j]
  rw [← foxAlgebraicStageDerivative_eq_discreteReduction (X := X) N j.1.modulus i w]

/--
Existence and uniqueness of the completed \(\mathbb{Z}_C\) component derivative characterized by
the finite-stage projections of the reduced ordinary relative Fox derivative.
-/
theorem existsUnique_zcFreeGroupFoxDerivative_finiteStageProjection_discreteReduction
    (i : X) :
    ∃! delta : FreeGroup X →
      ZCCompletedGroupAlgebra C (zcFiniteStageTarget X N),
      ∀ w
        (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N)),
        zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j (delta w) =
          (letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
           modNCompletedGroupAlgebraStageMapInClass j.1.modulus
            (zcFiniteStageTarget X N) C j.2
            (foxAlgebraicStageGroupRingReduction (X := X) N j.1.modulus
              (FoxCalculus.relativeFreeGroupFoxDerivative
                (H := zcFiniteStageTarget X N) X (QuotientGroup.mk' N) w i))) := by
  refine ⟨zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i, ?_, ?_⟩
  · intro w j
    exact zcFreeGroupFoxDerivative_finiteStageProjection_discreteReduction
      (C := C) (X := X) N i w j
  · intro delta hprojection
    exact zcFreeGroupFoxDerivative_unique_finiteStageProjection_discreteReduction
      (C := C) (X := X) N i delta hprojection

/--
The completed \(\mathbb{Z}_C\) derivative vector is uniquely determined by the finite-stage
projections of the ordinary relative Fox derivative after coefficient reduction.
-/
theorem zcFreeGroupFoxDerivativeVector_unique_finiteStageProjection_discreteReduction
    (delta : FreeGroup X →
      ZCFreeFoxCoordinates C (X := X) (H := zcFiniteStageTarget X N))
    (hprojection : ∀ w
      (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N)),
      (fun i : X =>
        zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j (delta w i)) =
        fun i : X =>
          letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
          modNCompletedGroupAlgebraStageMapInClass j.1.modulus
            (zcFiniteStageTarget X N) C j.2
            (foxAlgebraicStageGroupRingReduction (X := X) N j.1.modulus
              (FoxCalculus.relativeFreeGroupFoxDerivative
                (H := zcFiniteStageTarget X N) X (QuotientGroup.mk' N) w i))) :
    delta = zcFreeGroupFoxDerivativeVector C (QuotientGroup.mk' N) := by
  refine zcFreeGroupFoxDerivativeVector_unique_finiteStageProjection
    (C := C) (X := X) N delta ?_
  intro w j
  funext i
  let : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  have hcoord := congrFun (hprojection w j) i
  rw [hcoord]
  rw [← foxAlgebraicStageDerivative_eq_discreteReduction (X := X) N j.1.modulus i w]

/--
Existence and uniqueness of the completed \(\mathbb{Z}_C\) derivative vector characterized by
the finite-stage projections of the reduced ordinary relative Fox derivative.
-/
theorem existsUnique_zcFreeFoxDerivVec_finiteStageProj_discreteReduction :
    ∃! delta : FreeGroup X →
      ZCFreeFoxCoordinates C (X := X) (H := zcFiniteStageTarget X N),
      ∀ w
        (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N)),
        (fun i : X =>
          zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
            (delta w i)) =
          fun i : X =>
            letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
            modNCompletedGroupAlgebraStageMapInClass j.1.modulus
              (zcFiniteStageTarget X N) C j.2
              (foxAlgebraicStageGroupRingReduction (X := X) N j.1.modulus
                (FoxCalculus.relativeFreeGroupFoxDerivative
                  (H := zcFiniteStageTarget X N) X (QuotientGroup.mk' N) w i)) := by
  refine ⟨zcFreeGroupFoxDerivativeVector C (QuotientGroup.mk' N), ?_, ?_⟩
  · intro w j
    exact zcFreeGroupFoxDerivativeVector_finiteStageProjection_discreteReduction
      (C := C) (X := X) N w j
  · intro delta hprojection
    exact zcFreeGroupFoxDerivativeVector_unique_finiteStageProjection_discreteReduction
      (C := C) (X := X) N delta hprojection

/--
Projecting the completed Fox-Euler formula and reducing the coefficients identifies the
derivative coordinates with the ordinary relative Fox derivative.
-/
theorem zcFreeGroupFoxDerivative_fundFormula_finiteStageProj_discreteReduction
    [Fintype X]
    (w : FreeGroup X)
    (j : ZCCompletedGroupAlgebraIndex C (zcFiniteStageTarget X N)) :
    zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
        (zcCompletedGroupAlgebraBoundary C (QuotientGroup.mk' N) w) =
      ∑ i : X,
        (letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
         modNCompletedGroupAlgebraStageMapInClass j.1.modulus
          (zcFiniteStageTarget X N) C j.2
          (foxAlgebraicStageGroupRingReduction (X := X) N j.1.modulus
            (FoxCalculus.relativeFreeGroupFoxDerivative
              (H := zcFiniteStageTarget X N) X (QuotientGroup.mk' N) w i))) *
        zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
          (zcGroupLike C (zcFiniteStageTarget X N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  rw [zcFreeGroupFoxDerivative_fundamental_formula_finiteStageProjection_stageMap
    (C := C) (X := X) N w j]
  apply Finset.sum_congr rfl
  intro i hi
  let : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  rw [foxAlgebraicStageDerivative_eq_discreteReduction (X := X) N j.1.modulus i w]

/--
Over the all-finite coefficient class, a zero completed derivative vector on the finite quotient
map already forces the ordinary integral relative Fox derivative to vanish.
-/
theorem relFreeFoxDeriv_eq_zero_of_zcFreeFoxDerivVec_eq_zero_allFinite
    [DiscreteTopology (foxAlgebraicStageTargetQuotient (X := X) N)]
    [Finite (foxAlgebraicStageTargetQuotient (X := X) N)]
    (w : FreeGroup X)
    (hw :
      zcFreeGroupFoxDerivativeVector
        (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{u})
        (QuotientGroup.mk' N) w = 0) :
    FoxCalculus.relativeFreeGroupFoxDerivative
      (H := foxAlgebraicStageTargetQuotient (X := X) N)
      X (QuotientGroup.mk' N) w = 0 := by
  apply relFreeFoxDeriv_eq_zero_of_forall_foxAlgebraicStageDerivative_eq_zero
    (X := X) N w
  intro n hn i
  let j : ProCGroups.Completion.ProCIntegerIndex
      (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{u}) :=
    ProCGroups.Completion.ProCIntegerIndex.ofAllFiniteModulus n hn
  have hjmod : j.modulus = n := rfl
  have hCtarget :
      (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{u})
        (foxAlgebraicStageTargetQuotient (X := X) N) := by
    exact (inferInstance :
      Finite (foxAlgebraicStageTargetQuotient (X := X) N))
  have hcomponent :
      zcFreeGroupFoxDerivative
          (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{u})
          (QuotientGroup.mk' N) i w = 0 := by
    simpa [zcFreeGroupFoxDerivative] using congrFun hw i
  have hstage :=
    foxAlgebraicStageDerivative_eq_zero_of_zcFreeGroupFoxDerivative_eq_zero
      (C := (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{u}))
      (X := X) N
      (hIso := ProCGroups.FiniteGroupClass.allFinite_isomClosed)
      (hCtarget := hCtarget)
      j i hcomponent
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro q
  have hcoeff := congrArg (fun z => z.coeff q) hstage
  change
    (foxAlgebraicStageDerivative (X := X) N j.modulus i w).coeff q = 0
  exact hcoeff.trans (by rfl)

/--
Over the all-finite coefficient class, a zero completed universal differential on the finite
quotient map already forces the ordinary integral relative Fox derivative to vanish.
-/
theorem relFreeFoxDeriv_eq_zero_of_zcUnivDiff_eq_zero_allFinite
    [DiscreteTopology (foxAlgebraicStageTargetQuotient (X := X) N)]
    [Finite (foxAlgebraicStageTargetQuotient (X := X) N)]
    (w : FreeGroup X)
    (hw :
      zcUniversalDifferential
        (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{u})
        (QuotientGroup.mk' N) w = 0) :
    FoxCalculus.relativeFreeGroupFoxDerivative
      (H := foxAlgebraicStageTargetQuotient (X := X) N)
      X (QuotientGroup.mk' N) w = 0 := by
  exact
    relFreeFoxDeriv_eq_zero_of_zcFreeFoxDerivVec_eq_zero_allFinite
      (X := X) N w
      (zcFreeGroupFoxDerivativeVector_eq_zero_of_zcUniversalDifferential_eq_zero
        (C := (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{u}))
        (QuotientGroup.mk' N) hw)

/--
Over the finite \(p\)-group coefficient class, a zero completed derivative vector on the finite
quotient map forces the ordinary integral relative Fox derivative to vanish, using only the
prime-power coefficient stages.
-/
theorem relFreeFoxDeriv_eq_zero_of_zcFreeFoxDerivVec_eq_zero_pGroup
    (p : ℕ) [Fact (Nat.Prime p)]
    [DiscreteTopology (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hCtarget :
      ProCGroups.FiniteGroupClass.pGroup p
        (foxAlgebraicStageTargetQuotient (X := X) N))
    (w : FreeGroup X)
    (hw :
      zcFreeGroupFoxDerivativeVector
        (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{u})
        (QuotientGroup.mk' N) w = 0) :
    FoxCalculus.relativeFreeGroupFoxDerivative
      (H := foxAlgebraicStageTargetQuotient (X := X) N)
      X (QuotientGroup.mk' N) w = 0 := by
  apply relFreeFoxDeriv_eq_zero_of_forall_foxAlgebraicStageDerivative_primePow_eq_zero
    (X := X) N p w
  intro k i
  let j : ProCGroups.Completion.ProCIntegerIndex
      (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{u}) :=
    ProCGroups.Completion.ProCIntegerIndex.pGroupPower p k
  have hjmod : j.modulus = p ^ k := rfl
  have hcomponent :
      zcFreeGroupFoxDerivative
          (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{u})
          (QuotientGroup.mk' N) i w = 0 := by
    simpa [zcFreeGroupFoxDerivative] using congrFun hw i
  have hstage :=
    foxAlgebraicStageDerivative_eq_zero_of_zcFreeGroupFoxDerivative_eq_zero
      (C := (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{u}))
      (X := X) N
      (hIso := (ProCGroups.FiniteGroupClass.pGroup_formation p).isomClosed)
      (hCtarget := hCtarget)
      j i hcomponent
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro q
  have hcoeff := congrArg (fun z => z.coeff q) hstage
  change
    (foxAlgebraicStageDerivative (X := X) N j.modulus i w).coeff q = 0
  exact hcoeff.trans (by rfl)

/--
Over the finite \(p\)-group coefficient class, a zero completed universal differential on the
finite quotient map already forces the ordinary integral relative Fox derivative to vanish,
using only the prime-power coefficient stages.
-/
theorem relativeFreeGroupFoxDerivative_eq_zero_of_zcUniversalDifferential_eq_zero_pGroup
    (p : ℕ) [Fact (Nat.Prime p)]
    [DiscreteTopology (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hCtarget :
      ProCGroups.FiniteGroupClass.pGroup p
        (foxAlgebraicStageTargetQuotient (X := X) N))
    (w : FreeGroup X)
    (hw :
      zcUniversalDifferential
        (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{u})
        (QuotientGroup.mk' N) w = 0) :
    FoxCalculus.relativeFreeGroupFoxDerivative
      (H := foxAlgebraicStageTargetQuotient (X := X) N)
      X (QuotientGroup.mk' N) w = 0 := by
  exact
    relFreeFoxDeriv_eq_zero_of_zcFreeFoxDerivVec_eq_zero_pGroup
      (X := X) N p hCtarget w
      (zcFreeGroupFoxDerivativeVector_eq_zero_of_zcUniversalDifferential_eq_zero
        (C := (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{u}))
        (QuotientGroup.mk' N) hw)

end CompletedProjection

end DiscreteCompletion

section FiniteTarget

variable {X : Type u} [DecidableEq X]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
All-finite coefficient separation holds for an arbitrary finite discrete target map. The
quotient-map version is applied after identifying the target with \(\mathrm{FreeGroup}(X)/\ker
\psi\), and completed derivative vectors are transported by target naturality.
-/
theorem relFreeFoxDeriv_eq_zero_of_zcFreeFoxDerivVec_eq_zero_allFinite_of_surj
    [DiscreteTopology H] [Finite H]
    (ψ : FreeGroup X →* H) (hψ : Function.Surjective ψ)
    (w : FreeGroup X)
    (hw :
      zcFreeGroupFoxDerivativeVector
        (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{u})
        ψ w = 0) :
    FoxCalculus.relativeFreeGroupFoxDerivative (H := H) X ψ w = 0 := by
  let N : Subgroup (FreeGroup X) := ψ.ker
  let Q : Type u := foxAlgebraicStageTargetQuotient (X := X) N
  let : TopologicalSpace Q := ⊥
  let : DiscreteTopology Q := ⟨rfl⟩
  let : IsTopologicalGroup Q := inferInstance
  let e : Q ≃* H := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  let : Finite Q := Finite.of_injective e e.injective
  let q : FreeGroup X →* Q := QuotientGroup.mk' N
  have he_apply (g : FreeGroup X) : e (q g) = ψ g := by
    change QuotientGroup.quotientKerEquivOfSurjective ψ hψ
        (QuotientGroup.mk' ψ.ker g) = ψ g
    rfl
  let eSymm : H →ₜ* Q :=
    { toMonoidHom := e.symm.toMonoidHom
      continuous_toFun := continuous_of_discreteTopology }
  have hcompSymm : eSymm.toMonoidHom.comp ψ = q := by
    apply MonoidHom.ext
    intro g
    apply e.injective
    change e (e.symm (ψ g)) = e (q g)
    simpa using (he_apply g).symm
  have hvecQ :
      zcFreeGroupFoxDerivativeVector
          (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{u})
          q w = 0 := by
    have htarget :=
      zcFreeGroupFoxDerivativeVector_mapTarget
        (C := (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{u}))
        ProCGroups.FiniteGroupClass.allFinite_hereditary ψ eSymm w
    rw [hcompSymm] at htarget
    rw [htarget, hw]
    rfl
  have hq :
      FoxCalculus.relativeFreeGroupFoxDerivative (H := Q) X q w = 0 :=
    relFreeFoxDeriv_eq_zero_of_zcFreeFoxDerivVec_eq_zero_allFinite
      (X := X) N w hvecQ
  have hcomp : e.toMonoidHom.comp q = ψ := by
    apply MonoidHom.ext
    intro g
    exact he_apply g
  have hnat :=
    FoxCalculus.relativeFreeGroupFoxDerivative_mapDomain
      (H := Q) (K := H) q e.toMonoidHom w
  rw [hcomp] at hnat
  rw [hnat, hq]
  rfl

/--
Over the all-finite coefficient class, a zero completed universal differential on an arbitrary
finite discrete target map already forces the ordinary integral relative Fox derivative to
vanish.
-/
theorem relFreeFoxDeriv_eq_zero_of_zcUnivDiff_eq_zero_allFinite_of_surj
    [DiscreteTopology H] [Finite H]
    (ψ : FreeGroup X →* H) (hψ : Function.Surjective ψ)
    (w : FreeGroup X)
    (hw :
      zcUniversalDifferential
        (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{u})
        ψ w = 0) :
    FoxCalculus.relativeFreeGroupFoxDerivative (H := H) X ψ w = 0 :=
  relFreeFoxDeriv_eq_zero_of_zcFreeFoxDerivVec_eq_zero_allFinite_of_surj
    (X := X) ψ hψ w
    (zcFreeGroupFoxDerivativeVector_eq_zero_of_zcUniversalDifferential_eq_zero
      (C := (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{u}))
      ψ hw)

/--
Prime-power coefficient separation for an arbitrary finite discrete \(p\)-group target map. The
quotient-map version is applied after identifying the target with \(\mathrm{FreeGroup}(X)/\ker
\psi\); completed derivative vectors are transported by target naturality.
-/
theorem relFreeFoxDeriv_eq_zero_of_zcFreeFoxDerivVec_eq_zero_pGroup_of_surj
    (p : ℕ) [Fact (Nat.Prime p)]
    [DiscreteTopology H]
    (hCtarget : ProCGroups.FiniteGroupClass.pGroup p H)
    (ψ : FreeGroup X →* H) (hψ : Function.Surjective ψ)
    (w : FreeGroup X)
    (hw :
      zcFreeGroupFoxDerivativeVector
        (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{u})
        ψ w = 0) :
    FoxCalculus.relativeFreeGroupFoxDerivative (H := H) X ψ w = 0 := by
  let N : Subgroup (FreeGroup X) := ψ.ker
  let Q : Type u := foxAlgebraicStageTargetQuotient (X := X) N
  let : TopologicalSpace Q := ⊥
  let : DiscreteTopology Q := ⟨rfl⟩
  let : IsTopologicalGroup Q := inferInstance
  let e : Q ≃* H := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  let q : FreeGroup X →* Q := QuotientGroup.mk' N
  have he_apply (g : FreeGroup X) : e (q g) = ψ g := by
    change QuotientGroup.quotientKerEquivOfSurjective ψ hψ
        (QuotientGroup.mk' ψ.ker g) = ψ g
    rfl
  let eSymm : H →ₜ* Q :=
    { toMonoidHom := e.symm.toMonoidHom
      continuous_toFun := continuous_of_discreteTopology }
  have hcompSymm : eSymm.toMonoidHom.comp ψ = q := by
    apply MonoidHom.ext
    intro g
    apply e.injective
    change e (e.symm (ψ g)) = e (q g)
    simpa using (he_apply g).symm
  have hQtarget :
      ProCGroups.FiniteGroupClass.pGroup p Q :=
    ProCGroups.FiniteGroupClass.IsomClosed.of_mulEquiv
      (ProCGroups.FiniteGroupClass.pGroup_formation p).isomClosed
      e.symm hCtarget
  have hvecQ :
      zcFreeGroupFoxDerivativeVector
          (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{u})
          q w = 0 := by
    have htarget :=
      zcFreeGroupFoxDerivativeVector_mapTarget
        (C := (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{u}))
        (ProCGroups.FiniteGroupClass.pGroup_hereditary p) ψ eSymm w
    rw [hcompSymm] at htarget
    rw [htarget, hw]
    rfl
  have hq :
      FoxCalculus.relativeFreeGroupFoxDerivative (H := Q) X q w = 0 :=
    relFreeFoxDeriv_eq_zero_of_zcFreeFoxDerivVec_eq_zero_pGroup
      (X := X) N p hQtarget w hvecQ
  have hcomp : e.toMonoidHom.comp q = ψ := by
    apply MonoidHom.ext
    intro g
    exact he_apply g
  have hnat :=
    FoxCalculus.relativeFreeGroupFoxDerivative_mapDomain
      (H := Q) (K := H) q e.toMonoidHom w
  rw [hcomp] at hnat
  rw [hnat, hq]
  rfl

/--
Over the finite \(p\)-group coefficient class, a zero completed universal differential on an
arbitrary finite discrete \(p\)-group target map already forces the ordinary integral relative
Fox derivative to vanish.
-/
theorem relFreeFoxDeriv_eq_zero_of_zcUnivDiff_eq_zero_pGroup_of_surj
    (p : ℕ) [Fact (Nat.Prime p)]
    [DiscreteTopology H]
    (hCtarget : ProCGroups.FiniteGroupClass.pGroup p H)
    (ψ : FreeGroup X →* H) (hψ : Function.Surjective ψ)
    (w : FreeGroup X)
    (hw :
      zcUniversalDifferential
        (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{u})
        ψ w = 0) :
    FoxCalculus.relativeFreeGroupFoxDerivative (H := H) X ψ w = 0 :=
  relFreeFoxDeriv_eq_zero_of_zcFreeFoxDerivVec_eq_zero_pGroup_of_surj
    (X := X) p hCtarget ψ hψ w
    (zcFreeGroupFoxDerivativeVector_eq_zero_of_zcUniversalDifferential_eq_zero
      (C := (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{u}))
      ψ hw)

end FiniteTarget

end

end FoxDifferential
