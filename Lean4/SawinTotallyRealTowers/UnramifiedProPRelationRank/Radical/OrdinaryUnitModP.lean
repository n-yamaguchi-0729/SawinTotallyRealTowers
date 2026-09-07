import ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.SUnitPowerQuotient
import GaloisCohomology.Kummer.Concrete.SUnitPreparation.PrimePowerKernelCoordinates

set_option autoImplicit false
/-!
# Ordinary units modulo prime powers

This file computes the cardinality and `ZMod p`-dimension of the ordinary
number-field unit group modulo `p`-th powers.  The torsion correction is one
exactly when the field contains a primitive `p`-th root of unity.  The module
structure is exposed explicitly and is not installed as a global instance.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open NumberField IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K]

/-- The empty finite set gives the ordinary global unit group. -/
noncomputable def emptySUnitEquivNumberFieldUnits :
    SUnitGroup (K := K) (∅ : Finset (HeightOneSpectrum (𝓞 K))) ≃*
      (𝓞 K)ˣ :=
  (MulEquiv.subgroupCongr
    (congrArg
      (fun S : Set (HeightOneSpectrum (𝓞 K)) ↦ S.unit K)
      (show ((↑(∅ : Finset (HeightOneSpectrum (𝓞 K))) :
        Set (HeightOneSpectrum (𝓞 K)))) = ∅ by
          ext v
          simp))).trans
    (SUnitGroup.emptyEquivNumberFieldUnits (K := K))

/-- Ordinary global units modulo `n`-th powers. -/
abbrev OrdinaryUnitNthPowerQuotient (n : ℕ) :=
  (𝓞 K)ˣ ⧸
    (powMonoidHom n : (𝓞 K)ˣ →* (𝓞 K)ˣ).range

omit [NumberField K] in
/-- Every class modulo `p`-th powers has exponent dividing `p`. -/
theorem ordinaryUnitNthPowerQuotient_pow_eq_one
    (p : ℕ) (x : OrdinaryUnitNthPowerQuotient K p) :
    x ^ p = 1 := by
  refine QuotientGroup.induction_on x fun u ↦ ?_
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  simp

omit [NumberField K] in
/-- The canonical `ZMod p`-module structure on the additive presentation
of ordinary units modulo `p`-th powers. -/
@[reducible]
noncomputable def ordinaryUnitModPModule (p : ℕ) :
    Module (ZMod p) (Additive (OrdinaryUnitNthPowerQuotient K p)) :=
  KummerTheory.additiveZModModuleOfPowEqOne p
    (ordinaryUnitNthPowerQuotient_pow_eq_one K p)

/-- The empty-set `S`-unit power quotient is the ordinary-unit power quotient. -/
noncomputable def emptySUnitNthPowerQuotientEquiv
    (n : ℕ) :
    SUnitGroup (K := K) (∅ : Finset (HeightOneSpectrum (𝓞 K))) ⧸
        (powMonoidHom n :
          SUnitGroup (K := K) (∅ : Finset (HeightOneSpectrum (𝓞 K))) →*
            SUnitGroup (K := K) (∅ : Finset (HeightOneSpectrum (𝓞 K)))).range ≃*
      OrdinaryUnitNthPowerQuotient K n :=
  LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv
    (SUnitGroup (K := K) (∅ : Finset (HeightOneSpectrum (𝓞 K))))
    ((𝓞 K)ˣ) n
    (emptySUnitEquivNumberFieldUnits K)

/-- The quotient of ordinary units by positive powers is finite. -/
theorem finite_ordinaryUnitNthPowerQuotient (n : ℕ+) :
    Finite (OrdinaryUnitNthPowerQuotient K (n : ℕ)) := by
  let _ : Finite
      (SUnitGroup (K := K) (∅ : Finset (HeightOneSpectrum (𝓞 K))) ⧸
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) (∅ : Finset (HeightOneSpectrum (𝓞 K))) →*
            SUnitGroup (K := K) (∅ : Finset (HeightOneSpectrum (𝓞 K)))).range) :=
    KummerTheory.finite_sUnit_nthPowerQuotient
      (∅ : Finset (HeightOneSpectrum (𝓞 K))) n
  exact Finite.of_equiv
    (SUnitGroup (K := K) (∅ : Finset (HeightOneSpectrum (𝓞 K))) ⧸
      (powMonoidHom (n : ℕ) :
        SUnitGroup (K := K) (∅ : Finset (HeightOneSpectrum (𝓞 K))) →*
          SUnitGroup (K := K) (∅ : Finset (HeightOneSpectrum (𝓞 K)))).range)
    (emptySUnitNthPowerQuotientEquiv K (n : ℕ)).toEquiv

/-- Without a primitive `p`-th root, the roots-of-unity contribution to
the ordinary-unit quotient is trivial. -/
theorem card_numberFieldTorsion_pthPowerQuotient_of_no_primitiveRoot
    (p : ℕ) (hp : p.Prime)
    (hμ : ¬ ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Nat.card
        (NumberField.Units.torsion K ⧸
          (powMonoidHom p : NumberField.Units.torsion K →*
            NumberField.Units.torsion K).range) = 1 := by
  let T := NumberField.Units.torsion K
  have hnotdiv : ¬ p ∣ Nat.card T := by
    intro hdiv
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hdiv
    rw [← IsPrimitiveRoot.iff_orderOf,
      ← IsPrimitiveRoot.coe_submonoidClass_iff,
      ← IsPrimitiveRoot.coe_units_iff] at hζ
    have hζK : IsPrimitiveRoot ((ζ : (𝓞 K)ˣ) : K) p :=
      hζ.map_of_injective
        (FaithfulSMul.algebraMap_injective (𝓞 K) K)
    exact hμ ⟨((ζ : (𝓞 K)ˣ) : K), hζK⟩
  rw [LocalFieldTheory.card_nthPowerQuotient_eq_nthPowerKernel,
    IsCyclic.card_powMonoidHom_ker]
  exact (hp.coprime_iff_not_dvd.mpr hnotdiv).symm

/-- If `K` has no primitive `p`-th root, only the free Dirichlet-unit
coordinates contribute to the ordinary-unit quotient. -/
theorem card_ordinaryUnitNthPowerQuotient_of_no_primitiveRoot
    (p : ℕ) (hp : p.Prime)
    (hμ : ¬ ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Nat.card (OrdinaryUnitNthPowerQuotient K p) =
      p ^ (NumberField.InfinitePlace.nrRealPlaces K +
        NumberField.InfinitePlace.nrComplexPlaces K - 1) := by
  let S : Finset (HeightOneSpectrum (𝓞 K)) := ∅
  let F := Fin (SUnitGroup.logRank (K := K) S) →₀ ℤ
  let n : ℕ+ := (p.toPNat hp.pos)
  let : NeZero p := ⟨hp.ne_zero⟩
  let _ : Finite
      (F ⧸ LocalFieldTheory.nsmulAddSubgroup F p) := by
    change Finite
      ((Fin (SUnitGroup.logRank (K := K) S) →₀ ℤ) ⧸
        LocalFieldTheory.nsmulAddSubgroup
          (Fin (SUnitGroup.logRank (K := K) S) →₀ ℤ) (n : ℕ))
    exact KummerTheory.finite_finsupp_nsmulQuotient
      (SUnitGroup.logRank (K := K) S) n
  have hfree :
      Nat.card
          (Multiplicative F ⧸
            (powMonoidHom p : Multiplicative F →* Multiplicative F).range) =
        p ^ SUnitGroup.logRank (K := K) S := by
    rw [LocalFieldTheory.card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient]
    exact KummerTheory.card_finsupp_nsmulQuotient
      (SUnitGroup.logRank (K := K) S) n
  have hlog :
      SUnitGroup.logRank (K := K) S =
        NumberField.InfinitePlace.nrRealPlaces K +
          NumberField.InfinitePlace.nrComplexPlaces K - 1 := by
    unfold SUnitGroup.logRank S
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      Finset.card_empty, add_zero]
  calc
    Nat.card (OrdinaryUnitNthPowerQuotient K p) =
        Nat.card
          (SUnitGroup (K := K) S ⧸
            (powMonoidHom p : SUnitGroup (K := K) S →*
              SUnitGroup (K := K) S).range) := by
      exact Nat.card_congr
        (emptySUnitNthPowerQuotientEquiv K p).symm.toEquiv
    _ = Nat.card
          ((NumberField.Units.torsion K × Multiplicative F) ⧸
            (powMonoidHom p :
              NumberField.Units.torsion K × Multiplicative F →*
                NumberField.Units.torsion K × Multiplicative F).range) := by
      exact Nat.card_congr
        (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv
          (SUnitGroup (K := K) S)
          (NumberField.Units.torsion K × Multiplicative F) p
          (SUnitGroup.decomposition (K := K) S)).toEquiv
    _ = Nat.card
          ((NumberField.Units.torsion K ⧸
              (powMonoidHom p : NumberField.Units.torsion K →*
                NumberField.Units.torsion K).range) ×
            (Multiplicative F ⧸
              (powMonoidHom p : Multiplicative F →* Multiplicative F).range)) := by
      exact Nat.card_congr
        (LocalFieldTheory.nthPowerProductQuotientEquiv
          (NumberField.Units.torsion K) (Multiplicative F) p).toEquiv
    _ = 1 * p ^ SUnitGroup.logRank (K := K) S := by
      rw [Nat.card_prod,
        card_numberFieldTorsion_pthPowerQuotient_of_no_primitiveRoot K p hp hμ,
        hfree]
    _ = p ^ (NumberField.InfinitePlace.nrRealPlaces K +
          NumberField.InfinitePlace.nrComplexPlaces K - 1) := by
      rw [one_mul, hlog]

/-- If `K` contains a primitive `p`-th root, the ordinary-unit quotient
has one torsion coordinate in addition to the free unit rank. -/
theorem card_ordinaryUnitNthPowerQuotient_of_primitiveRoot
    (p : ℕ) (hp : p.Prime)
    (hμ : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Nat.card (OrdinaryUnitNthPowerQuotient K p) =
      p ^ (NumberField.InfinitePlace.nrRealPlaces K +
        NumberField.InfinitePlace.nrComplexPlaces K) := by
  let n : ℕ+ := (p.toPNat hp.pos)
  have hμ' : (primitiveRoots p K).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hμ
    exact ⟨ζ, (mem_primitiveRoots hp.pos).2 hζ⟩
  calc
    Nat.card (OrdinaryUnitNthPowerQuotient K p) =
        Nat.card
          (SUnitGroup (K := K) (∅ : Finset (HeightOneSpectrum (𝓞 K))) ⧸
            (powMonoidHom p :
              SUnitGroup (K := K) (∅ : Finset (HeightOneSpectrum (𝓞 K))) →*
                SUnitGroup (K := K)
                  (∅ : Finset (HeightOneSpectrum (𝓞 K)))).range) := by
      exact Nat.card_congr
        (emptySUnitNthPowerQuotientEquiv K p).symm.toEquiv
    _ = p ^ KummerTheory.totalPlaceCard
          (K := K) (∅ : Finset (HeightOneSpectrum (𝓞 K))) := by
      exact KummerTheory.card_sUnit_nthPowerQuotient
        (∅ : Finset (HeightOneSpectrum (𝓞 K))) n hμ'
    _ = p ^ (NumberField.InfinitePlace.nrRealPlaces K +
          NumberField.InfinitePlace.nrComplexPlaces K) := by
      rw [KummerTheory.totalPlaceCard, Finset.card_empty, add_zero,
        NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]

/-- The ordinary-unit quotient has Dirichlet rank, plus exactly one
torsion coordinate when `K` contains a primitive `p`-th root. -/
theorem card_ordinaryUnitNthPowerQuotient
    (p : ℕ) (hp : p.Prime) :
    Nat.card (OrdinaryUnitNthPowerQuotient K p) =
      p ^ (NumberField.InfinitePlace.nrRealPlaces K +
        NumberField.InfinitePlace.nrComplexPlaces K - 1 +
          (if (primitiveRoots p K).Nonempty then 1 else 0)) := by
  by_cases hroots : (primitiveRoots p K).Nonempty
  · have hμ : ∃ ζ : K, IsPrimitiveRoot ζ p := by
      obtain ⟨ζ, hζ⟩ := hroots
      exact ⟨ζ, (mem_primitiveRoots hp.pos).mp hζ⟩
    rw [card_ordinaryUnitNthPowerQuotient_of_primitiveRoot K p hp hμ]
    simp only [if_pos hroots]
    congr 1
    have hplaces :
        0 < NumberField.InfinitePlace.nrRealPlaces K +
          NumberField.InfinitePlace.nrComplexPlaces K := by
      rw [← NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
      exact Fintype.card_pos
    omega
  · have hμ : ¬ ∃ ζ : K, IsPrimitiveRoot ζ p := by
      rintro ⟨ζ, hζ⟩
      exact hroots ⟨ζ, (mem_primitiveRoots hp.pos).mpr hζ⟩
    rw [card_ordinaryUnitNthPowerQuotient_of_no_primitiveRoot K p hp hμ]
    simp [hroots]

/-- The `ZMod p`-dimension computed using the explicit ordinary-unit module. -/
noncomputable def ordinaryUnitModPFinrank (p : ℕ) : ℕ :=
  letI : Module (ZMod p)
      (Additive (OrdinaryUnitNthPowerQuotient K p)) :=
    ordinaryUnitModPModule K p
  Module.finrank (ZMod p)
    (Additive (OrdinaryUnitNthPowerQuotient K p))

/-- The `ZMod p`-dimension of ordinary units modulo `p`-th powers. -/
theorem finrank_ordinaryUnitModP
    (p : ℕ) (hp : p.Prime) :
    ordinaryUnitModPFinrank K p =
      NumberField.InfinitePlace.nrRealPlaces K +
        NumberField.InfinitePlace.nrComplexPlaces K - 1 +
          (if (primitiveRoots p K).Nonempty then 1 else 0) := by
  unfold ordinaryUnitModPFinrank
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Module (ZMod p)
      (Additive (OrdinaryUnitNthPowerQuotient K p)) :=
    ordinaryUnitModPModule K p
  let _ : Finite (Additive (OrdinaryUnitNthPowerQuotient K p)) :=
    finite_ordinaryUnitNthPowerQuotient K (p.toPNat hp.pos)
  let _ : Module.Finite (ZMod p)
      (Additive (OrdinaryUnitNthPowerQuotient K p)) :=
    Module.Finite.of_finite
  apply Nat.pow_right_injective hp.two_le
  calc
    p ^ Module.finrank (ZMod p)
        (Additive (OrdinaryUnitNthPowerQuotient K p)) =
        Nat.card (Additive (OrdinaryUnitNthPowerQuotient K p)) := by
      rw [Module.natCard_eq_pow_finrank
        (K := ZMod p)
        (V := Additive (OrdinaryUnitNthPowerQuotient K p)), Nat.card_zmod]
    _ = Nat.card (OrdinaryUnitNthPowerQuotient K p) := rfl
    _ = p ^ (NumberField.InfinitePlace.nrRealPlaces K +
          NumberField.InfinitePlace.nrComplexPlaces K - 1 +
            (if (primitiveRoots p K).Nonempty then 1 else 0)) :=
      card_ordinaryUnitNthPowerQuotient K p hp

end ClassFieldTower.Martinet.Shafarevich
