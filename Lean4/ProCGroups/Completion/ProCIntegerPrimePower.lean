import ProCGroups.Completion.ProCInteger

set_option autoImplicit false

/-!
# Pro C Groups / Completion / Prime-Power pro-C Integer

This module specializes the pro-C integer construction to prime-power moduli and proves the
pro-p density, generation, and procyclicity results.
-/

namespace ProCGroups.Completion

noncomputable section

universe u

namespace ProCIntegerIndex

/-- The \(p^k\)-modulus coefficient index for the pro-\(p\) integer limit. -/
def pGroupPower (p k : ℕ) [Fact (Nat.Prime p)] :
    ProCIntegerIndex (FiniteGroupClass.pGroup p : FiniteGroupClass.{u}) where
  modulus := p ^ k
  positive := by
    exact Nat.pow_pos (show 0 < p from (Fact.out : Nat.Prime p).pos)
  cyclic_mem := by
    refine (FiniteGroupClass.memAcrossUniverses_ulift_iff
      (FiniteGroupClass.pGroup p : FiniteGroupClass.{u})
      (Multiplicative (ZMod (p ^ k)))).1 ?_
    apply FiniteGroupClass.memAcrossUniverses_of_mem
    let : NeZero (p ^ k) := ⟨Nat.ne_of_gt (Nat.pow_pos
      (show 0 < p from (Fact.out : Nat.Prime p).pos))⟩
    constructor
    · exact Finite.of_equiv (ZMod (p ^ k))
        (Multiplicative.ofAdd.trans Equiv.ulift.symm)
    · intro g
      refine ⟨k, ?_⟩
      cases g with
      | up g' =>
        apply ULift.ext
        change g' ^ p ^ k = 1
        cases g' with
        | ofAdd z =>
          change Multiplicative.ofAdd ((p ^ k) • z) = Multiplicative.ofAdd 0
          simp only [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero]

/-- The prime-power coefficient index has modulus \(p ^ n\). -/
@[simp]
theorem modulus_pGroupPower (p k : ℕ) [Fact (Nat.Prime p)] :
    (pGroupPower p k :
      ProCIntegerIndex (FiniteGroupClass.pGroup p : FiniteGroupClass.{u})).modulus = p ^ k :=
  rfl

/-- Any coefficient index for the finite \(p\)-group class is dominated by a prime-power modulus. -/
theorem modulus_dvd_pow_of_mem_pGroup (p : ℕ) [Fact (Nat.Prime p)]
    (i : ProCIntegerIndex (FiniteGroupClass.pGroup p : FiniteGroupClass.{u})) :
    ∃ k, i.modulus ∣ p ^ k := by
  rcases i.cyclic_mem with ⟨H, hH, ⟨e⟩⟩
  rcases hH with ⟨_hfin, hp⟩
  rcases hp (e.symm (Multiplicative.ofAdd (1 : ZMod i.modulus))) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hk' : ((p ^ k : ℕ) : ZMod i.modulus) = 0 := by
    have hpow :
        (Multiplicative.ofAdd (1 : ZMod i.modulus)) ^ (p ^ k) = 1 := by
      simpa using congrArg e hk
    have h := congrArg Multiplicative.toAdd hpow
    simpa using h
  exact (ZMod.natCast_eq_zero_iff (p ^ k) i.modulus).mp hk'

/-- The finite \(p\)-group coefficient indices for pro-\(C\) integers are directed. -/
theorem directed_pGroup (p : ℕ) [Fact (Nat.Prime p)] :
    Directed (· ≤ ·)
      (id : ProCIntegerIndex (FiniteGroupClass.pGroup p : FiniteGroupClass.{u}) →
        ProCIntegerIndex (FiniteGroupClass.pGroup p : FiniteGroupClass.{u})) := by
  intro i j
  rcases modulus_dvd_pow_of_mem_pGroup (p := p) i with ⟨ki, hki⟩
  rcases modulus_dvd_pow_of_mem_pGroup (p := p) j with ⟨kj, hkj⟩
  refine ⟨pGroupPower p (ki + kj), ?_, ?_⟩
  · exact dvd_trans hki (pow_dvd_pow p (Nat.le_add_right ki kj))
  · exact dvd_trans hkj (pow_dvd_pow p (Nat.le_add_left kj ki))

end ProCIntegerIndex

/-- The distinguished element \(1\) projects to \(1\) on every prime-power coordinate. -/
@[simp]
theorem proCIntegerProj_pGroupPower_one (p k : ℕ) [Fact (Nat.Prime p)] :
    proCIntegerProj
        (C := (FiniteGroupClass.pGroup p : FiniteGroupClass.{u}))
        (ProCIntegerIndex.pGroupPower p k)
        (proCIntegerOne
          (C := (FiniteGroupClass.pGroup p : FiniteGroupClass.{u}))).toAdd =
      (1 : ZMod (p ^ k)) :=
  rfl

/-- The ordinary integers are dense in the pro-\(p\) integer coefficient ring. -/
theorem denseRange_intToProCInteger_pGroup (p : ℕ) [Fact (Nat.Prime p)] :
    DenseRange (intToProCInteger
      (C := (FiniteGroupClass.pGroup p : FiniteGroupClass.{u}))) := by
  let C : FiniteGroupClass.{u} := FiniteGroupClass.pGroup p
  let S := proCIntegerSystem C
  let φ : ∀ i : ProCIntegerIndex C, ℤ → S.X i := fun i n => (n : ZMod i.modulus)
  have hφ : S.CompatibleMaps φ := by
    intro i j hij
    funext n
    exact map_intCast (ZMod.castHom hij (ZMod i.modulus)) n
  have hsurj : ∀ i, Function.Surjective (φ i) := by
    intro i
    exact ZMod.intCast_surjective
  let : Nonempty (ProCIntegerIndex C) := ⟨ProCIntegerIndex.pGroupPower p 0⟩
  have hdense : DenseRange (S.inverseLimitLift φ hφ) :=
    ProCGroups.InverseSystems.InverseSystem.denseRange_lift
      (S := S) φ hφ hsurj (ProCIntegerIndex.directed_pGroup (p := p))
  have hfun :
      (intToProCInteger (C := C) : ℤ → ProCIntegerLimitCarrier C) =
        S.inverseLimitLift φ hφ := by
    funext n
    apply Subtype.ext
    rfl
  rw [hfun]
  exact hdense

/-- The multiplicative infinite-cyclic map is dense in the pro-\(p\) integers. -/
theorem denseRange_multiplicativeIntToProCInteger_pGroup (p : ℕ) [Fact (Nat.Prime p)] :
    DenseRange
      (multiplicativeIntToProCInteger
        (C := (FiniteGroupClass.pGroup p : FiniteGroupClass.{u}))) := by
  let C : FiniteGroupClass.{u} := FiniteGroupClass.pGroup p
  have hdense :
      Dense (Set.range fun n : ℤ =>
        (n : ProCIntegerLimitCarrier C)) :=
    denseRange_intToProCInteger_pGroup (p := p)
  have hdense' :
      Dense (Set.range fun n : ℤ =>
        Multiplicative.ofAdd (n : ProCIntegerLimitCarrier C)) := by
    change Dense (Set.range fun n : ℤ => (n : ProCIntegerLimitCarrier C))
    exact hdense
  change Dense (Set.range fun z : Multiplicative ℤ =>
    Multiplicative.ofAdd (z.toAdd : ProCIntegerLimitCarrier C))
  have hrange :
      Set.range (fun z : Multiplicative ℤ =>
        Multiplicative.ofAdd (z.toAdd : ProCIntegerLimitCarrier C)) =
        Set.range (fun n : ℤ =>
          Multiplicative.ofAdd (n : ProCIntegerLimitCarrier C)) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.toAdd, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨Multiplicative.ofAdd n, rfl⟩
  rw [hrange]
  exact hdense'

/-- The distinguished element 1 topologically generates the pro-\(p\) integers. -/
theorem topologicallyGenerates_singleton_proCIntegerOne_pGroup
    (p : ℕ) [Fact (Nat.Prime p)] :
    ProCGroups.Generation.TopologicallyGenerates
      (G := Multiplicative
        (ProCIntegerLimitCarrier (FiniteGroupClass.pGroup p : FiniteGroupClass.{0})))
      ({proCIntegerOne
        (C := (FiniteGroupClass.pGroup p : FiniteGroupClass.{0}))} : Set _) := by
  let C : FiniteGroupClass.{0} := FiniteGroupClass.pGroup p
  simpa [C, proCIntegerOne] using
    (ProCGroups.Generation.topologicallyGenerates_singleton_of_denseRange_mint
      (f := multiplicativeIntToProCInteger (C := C))
      (denseRange_multiplicativeIntToProCInteger_pGroup (p := p)))

/-- The pro-\(p\) integers have an open-normal basis of finite \(p\)-group quotients. -/
theorem hasPGroupOpenNormalBasis_multiplicative_proCInteger_pGroup (p : ℕ) [Fact (Nat.Prime p)] :
    ProCGroups.ProC.HasPGroupOpenNormalBasis p
      (Multiplicative
        (ProCIntegerLimitCarrier (FiniteGroupClass.pGroup p : FiniteGroupClass.{0}))) := by
  let C : FiniteGroupClass.{0} := FiniteGroupClass.pGroup p
  let : Nonempty (ProCIntegerIndex C) := ⟨ProCIntegerIndex.pGroupPower p 0⟩
  simpa [ProCGroups.ProC.HasPGroupOpenNormalBasis, C] using
    hasOpenNormalBasisInClass_multiplicative_proCInteger
      (C := C)
      (FiniteGroupClass.pGroup_formation p).isomClosed
      (FiniteGroupClass.pGroup_formation p).quotientClosed
      (ProCIntegerIndex.directed_pGroup (p := p))

/-- The pro-\(p\) integers have a cyclic open-normal quotient basis. -/
theorem hasCyclicOpenNormalBasis_multiplicative_proCInteger_pGroup (p : ℕ) [Fact (Nat.Prime p)] :
    ProCGroups.ProC.HasCyclicOpenNormalBasis
      (Multiplicative
        (ProCIntegerLimitCarrier (FiniteGroupClass.pGroup p : FiniteGroupClass.{0}))) := by
  let : T2Space
      (Multiplicative
        (ProCIntegerLimitCarrier (FiniteGroupClass.pGroup p : FiniteGroupClass.{0}))) := by
    change T2Space
      (ProCIntegerLimitCarrier (FiniteGroupClass.pGroup p : FiniteGroupClass.{0}))
    exact instT2SpaceProCInteger
      (C := (FiniteGroupClass.pGroup p : FiniteGroupClass.{0}))
  let : TotallyDisconnectedSpace
      (Multiplicative
        (ProCIntegerLimitCarrier (FiniteGroupClass.pGroup p : FiniteGroupClass.{0}))) := by
    change TotallyDisconnectedSpace
      (ProCIntegerLimitCarrier (FiniteGroupClass.pGroup p : FiniteGroupClass.{0}))
    infer_instance
  exact ProCGroups.ProC.hasCyclicOpenNormalBasis_of_topologicallyGenerates_singleton
    (G := Multiplicative
      (ProCIntegerLimitCarrier (FiniteGroupClass.pGroup p : FiniteGroupClass.{0})))
    (topologicallyGenerates_singleton_proCIntegerOne_pGroup (p := p))

end

end ProCGroups.Completion
