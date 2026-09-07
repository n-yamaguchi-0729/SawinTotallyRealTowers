import GaloisCohomology.ProP.FiniteCyclicCarryCocycle

set_option autoImplicit false
/-!
# The cyclic carry identity for the bar--periodic comparison

For a specified generator `g`, let `S(x)` be the prefix
`1 + g + ... + g^(r(x)-1)`, where `r(x)` is the standard representative of
the generator coordinate of `x`.  The degree-two bar differential applied to
these prefixes is the carry times the full cyclic norm vector.  In particular,
the comparison has positive sign.
-/

namespace ClassFieldTower.Cohomology

noncomputable section

open Representation

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- The prefix `1 + g + ... + g^(m-1)` in the left regular representation. -/
noncomputable def finiteCyclicPrefixNat (g : G) (m : ℕ) : MonoidAlgebra R G :=
  ∑ i ∈ Finset.range m, MonoidAlgebra.single (g ^ i) 1

/-- The prefix whose length is the standard generator coordinate of `x`. -/
noncomputable def finiteCyclicGeneratorPrefix
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x : G) : MonoidAlgebra R G :=
  finiteCyclicPrefixNat (R := R) g
    (finiteCyclicGeneratorCoordinate g hg x).val

@[simp]
theorem finiteCyclicGeneratorPrefix_one
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    finiteCyclicGeneratorPrefix (R := R) g hg 1 = 0 := by
  simp [finiteCyclicGeneratorPrefix, finiteCyclicPrefixNat]

omit [Fintype G] in
@[simp]
theorem finiteCyclicPrefixNat_zero (g : G) :
    finiteCyclicPrefixNat (R := R) g 0 = 0 := by
  simp [finiteCyclicPrefixNat]

omit [Fintype G] in
theorem finiteCyclicPrefixNat_succ (g : G) (m : ℕ) :
    finiteCyclicPrefixNat (R := R) g (m + 1) =
      finiteCyclicPrefixNat (R := R) g m + MonoidAlgebra.single (g ^ m) 1 := by
  simp [finiteCyclicPrefixNat, Finset.sum_range_succ]

omit [Fintype G] in
theorem leftRegular_single_one (x y : G) :
    (Rep.leftRegular R G).ρ x (MonoidAlgebra.single y 1) =
      MonoidAlgebra.single (x * y) 1 := by
  simp

omit [Fintype G] in
theorem leftRegular_pow_single_one (g : G) (i j : ℕ) :
    (Rep.leftRegular R G).ρ (g ^ i) (MonoidAlgebra.single (g ^ j) 1) =
      MonoidAlgebra.single (g ^ (i + j)) 1 := by
  rw [leftRegular_single_one, pow_add]

omit [Fintype G] in
/-- Concatenating two prefixes translates the second one by the first power. -/
theorem finiteCyclicPrefixNat_add (g : G) (i j : ℕ) :
    finiteCyclicPrefixNat (R := R) g i +
        (Rep.leftRegular R G).ρ (g ^ i) (finiteCyclicPrefixNat (R := R) g j) =
      finiteCyclicPrefixNat (R := R) g (i + j) := by
  induction j with
  | zero => simp [finiteCyclicPrefixNat]
  | succ j ih =>
      rw [finiteCyclicPrefixNat_succ, map_add]
      calc
        _ =
            (finiteCyclicPrefixNat (R := R) g i +
              (Rep.leftRegular R G).ρ (g ^ i)
                (finiteCyclicPrefixNat (R := R) g j)) +
              (Rep.leftRegular R G).ρ (g ^ i)
                (MonoidAlgebra.single (g ^ j) 1) := by abel
        _ = finiteCyclicPrefixNat (R := R) g (i + j) +
              MonoidAlgebra.single (g ^ (i + j)) 1 := by
            rw [ih, leftRegular_pow_single_one]
        _ = finiteCyclicPrefixNat (R := R) g (i + j + 1) := by
            rw [finiteCyclicPrefixNat_succ]
        _ = finiteCyclicPrefixNat (R := R) g (i + (j + 1)) := by
            rw [Nat.add_assoc]

theorem generator_pow_natCard (g : G) : g ^ Nat.card G = 1 := by
  rw [Nat.card_eq_fintype_card]
  exact pow_card_eq_one

theorem finiteCyclicPrefixNat_card_add (g : G) (m : ℕ) :
    finiteCyclicPrefixNat (R := R) g (Nat.card G + m) =
      finiteCyclicPrefixNat (R := R) g (Nat.card G) +
        finiteCyclicPrefixNat (R := R) g m := by
  have h := finiteCyclicPrefixNat_add (R := R) g (Nat.card G) m
  rw [generator_pow_natCard, map_one] at h
  exact h.symm

omit [Fintype G] in
theorem leftRegular_prefix_sub (g : G) (m : ℕ) :
    (Rep.leftRegular R G).ρ g
          (finiteCyclicPrefixNat (R := R) g m) -
        finiteCyclicPrefixNat (R := R) g m =
      MonoidAlgebra.single (g ^ m) 1 - MonoidAlgebra.single 1 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [finiteCyclicPrefixNat_succ, map_add]
      have hsingle :
          (Rep.leftRegular R G).ρ g (MonoidAlgebra.single (g ^ m) 1) =
            MonoidAlgebra.single (g ^ (m + 1)) 1 := by
        ext z
        simp [pow_succ']
      calc
        _ =
            ((Rep.leftRegular R G).ρ g
                (finiteCyclicPrefixNat (R := R) g m) -
              finiteCyclicPrefixNat (R := R) g m) +
            ((Rep.leftRegular R G).ρ g (MonoidAlgebra.single (g ^ m) 1) -
              MonoidAlgebra.single (g ^ m) 1) := by abel
        _ =
            (MonoidAlgebra.single (g ^ m) 1 - MonoidAlgebra.single 1 1) +
            (MonoidAlgebra.single (g ^ (m + 1)) 1 -
              MonoidAlgebra.single (g ^ m) 1) := by rw [ih, hsingle]
        _ = _ := by abel

/-- The degree-one prefix has differential `[x] - [1]`. -/
theorem finiteCyclicGeneratorPrefix_sub
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x : G) :
    (Rep.leftRegular R G).ρ g
          (finiteCyclicGeneratorPrefix (R := R) g hg x) -
        finiteCyclicGeneratorPrefix (R := R) g hg x =
      MonoidAlgebra.single x 1 - MonoidAlgebra.single 1 1 := by
  rw [finiteCyclicGeneratorPrefix, leftRegular_prefix_sub,
    finiteCyclicGenerator_zpow_coordinate]

/-- The degree-two bar--periodic comparison identity.  A carry contributes
the full cyclic norm vector with positive sign. -/
theorem finiteCyclicGeneratorPrefix_carry
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x y : G) :
    (Rep.leftRegular R G).ρ x
          (finiteCyclicGeneratorPrefix (R := R) g hg y) -
        finiteCyclicGeneratorPrefix (R := R) g hg (x * y) +
          finiteCyclicGeneratorPrefix (R := R) g hg x =
      finiteCyclicCarry g hg x y •
        finiteCyclicPrefixNat (R := R) g (Nat.card G) := by
  let _ : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  let cx := finiteCyclicGeneratorCoordinate g hg x
  let cy := finiteCyclicGeneratorCoordinate g hg y
  have hx : g ^ cx.val = x := finiteCyclicGenerator_zpow_coordinate g hg x
  have hxy : finiteCyclicGeneratorCoordinate g hg (x * y) = cx + cy :=
    finiteCyclicGeneratorCoordinate_mul g hg x y
  have hsum := finiteCyclicPrefixNat_add (R := R) g cx.val cy.val
  have haction :
      (Rep.leftRegular R G).ρ x (finiteCyclicPrefixNat (R := R) g cy.val) =
        (Rep.leftRegular R G).ρ (g ^ cx.val)
          (finiteCyclicPrefixNat (R := R) g cy.val) := by rw [hx]
  simp only [finiteCyclicGeneratorPrefix]
  rw [hxy, haction]
  change
    (Rep.leftRegular R G).ρ (g ^ cx.val)
          (finiteCyclicPrefixNat (R := R) g cy.val) -
        finiteCyclicPrefixNat (R := R) g (cx + cy).val +
          finiteCyclicPrefixNat (R := R) g cx.val =
      zmodCarry cx cy • finiteCyclicPrefixNat (R := R) g (Nat.card G)
  by_cases hcarry : Nat.card G ≤ cx.val + cy.val
  · rw [ZMod.val_add_of_le hcarry]
    have hadd : Nat.card G + (cx.val + cy.val - Nat.card G) =
        cx.val + cy.val := by omega
    have hperiod := finiteCyclicPrefixNat_card_add (R := R) g
      (cx.val + cy.val - Nat.card G)
    rw [hadd] at hperiod
    have hc : zmodCarry cx cy = 1 :=
      (zmodCarry_eq_one_iff cx cy).2 hcarry
    rw [hc, one_nsmul]
    calc
      _ =
          (finiteCyclicPrefixNat (R := R) g cx.val +
              (Rep.leftRegular R G).ρ (g ^ cx.val)
                (finiteCyclicPrefixNat (R := R) g cy.val)) -
            finiteCyclicPrefixNat (R := R) g
              (cx.val + cy.val - Nat.card G) := by abel
      _ = finiteCyclicPrefixNat (R := R) g (cx.val + cy.val) -
            finiteCyclicPrefixNat (R := R) g
              (cx.val + cy.val - Nat.card G) := by rw [hsum]
      _ = _ := by rw [hperiod]; abel
  · have hlt : cx.val + cy.val < Nat.card G := Nat.lt_of_not_ge hcarry
    rw [ZMod.val_add_of_lt hlt]
    have hc : zmodCarry cx cy = 0 :=
      (zmodCarry_eq_zero_iff cx cy).2 hlt
    rw [hc, zero_nsmul]
    calc
      _ =
          (finiteCyclicPrefixNat (R := R) g cx.val +
              (Rep.leftRegular R G).ρ (g ^ cx.val)
                (finiteCyclicPrefixNat (R := R) g cy.val)) -
            finiteCyclicPrefixNat (R := R) g (cx.val + cy.val) := by abel
      _ = 0 := by rw [hsum]; abel

end

end ClassFieldTower.Cohomology
